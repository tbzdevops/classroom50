#!/usr/bin/env python3
"""classroom50 runner.

Fetched from the teacher's GitHub Pages site by the autograde-runner
reusable workflow on every submission. Responsibilities:

  1. Read env (CLASSROOM, ASSIGNMENT, SUBMISSION_TAG, etc.)
  2. Compute helper values (USERNAME, COMMIT_URL, RELEASE_URL,
     REVIEW_URL)
  3. Download the per-assignment bundle from Pages, extract it
  4. Resolve the entrypoint:
       per-assignment <classroom>/autograders/<slug>/autograder.py
       (extracted from the bundle), or
       classroom default at <classroom>/autograder.py
       (fetched from the per-classroom Pages URL).
       When neither exists, synthesize a vacuous-pass result so the
       workflow still publishes the submit-tag release with a clear
       "no autograder configured" status.
  5. Exec the entrypoint with the helper env vars and cwd at the
     student's repo checkout
  6. Read the autograder's outputs: ./result.json,
     ./release-body.md, and status= / summary= entries in
     $GITHUB_OUTPUT. Synthesize anything the autograder didn't
     write so the workflow's downstream steps always have something
     v1-shaped to publish.

Teachers don't normally edit this file. Per-assignment grading
logic lives in autograder.py — see the Autograders wiki page.

The runner exits 0 for every grading outcome — including failures
(bundle fetch error, malformed result.json, autograder rc != 0, etc.),
which are reported via a synthetic error result + status=error so the
workflow's release/commit-status steps still fire and the gradebook
still ingests the submission. The one exception is missing required
env vars (PAGES_BASE_URL, CLASSROOM, ASSIGNMENT, SUBMISSION_TAG):
without those identity fields the runner can't synthesize a v1-shaped
result.json, so it fails fast with exit 1 — this only happens when
the script is invoked outside the autograde-runner workflow.

Environment (set by the autograde-runner workflow):
  PAGES_BASE_URL    org-level Pages URL of the classroom50 config repo
  CLASSROOM         classroom short-name
  ASSIGNMENT        assignment slug
  SUBMISSION_TAG    submit/<UTC-timestamp>-<short-sha>
  GITHUB_REPOSITORY <owner>/<repo>
  GITHUB_SHA        commit SHA
  GITHUB_SERVER_URL https://github.com (or GHES base)
  GITHUB_ACTOR      fallback username when the repo name doesn't
                    follow the <classroom>-<assignment>-<username>
                    convention
  GITHUB_OUTPUT     workflow-step output sink

Additional env vars passed through to the entrypoint:
  USERNAME          student GitHub username (derived from repo name)
  COMMIT_URL        link to the graded commit on github.com
  RELEASE_URL       link to the submission release on github.com
  REVIEW_URL        full diff (baseline...graded commit); equals
                    COMMIT_URL when history is unavailable or there
                    is nothing to compare (baseline == commit)
"""

from __future__ import annotations

import datetime
import io
import json
import os
import pathlib
import re
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from typing import Any

# Schema sentinel — keep in lockstep with collect_scores.py::validate_result
# (cli/gh-teacher/skeleton/dotgithub/scripts/collect_scores.py).
RESULT_SCHEMA_V1 = "classroom50/result/v1"

# Filenames the autograder must (or may) write into the workspace.
# release-body.md is optional; the runner synthesizes one when
# missing. result.json is required.
RESULT_FILENAME = "result.json"
RELEASE_BODY_FILENAME = "release-body.md"

# Conventional name for both the per-assignment override and the
# classroom default entrypoint.
ENTRYPOINT_FILENAME = "autograder.py"

# Per-assignment declarative tests: a bundled tests.json (materialized
# from assignments.json by publish-pages.yaml) is graded by the built-in
# interpreter below. Schema lives in tests.go; contract in the wiki.
TESTS_FILENAME = "tests.json"
TESTS_SCHEMA_V1 = "classroom50/tests/v1"

# Default per-test timeout (seconds) when `timeout` is omitted/0. Setup
# and run commands are each bounded by it independently.
DEFAULT_TEST_TIMEOUT = 10

# Captured stdout/stderr is truncated to this many characters in the
# release body so a runaway program can't bloat the published release.
MAX_CAPTURED_CHARS = 2000

# Test types and io comparison modes -- mirror the allow-lists in tests.go.
TEST_TYPE_IO = "io"
TEST_TYPE_RUN = "run"
TEST_TYPE_PYTHON = "python"
TEST_TYPES = (TEST_TYPE_IO, TEST_TYPE_RUN, TEST_TYPE_PYTHON)

COMPARISON_INCLUDED = "included"
COMPARISON_EXACT = "exact"
COMPARISON_REGEX = "regex"
COMPARISONS = (COMPARISON_INCLUDED, COMPARISON_EXACT, COMPARISON_REGEX)

# Bounded retry for Pages fetches. 1s → 2s → 4s on transient network
# errors / HTTP 5xx. 404 is NOT retried — for the bundle URL it
# means "no per-assignment override"; for the classroom-default URL
# it means the classroom hasn't run `gh teacher autograder
# set-default` (the runner falls back to a vacuous-pass result).
FETCH_ATTEMPTS = 3

# Hard cap on the bundle / classroom-default fetches. Bundles fitting
# in 10 MB cover all realistic test suites; a single autograder.py
# is small but the same ceiling avoids a hostile asset.
MAX_FETCH_BYTES = 10 * 1024 * 1024

# Subject of the plumbing commit `gh student accept` adds after
# templating (.classroom50.yaml + autograde shim). Mirrors
# cli/gh-student/metadata.go (dropClassroomFiles) -- keep in lockstep.
# baseline_sha skips past it so those files don't diff as student work.
ACCEPT_COMMIT_SUBJECT = (
    "Initialize .classroom50.yaml and autograde workflow (gh student accept)"
)


def runtime_root() -> pathlib.Path:
    """Pick a writable scratch dir for bundle extraction + entrypoint
    fetches. Prefers `$RUNNER_TEMP` (Actions cross-platform temp dir,
    cleaned between jobs) and falls back to `tempfile.mkdtemp()` for
    local development. Hard-coded `/tmp/` would break on Windows
    runners (which `runtime.go`'s allow-list still admits)."""
    base = os.environ.get("RUNNER_TEMP", "").strip()
    if base:
        return pathlib.Path(base) / "classroom50-runtime"
    return pathlib.Path(tempfile.mkdtemp(prefix="classroom50-runtime-"))


# ---------------------------------------------------------------------------
# Pure helpers (no I/O — fully unit-testable)
# ---------------------------------------------------------------------------


def username_from_repo(repository: str, classroom: str, assignment: str, actor: str) -> str:
    """Derive the student username from `<owner>/<classroom>-<assignment>-<username>`.

    Mirrors the `assignmentRepoName` formula in cli/gh-student/accept.go
    (lowercased throughout). Falls back to GITHUB_ACTOR when the repo
    name doesn't follow the convention (e.g. hand-created repos for
    testing).
    """
    if "/" in repository:
        _, repo = repository.split("/", 1)
    else:
        repo = repository
    prefix = f"{classroom.lower()}-{assignment.lower()}-"
    if repo.lower().startswith(prefix):
        return repo[len(prefix):]
    return actor


def commit_url(server_url: str, repository: str, sha: str) -> str:
    return f"{server_url}/{repository}/commit/{sha}"


def release_url(server_url: str, repository: str, submission_tag: str) -> str:
    return f"{server_url}/{repository}/releases/tag/{urllib.parse.quote(submission_tag, safe='')}"


def compare_url(server_url: str, repository: str, base_sha: str, head_sha: str) -> str:
    return f"{server_url}/{repository}/compare/{base_sha}...{head_sha}"


def review_url(server_url: str, repository: str, base_sha: str | None, head_sha: str) -> str:
    """Full diff from the student's baseline to the graded commit;
    commit view when there's no usable baseline (history unavailable,
    or baseline == head)."""
    if base_sha and head_sha and base_sha != head_sha:
        return compare_url(server_url, repository, base_sha, head_sha)
    return commit_url(server_url, repository, head_sha)


def bundle_url(pages_base_url: str, classroom: str, assignment: str) -> str:
    """The Pages URL for an assignment's bundle (autograder.py +
    sibling fixtures, packaged by publish-pages.yaml)."""
    safe_classroom = urllib.parse.quote(classroom, safe="")
    safe_slug = urllib.parse.quote(assignment, safe="")
    return f"{pages_base_url}/{safe_classroom}/autograders/{safe_slug}.tar.gz"


def classroom_default_autograder_url(pages_base_url: str, classroom: str) -> str:
    """The Pages URL for a classroom's default autograder.py.

    Published verbatim by publish-pages.yaml from the repo path
    `<classroom>/autograder.py` to the Pages path
    `<classroom>/autograder.py`. Optional — classrooms that haven't
    run `gh teacher autograder set-default` won't have one, and the
    runner falls back to a vacuous-pass result for those.
    """
    safe_classroom = urllib.parse.quote(classroom, safe="")
    return f"{pages_base_url}/{safe_classroom}/{ENTRYPOINT_FILENAME}"


def make_result(
    *,
    classroom: str,
    assignment: str,
    username: str,
    submission: str,
    commit_link: str,
    release_link: str,
    when: datetime.datetime,
    score: int,
    max_score: int,
    tests: list[dict[str, Any]],
    review_link: str | None = None,
) -> dict[str, Any]:
    """Build a v1-shaped result.json payload. Single source of the field
    layout shared by the error/vacuous paths (empty_result) and the
    declarative grader (which passes real score/tests). review falls
    back to the commit view when review_link is None."""
    return {
        "schema": RESULT_SCHEMA_V1,
        "classroom": classroom,
        "assignment": assignment,
        "usernames": [username],
        "submission": submission,
        "commit": commit_link,
        "release": release_link,
        "review": review_link or commit_link,
        "datetime": when.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "score": score,
        "max-score": max_score,
        "tests": tests,
    }


def empty_result(
    *,
    classroom: str,
    assignment: str,
    username: str,
    submission: str,
    commit_link: str,
    release_link: str,
    when: datetime.datetime,
    review_link: str | None = None,
) -> dict[str, Any]:
    """A v1-valid result.json payload with no tests (score 0/0).

    The runner uses this for every error path — collect-scores
    ingests it as "submitted, error"; the workflow log carries the
    actual failure reason.
    """
    return make_result(
        classroom=classroom,
        assignment=assignment,
        username=username,
        submission=submission,
        commit_link=commit_link,
        release_link=release_link,
        when=when,
        score=0,
        max_score=0,
        tests=[],
        review_link=review_link,
    )


def derive_status_and_summary(result: dict[str, Any]) -> tuple[str, str]:
    """Map a result.json payload to a commit-status state + summary line.

    `success` when all tests pass (or when there are zero tests —
    vacuous pass, "submitted, no autograder configured"). `failure`
    when any test failed. The error path is set explicitly by the
    runner, never derived here.
    """
    tests = result.get("tests") or []
    score = int(result.get("score") or 0)
    max_score = int(result.get("max-score") or 0)
    assignment = result.get("assignment") or "assignment"

    if not tests:
        return (
            "success",
            f"classroom50 autograde: submitted — no autograder configured for {assignment}",
        )

    passed = sum(1 for t in tests if t.get("passed"))
    total = len(tests)
    if passed == total:
        return "success", f"classroom50 autograde: {score}/{max_score} (all tests passed)"
    return "failure", f"classroom50 autograde: {score}/{max_score} ({passed}/{total} tests passed)"


def render_release_body(result: dict[str, Any], summary: str) -> str:
    """Render the Markdown body for the submit-tag release.

    Shows the score line, then a per-test table (or just the summary
    when `tests` is empty). `|` characters in test names are escaped
    so they don't break the Markdown table.
    """
    score = int(result.get("score") or 0)
    max_score = int(result.get("max-score") or 0)
    tests = result.get("tests") or []

    lines = [f"### classroom50 autograde: {score}/{max_score}", ""]
    if tests:
        lines.append("| Test | Result | Score |")
        lines.append("|---|---|---|")
        for t in tests:
            ok = "PASS" if t.get("passed") else "FAIL"
            test_name = (t.get("test-name") or "").replace("|", "\\|")
            lines.append(
                f"| {test_name} | {ok} | "
                f"{int(t.get('score') or 0)} / {int(t.get('max-score') or 0)} |"
            )
        lines.append("")
        lines.append(f"Status: {summary}")
    else:
        lines.append(f"_{summary}_")
    return "\n".join(lines) + "\n"


def validate_result(data: Any, *, classroom: str, assignment: str) -> str | None:
    """Return None if `data` is v1-shaped for the given identity, else
    a human-readable error string.

    Mirrors collect_scores.py::validate_result so a payload that
    passes here also passes the gradebook ingest. Without the parity,
    a malformed result.json (wrong type on `usernames`, non-int score,
    test entry that isn't a dict, etc.) would silently pass the
    runner, get published as a release, and only get rejected on the
    next collect-scores run — the student appears as not-yet-submitted
    in the gradebook with no signal in the workflow log.
    """
    if not isinstance(data, dict):
        return f"{RESULT_FILENAME} is not a JSON object"
    if data.get("schema") != RESULT_SCHEMA_V1:
        return f"{RESULT_FILENAME} schema is {data.get('schema')!r}, want {RESULT_SCHEMA_V1!r}"
    if data.get("classroom") != classroom:
        return (
            f"{RESULT_FILENAME} classroom is {data.get('classroom')!r}, "
            f"want {classroom!r}"
        )
    if data.get("assignment") != assignment:
        return (
            f"{RESULT_FILENAME} assignment is {data.get('assignment')!r}, "
            f"want {assignment!r}"
        )

    usernames = data.get("usernames")
    if not isinstance(usernames, list) or len(usernames) != 1:
        return f"{RESULT_FILENAME} 'usernames' must be a one-element list"
    if not isinstance(usernames[0], str) or not usernames[0]:
        return f"{RESULT_FILENAME} 'usernames[0]' must be a non-empty string"

    submission = data.get("submission")
    if not isinstance(submission, str) or not submission.startswith("submit/"):
        return f"{RESULT_FILENAME} 'submission' must be a 'submit/*' string"

    for field in ("commit", "release", "review", "datetime"):
        v = data.get(field)
        if not isinstance(v, str) or not v:
            return f"{RESULT_FILENAME} {field!r} must be a non-empty string"

    score = data.get("score")
    max_score = data.get("max-score")
    # Reject bool (which is an int subclass in Python) — bool slipping
    # past `isinstance(int)` would let `True`/`False` pass for scores.
    if isinstance(score, bool) or not isinstance(score, int) or score < 0:
        return f"{RESULT_FILENAME} 'score' must be a non-negative integer"
    if isinstance(max_score, bool) or not isinstance(max_score, int) or max_score < 0:
        return f"{RESULT_FILENAME} 'max-score' must be a non-negative integer"
    if score > max_score:
        return f"{RESULT_FILENAME} score ({score}) > max-score ({max_score})"

    tests = data.get("tests")
    if not isinstance(tests, list):
        return f"{RESULT_FILENAME} 'tests' is not a list"
    for i, t in enumerate(tests):
        if not isinstance(t, dict):
            return f"{RESULT_FILENAME} 'tests[{i}]' is not an object"
        name = t.get("test-name")
        if not isinstance(name, str) or not name:
            return f"{RESULT_FILENAME} 'tests[{i}].test-name' must be a non-empty string"
        if not isinstance(t.get("passed"), bool):
            return f"{RESULT_FILENAME} 'tests[{i}].passed' must be a boolean"
        ts, tm = t.get("score"), t.get("max-score")
        if isinstance(ts, bool) or not isinstance(ts, int) or ts < 0:
            return f"{RESULT_FILENAME} 'tests[{i}].score' must be a non-negative integer"
        if isinstance(tm, bool) or not isinstance(tm, int) or tm < 0:
            return f"{RESULT_FILENAME} 'tests[{i}].max-score' must be a non-negative integer"
        if ts > tm:
            return f"{RESULT_FILENAME} 'tests[{i}].score' ({ts}) > 'tests[{i}].max-score' ({tm})"
    return None


# ---------------------------------------------------------------------------
# I/O helpers
# ---------------------------------------------------------------------------


def baseline_sha(workspace: pathlib.Path) -> str | None:
    """SHA of the commit the student started from: the `gh student
    accept` plumbing commit (matched via ACCEPT_COMMIT_SUBJECT) when
    present, else the root commit. Returns None when history is
    unavailable -- no git binary, no .git (actions/checkout's tarball
    fallback in git-less containers), or an un-deepenable shallow
    clone -- and the caller falls back to the commit view."""

    def git(*args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", "-C", str(workspace), *args],
            capture_output=True, text=True, timeout=120, check=False,
        )

    try:
        shallow = git("rev-parse", "--is-shallow-repository")
        if shallow.returncode != 0:
            return None
        if shallow.stdout.strip() == "true":
            # Depth-1 checkout (workflows predating fetch-depth: 0):
            # deepen, or the graft boundary would pose as the root.
            # checkout's persisted credentials authenticate the fetch.
            if git("fetch", "--quiet", "--unshallow", "origin").returncode != 0:
                return None
        log = git("log", "--reverse", "--first-parent", "--format=%H %s", "HEAD")
        if log.returncode != 0:
            return None
        lines = [line for line in log.stdout.splitlines() if line.strip()]
        if not lines:
            return None
        # Earliest match wins: a commit crafted later in history with
        # the same subject can't move the baseline forward. (Today the
        # accept commit is always position 1 -- the template-generate
        # API squashes the starter into a single initial commit -- but
        # scanning keeps this correct if the creation flow changes.)
        for line in lines:
            sha, _, subject = line.partition(" ")
            if subject == ACCEPT_COMMIT_SUBJECT:
                return sha
        return lines[0].partition(" ")[0]
    except (OSError, subprocess.SubprocessError):
        return None


def fetch_url(url: str) -> bytes | None:
    """GET `url`. 200 → bytes (≤ MAX_FETCH_BYTES), 404 → None,
    transient 5xx/network failures retried with exponential backoff."""
    last_exc: Exception | None = None
    for attempt in range(FETCH_ATTEMPTS):
        req = urllib.request.Request(url, headers={"User-Agent": "classroom50-autograde"})
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                body = resp.read(MAX_FETCH_BYTES + 1)
                if len(body) > MAX_FETCH_BYTES:
                    raise ValueError(f"response from {url} exceeds {MAX_FETCH_BYTES}-byte ceiling")
                return body
        except urllib.error.HTTPError as exc:
            if exc.code == 404:
                return None
            last_exc = exc
            if exc.code < 500 or attempt == FETCH_ATTEMPTS - 1:
                raise
        except urllib.error.URLError as exc:
            last_exc = exc
            if attempt == FETCH_ATTEMPTS - 1:
                raise
        time.sleep(2 ** attempt)
    raise RuntimeError(f"fetch_url exhausted retries: {last_exc!r}")


def extract_tarball(data: bytes, dest: pathlib.Path) -> None:
    """Safe-extract a gzipped tar archive into `dest`.

    Prefers `tarfile.extractall(filter='data')` (Python 3.12+) to
    block path-traversal and other unsafe member types. Falls back
    to a manual prefix check when running on older interpreters,
    since `runtime.python` lets teachers pin 3.10 / 3.11 and the
    container path inherits whatever python the image ships.
    """
    dest.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tar:
        if sys.version_info >= (3, 12):
            tar.extractall(path=dest, filter="data")
            return
        _safe_extractall_legacy(tar, dest)


def _safe_extractall_legacy(tar: tarfile.TarFile, dest: pathlib.Path) -> None:
    """Path-traversal-safe extraction for Python < 3.12.

    Mirrors the rejections that `filter='data'` enforces upstream:
    no absolute paths, no `..` segments escaping `dest`, no symlinks
    or hard links, no device / FIFO / character-special members.
    Sane bundles produced by `git archive` / `tar -czf` extract
    identically on both code paths.
    """
    dest_real = pathlib.Path(os.path.realpath(dest))
    for m in tar.getmembers():
        if m.issym() or m.islnk() or m.isdev() or m.ischr() or m.isfifo():
            raise ValueError(f"unsupported tar member type: {m.name!r}")
        if not m.name or os.path.isabs(m.name) or m.name.startswith(".."):
            raise ValueError(f"unsafe tar path: {m.name!r}")
        target = pathlib.Path(os.path.realpath(dest_real / m.name))
        if target != dest_real and dest_real not in target.parents:
            raise ValueError(f"unsafe tar path: {m.name!r}")
    tar.extractall(path=dest)


def output_has_status(github_output_path: str | None) -> bool:
    """Did the autograder write a status= line to $GITHUB_OUTPUT?"""
    if not github_output_path:
        return False
    p = pathlib.Path(github_output_path)
    if not p.is_file():
        return False
    return any(line.startswith("status=") for line in p.read_text().splitlines())


def append_outputs(github_output_path: str | None, status: str, summary: str) -> None:
    if not github_output_path:
        return
    safe_summary = summary.replace("\n", " ").replace("\r", " ")
    with open(github_output_path, "a") as fh:
        fh.write(f"status={status}\n")
        fh.write(f"summary={safe_summary}\n")


def now_utc() -> datetime.datetime:
    return datetime.datetime.now(datetime.timezone.utc)


# ---------------------------------------------------------------------------
# Error finalizer
# ---------------------------------------------------------------------------


class Finalizer:
    """Synthesizes a v1 result.json + release body + GITHUB_OUTPUT
    entries on any error path. The runner calls `.error(message)`
    instead of returning a non-zero exit code so the workflow's
    downstream publish step still gets something to upload."""

    def __init__(
        self,
        *,
        workspace: pathlib.Path,
        github_output: str | None,
        classroom: str,
        assignment: str,
        username: str,
        submission: str,
        commit_link: str,
        release_link: str,
        review_link: str | None = None,
    ):
        self.workspace = workspace
        self.github_output = github_output
        self.classroom = classroom
        self.assignment = assignment
        self.username = username
        self.submission = submission
        self.commit_link = commit_link
        self.release_link = release_link
        self.review_link = review_link

    def error(self, message: str) -> int:
        print(f"::error::{message}", file=sys.stderr)
        result = empty_result(
            classroom=self.classroom,
            assignment=self.assignment,
            username=self.username,
            submission=self.submission,
            commit_link=self.commit_link,
            release_link=self.release_link,
            when=now_utc(),
            review_link=self.review_link,
        )
        summary = f"classroom50 autograde: {message}"
        (self.workspace / RESULT_FILENAME).write_text(json.dumps(result, indent=2) + "\n")
        (self.workspace / RELEASE_BODY_FILENAME).write_text(render_release_body(result, summary))
        # Always overwrite — the autograder may have written a stale
        # status= before exiting non-zero or producing bad output.
        append_outputs(self.github_output, "error", summary)
        return 0

    def no_autograder(self) -> int:
        """Vacuous-pass synthesis for classrooms that haven't configured
        an autograder yet. Distinct from `error()` because "no autograder
        configured" is a valid mid-setup state, not a failure: the
        student still submitted, the workflow still tagged, and the
        gradebook should record the submission as 0/0 success rather
        than as an error. Reuses derive_status_and_summary's empty-tests
        branch so the framing stays in lockstep."""
        result = empty_result(
            classroom=self.classroom,
            assignment=self.assignment,
            username=self.username,
            submission=self.submission,
            commit_link=self.commit_link,
            release_link=self.release_link,
            when=now_utc(),
            review_link=self.review_link,
        )
        status, summary = derive_status_and_summary(result)
        print(f"runner: {summary}")
        (self.workspace / RESULT_FILENAME).write_text(json.dumps(result, indent=2) + "\n")
        (self.workspace / RELEASE_BODY_FILENAME).write_text(render_release_body(result, summary))
        append_outputs(self.github_output, status, summary)
        return 0


# ---------------------------------------------------------------------------
# Declarative test grading (GitHub Classroom-style io / run / python tests)
# ---------------------------------------------------------------------------
#
# Grades a bundled tests.json with a built-in interpreter. The specs are
# DATA, never code: `run`/`setup` strings are teacher-authored shell,
# executed in the student checkout at the same privilege as an
# autograder.py. They arrive via the Pages bundle — never interpolated
# into workflow YAML — and students can't edit assignments.json. The
# interpreter re-validates spec shape because the file is hand-editable.
# Write-time validator: tests.go; trust-boundary rationale: the
# Autograders wiki page.


class TestsConfigError(Exception):
    """Raised when tests.json is missing, malformed, or fails the
    runtime re-validation. Surfaced to the workflow via Finalizer.error."""


class TestFixtureError(Exception):
    """Raised when a test references an input-file/expected-file that is
    missing or escapes the bundle directory."""


def compare_output(actual: str, expected: str, mode: str) -> bool:
    """Compare program stdout against expected output, GitHub Classroom-style.

    - included: expected appears anywhere in actual (raw substring).
    - exact: actual equals expected, ignoring leading/trailing whitespace
      (the trailing-newline footgun otherwise fails almost every test).
    - regex: Python `re.search` with re.MULTILINE (so ^/$ anchor at line
      boundaries in multi-line output). Raises re.error on a malformed
      pattern so the caller can report it as a failing test.
    """
    if mode == COMPARISON_INCLUDED:
        return expected in actual
    if mode == COMPARISON_EXACT:
        return actual.strip() == expected.strip()
    if mode == COMPARISON_REGEX:
        return re.search(expected, actual, re.MULTILINE) is not None
    raise ValueError(f"unknown comparison mode {mode!r}")


def _clip(text: str | None) -> str:
    """Truncate captured output for the release body."""
    text = text or ""
    if len(text) > MAX_CAPTURED_CHARS:
        return text[:MAX_CAPTURED_CHARS] + "\n... (truncated)"
    return text


def _fence(text: str) -> str:
    """A backtick fence longer than any backtick run inside `text`, so
    student output containing ``` can't break out of the code block and
    inject Markdown into the release body."""
    longest = max((len(m.group(0)) for m in re.finditer(r"`+", text)), default=0)
    return "`" * max(3, longest + 1)


def _make_outcome(name: str, points: int, passed: bool, detail: str,
                  *, score: int | None = None) -> dict[str, Any]:
    """One test's outcome. Carries the v1 result-row fields plus a `detail`
    string used only for the release body (stripped before result.json)."""
    if score is None:
        score = points if passed else 0
    return {
        "test-name": name,
        "passed": passed,
        "score": score,
        "max-score": points,
        "detail": detail,
    }


def _read_fixture(rel: str, fixtures_dir: pathlib.Path) -> str:
    """Read a bundled fixture file, rejecting any path that escapes the
    bundle directory (a hand-edited expected-file: '../../etc/passwd'
    must not be readable)."""
    base = pathlib.Path(os.path.realpath(fixtures_dir))
    target = pathlib.Path(os.path.realpath(base / rel))
    if target != base and base not in target.parents:
        raise TestFixtureError(f"fixture path escapes the bundle: {rel!r}")
    if not target.is_file():
        raise TestFixtureError(f"fixture file not found: {rel!r}")
    return target.read_text(encoding="utf-8", errors="replace")


def _resolve_stdin(spec: dict[str, Any], fixtures_dir: pathlib.Path) -> str:
    """stdin for an io test: the bundled input-file if set, else the inline
    `input`, else empty (always a string so the child never inherits the
    parent's stdin and hangs waiting on a terminal)."""
    if spec.get("input-file"):
        return _read_fixture(spec["input-file"], fixtures_dir)
    return spec.get("input") or ""


def _resolve_expected(spec: dict[str, Any], fixtures_dir: pathlib.Path) -> str:
    if spec.get("expected-file"):
        return _read_fixture(spec["expected-file"], fixtures_dir)
    return spec.get("expected") or ""


def _run_command(command: str, cwd: pathlib.Path, timeout: int,
                 stdin: str = "") -> subprocess.CompletedProcess[str]:
    """Run a shell command in the student checkout with captured text
    output and an empty-by-default stdin."""
    return subprocess.run(
        command,
        shell=True,
        cwd=str(cwd),
        input=stdin,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=timeout,
    )


def _run_setup(setup: str, cwd: pathlib.Path, timeout: int) -> str | None:
    """Run a test's setup command. Returns an error string if it times out
    or exits non-zero, else None."""
    try:
        sp = _run_command(setup, cwd, timeout)
    except subprocess.TimeoutExpired:
        return f"setup timed out after {timeout}s"
    except OSError as exc:
        return f"setup failed to start: {exc}"
    if sp.returncode != 0:
        return f"setup exited {sp.returncode}\n{_clip(sp.stderr or sp.stdout)}"
    return None


def _grade_python(spec: dict[str, Any], cwd: pathlib.Path, timeout: int,
                  points: int, name: str) -> dict[str, Any]:
    """Run a pytest command and split `points` across discovered cases
    (GitHub Classroom's points/num_tests model), reading pytest-json-report
    output. Falls back to exit-code scoring (all-or-nothing) when no JSON
    report is produced -- e.g. the plugin isn't installed."""
    report_dir = pathlib.Path(tempfile.mkdtemp(prefix="classroom50-pytest-"))
    report = report_dir / "report.json"
    # Skip appending when the teacher's command already configures the
    # plugin (duplicate flags would make pytest exit with a usage error).
    if "--json-report" in spec["run"]:
        cmd = spec["run"]
    else:
        cmd = f"{spec['run']} --json-report --json-report-file={shlex.quote(str(report))}"
    try:
        rp = _run_command(cmd, cwd, timeout)
    except subprocess.TimeoutExpired:
        shutil.rmtree(report_dir, ignore_errors=True)
        return _make_outcome(name, points, False, f"timed out after {timeout}s")
    except OSError as exc:
        shutil.rmtree(report_dir, ignore_errors=True)
        return _make_outcome(name, points, False, f"failed to start: {exc}")

    passed_n = total_n = None
    if report.is_file():
        try:
            summary = (json.loads(report.read_text(encoding="utf-8", errors="replace"))
                       .get("summary") or {})
            total_n = int(summary.get("total") or 0)
            passed_n = int(summary.get("passed") or 0)
        except (json.JSONDecodeError, ValueError, TypeError, AttributeError):
            passed_n = total_n = None
    shutil.rmtree(report_dir, ignore_errors=True)

    if total_n:
        score = max(0, min(points, round(points * passed_n / total_n)))
        passed = passed_n == total_n
        # Full credit is reserved for an all-pass run: with small point
        # values, round() could otherwise award points/points to a test
        # whose row reads FAIL (e.g. points=1, 2/3 cases passed).
        if not passed:
            score = min(score, max(0, points - 1))
        detail = f"pytest: {passed_n}/{total_n} cases passed"
        if not passed:
            detail += "\n" + _clip(rp.stdout or rp.stderr)
        return _make_outcome(name, points, passed, detail, score=score)

    # Fallback: no parseable report -> all-or-nothing on the exit code.
    passed = rp.returncode == 0
    detail = (f"pytest exit {rp.returncode} "
              f"(no JSON report; install pytest-json-report for per-case scoring)")
    if not passed:
        detail += "\n" + _clip(rp.stdout or rp.stderr)
    return _make_outcome(name, points, passed, detail)


def execute_test(spec: dict[str, Any], *, cwd: pathlib.Path,
                 fixtures_dir: pathlib.Path) -> dict[str, Any]:
    """Run one declarative test and return its outcome dict. Never raises
    for a test failure -- a timeout, crash, bad fixture, or bad regex all
    map to a failing outcome with a diagnostic `detail`."""
    name = spec["name"]
    points = int(spec.get("points") or 0)
    ttype = spec["type"]
    timeout = int(spec.get("timeout") or 0) or DEFAULT_TEST_TIMEOUT

    setup = spec.get("setup") or ""
    if setup:
        err = _run_setup(setup, cwd, timeout)
        if err:
            return _make_outcome(name, points, False, err)

    if ttype == TEST_TYPE_PYTHON:
        return _grade_python(spec, cwd, timeout, points, name)

    try:
        stdin = _resolve_stdin(spec, fixtures_dir)
    except TestFixtureError as exc:
        return _make_outcome(name, points, False, str(exc))

    try:
        rp = _run_command(spec["run"], cwd, timeout, stdin=stdin)
    except subprocess.TimeoutExpired:
        return _make_outcome(name, points, False, f"timed out after {timeout}s")
    except OSError as exc:
        return _make_outcome(name, points, False, f"failed to start: {exc}")

    if ttype == TEST_TYPE_RUN:
        want = spec.get("exit-code")
        want = 0 if want is None else int(want)
        passed = rp.returncode == want
        detail = f"exit {rp.returncode} (wanted {want})"
        if not passed:
            detail += "\n" + _clip(rp.stderr or rp.stdout)
        return _make_outcome(name, points, passed, detail)

    # io test.
    try:
        expected = _resolve_expected(spec, fixtures_dir)
    except TestFixtureError as exc:
        return _make_outcome(name, points, False, str(exc))
    comparison = spec["comparison"]
    try:
        passed = compare_output(rp.stdout, expected, comparison)
    except re.error as exc:
        return _make_outcome(name, points, False, f"invalid regex in expected: {exc}")
    detail = f"exit {rp.returncode}; comparison={comparison}"
    if not passed:
        detail += (f"\n--- expected ({comparison}) ---\n{_clip(expected)}"
                   f"\n--- actual stdout ---\n{_clip(rp.stdout)}")
        if rp.stderr.strip():
            detail += f"\n--- stderr ---\n{_clip(rp.stderr)}"
    return _make_outcome(name, points, passed, detail)


def _validate_test_spec(t: Any) -> str | None:
    """Re-validate one spec at grade time — a lower bar than tests.go
    that keeps a hand-edited assignments.json from crashing the grader."""
    if not isinstance(t, dict):
        return "not an object"
    name = t.get("name")
    if not isinstance(name, str) or not name:
        return "name must be a non-empty string"
    if t.get("type") not in TEST_TYPES:
        return f"type {t.get('type')!r} must be one of {list(TEST_TYPES)}"
    if not isinstance(t.get("run"), str) or not t.get("run"):
        return "run must be a non-empty string"
    points = t.get("points", 0)
    if isinstance(points, bool) or not isinstance(points, int) or points < 0:
        return "points must be a non-negative integer"
    timeout = t.get("timeout", 0)
    if isinstance(timeout, bool) or not isinstance(timeout, int) or timeout < 0 or timeout > 600:
        return "timeout must be an integer between 0 and 600"
    # Type-check the optional string fields execute_test consumes, so a
    # malformed tests.json fails with a clear message instead of a
    # mid-run TypeError.
    for key in ("setup", "input", "input-file", "expected", "expected-file"):
        v = t.get(key)
        if v is not None and not isinstance(v, str):
            return f"{key} must be a string"
    if t.get("type") == TEST_TYPE_IO and t.get("comparison") not in COMPARISONS:
        return f"comparison must be one of {list(COMPARISONS)}"
    # exit-code feeds `int(...)` and an equality check in execute_test.
    exit_code = t.get("exit-code")
    if exit_code is not None and (isinstance(exit_code, bool) or not isinstance(exit_code, int)):
        return "exit-code must be an integer"
    return None


def load_tests(path: pathlib.Path) -> list[dict[str, Any]]:
    """Parse + re-validate a materialized tests.json. Raises TestsConfigError
    on any structural problem."""
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise TestsConfigError(f"{TESTS_FILENAME} is not a JSON object")
    if data.get("schema") != TESTS_SCHEMA_V1:
        raise TestsConfigError(
            f"{TESTS_FILENAME} schema is {data.get('schema')!r}, want {TESTS_SCHEMA_V1!r}")
    tests = data.get("tests")
    if not isinstance(tests, list) or not tests:
        raise TestsConfigError(f"{TESTS_FILENAME} 'tests' must be a non-empty list")
    seen = set()
    for i, t in enumerate(tests):
        err = _validate_test_spec(t)
        if err:
            raise TestsConfigError(f"{TESTS_FILENAME} tests[{i}]: {err}")
        # Names are row identities in result.json; duplicates would make
        # the gradebook ambiguous.
        if t["name"] in seen:
            raise TestsConfigError(f"{TESTS_FILENAME} tests[{i}]: duplicate test name {t['name']!r}")
        seen.add(t["name"])
    return tests


def render_declarative_body(result: dict[str, Any], outcomes: list[dict[str, Any]],
                            summary: str) -> str:
    """Release-body Markdown for a declaratively-graded submission: the
    score line, a per-test table, and a collapsible failure-detail section
    with captured output for any failing test."""
    lines = [f"### classroom50 autograde: {result['score']}/{result['max-score']}", ""]
    lines.append("| Test | Result | Score |")
    lines.append("|---|---|---|")
    for o in outcomes:
        ok = "PASS" if o["passed"] else "FAIL"
        name = o["test-name"].replace("|", "\\|")
        lines.append(f"| {name} | {ok} | {o['score']} / {o['max-score']} |")
    lines.append("")

    failed = [o for o in outcomes if not o["passed"]]
    if failed:
        lines.append("<details><summary>Failure details</summary>")
        lines.append("")
        for o in failed:
            detail = (o.get("detail") or "").rstrip()
            fence = _fence(detail)
            lines.append(f"**{o['test-name']}**")
            lines.append("")
            lines.append(fence)
            lines.append(detail)
            lines.append(fence)
            lines.append("")
        lines.append("</details>")
        lines.append("")

    lines.append(f"Status: {summary}")
    return "\n".join(lines) + "\n"


class DeclarativeGrader:
    """Runs a list of declarative test specs and builds the v1 result.json.
    Constructed with the same identity context the Finalizer carries."""

    def __init__(self, *, workspace: pathlib.Path, fixtures_dir: pathlib.Path,
                 classroom: str, assignment: str, username: str, submission: str,
                 commit_link: str, release_link: str,
                 review_link: str | None = None):
        self.workspace = workspace
        self.fixtures_dir = fixtures_dir
        self.classroom = classroom
        self.assignment = assignment
        self.username = username
        self.submission = submission
        self.commit_link = commit_link
        self.release_link = release_link
        self.review_link = review_link

    def grade(self, tests: list[dict[str, Any]]) -> tuple[dict[str, Any], list[dict[str, Any]]]:
        """Run every test. Returns (result.json dict, outcomes) where the
        outcomes carry per-test `detail` for the release body."""
        outcomes = [execute_test(t, cwd=self.workspace, fixtures_dir=self.fixtures_dir)
                    for t in tests]
        rows = [{k: o[k] for k in ("test-name", "passed", "score", "max-score")}
                for o in outcomes]
        result = make_result(
            classroom=self.classroom,
            assignment=self.assignment,
            username=self.username,
            submission=self.submission,
            commit_link=self.commit_link,
            release_link=self.release_link,
            when=now_utc(),
            score=sum(o["score"] for o in outcomes),
            max_score=sum(o["max-score"] for o in outcomes),
            tests=rows,
            review_link=self.review_link,
        )
        return result, outcomes


def run_declarative(tests_path: pathlib.Path, finalize: Finalizer,
                    fixtures_dir: pathlib.Path) -> int:
    """Grade a per-assignment tests.json: load + re-validate, run each test,
    then write result.json / release-body.md / GITHUB_OUTPUT. A malformed
    tests.json routes through Finalizer.error so the submission still
    publishes as 'submitted, error'. Always returns 0 -- a grading outcome
    (even all-fail) never fails the runner."""
    try:
        tests = load_tests(tests_path)
    except (json.JSONDecodeError, TestsConfigError, OSError) as exc:
        return finalize.error(f"{TESTS_FILENAME}: {exc}")

    grader = DeclarativeGrader(
        workspace=finalize.workspace,
        fixtures_dir=fixtures_dir,
        classroom=finalize.classroom,
        assignment=finalize.assignment,
        username=finalize.username,
        submission=finalize.submission,
        commit_link=finalize.commit_link,
        release_link=finalize.release_link,
        review_link=finalize.review_link,
    )
    # Backstop: execute_test/load_tests handle the expected failures; the
    # broad catch guarantees the "grading outcomes always exit 0"
    # invariant — an unexpected exception becomes a published error
    # result, never an uncaught crash.
    try:
        result, outcomes = grader.grade(tests)
    except Exception as exc:  # noqa: BLE001 - grading must never crash the runner
        return finalize.error(f"declarative grader crashed: {exc}")

    # Should always pass (the grader controls every field), but validating
    # keeps parity with collect_scores ingest and catches drift early.
    err = validate_result(result, classroom=finalize.classroom, assignment=finalize.assignment)
    if err is not None:
        return finalize.error(f"declarative grader produced invalid result: {err}")

    status, summary = derive_status_and_summary(result)
    print(f"runner: {summary}")
    (finalize.workspace / RESULT_FILENAME).write_text(json.dumps(result, indent=2) + "\n")
    (finalize.workspace / RELEASE_BODY_FILENAME).write_text(
        render_declarative_body(result, outcomes, summary))
    append_outputs(finalize.github_output, status, summary)
    return 0


# ---------------------------------------------------------------------------
# main()
# ---------------------------------------------------------------------------


def main() -> int:
    pages_base_url = os.environ.get("PAGES_BASE_URL", "").strip()
    classroom = os.environ.get("CLASSROOM", "").strip()
    assignment = os.environ.get("ASSIGNMENT", "").strip()
    submission = os.environ.get("SUBMISSION_TAG", "").strip()
    if not (pages_base_url and classroom and assignment and submission):
        print(
            "::error::runner requires PAGES_BASE_URL, CLASSROOM, "
            "ASSIGNMENT, and SUBMISSION_TAG — running outside the autograde-runner workflow?",
            file=sys.stderr,
        )
        return 1

    repository = os.environ.get("GITHUB_REPOSITORY", "")
    sha = os.environ.get("GITHUB_SHA", "")
    server_url = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
    actor = os.environ.get("GITHUB_ACTOR", "")
    github_output = os.environ.get("GITHUB_OUTPUT")
    workspace = pathlib.Path.cwd()

    username = username_from_repo(repository, classroom, assignment, actor)
    commit_link = commit_url(server_url, repository, sha)
    release_link = release_url(server_url, repository, submission)
    base_sha = baseline_sha(workspace)
    review_link = review_url(server_url, repository, base_sha, sha)
    if base_sha is None:
        print("runner: no baseline commit found; review link falls back to the commit view")

    print(
        f"runner: classroom={classroom!r} assignment={assignment!r} "
        f"submission={submission!r} username={username!r}"
    )
    print(f"runner: review link {review_link}")

    finalize = Finalizer(
        workspace=workspace,
        github_output=github_output,
        classroom=classroom,
        assignment=assignment,
        username=username,
        submission=submission,
        commit_link=commit_link,
        release_link=release_link,
        review_link=review_link,
    )

    # Reset the runtime root and clear stale outputs from any prior run.
    runtime_dir = runtime_root()
    if runtime_dir.exists():
        shutil.rmtree(runtime_dir)
    runtime_dir.mkdir(parents=True)
    for f in (workspace / RESULT_FILENAME, workspace / RELEASE_BODY_FILENAME):
        if f.exists():
            f.unlink()

    # 1) Download the per-assignment bundle (404 → no override, fall
    # through to the classroom default).
    burl = bundle_url(pages_base_url, classroom, assignment)
    print(f"runner: fetching bundle {burl}")
    try:
        bundle = fetch_url(burl)
    except (urllib.error.HTTPError, urllib.error.URLError, ValueError) as exc:
        return finalize.error(f"bundle fetch failed: {exc} — see workflow logs")

    if bundle is not None:
        print(f"runner: bundle size {len(bundle)} bytes")
        try:
            extract_tarball(bundle, runtime_dir)
        except (tarfile.TarError, OSError, ValueError) as exc:
            return finalize.error(f"bundle extraction failed: {exc} — see workflow logs")

    # 2) Resolve the entrypoint, most-specific first:
    #      per-assignment autograder.py
    #      > per-assignment tests.json (declarative, graded in-process)
    #      > classroom default autograder.py
    #      > vacuous pass.
    # A hand-written per-assignment autograder.py wins over declarative
    # tests for the same slug (it's the escape hatch). When nothing
    # exists, finalize.no_autograder() synthesizes a vacuous-pass result
    # — "no autograder configured" is a valid mid-setup state, not an
    # error, so the gradebook records the submission as 0/0 success.
    per_assignment = runtime_dir / assignment / ENTRYPOINT_FILENAME
    per_assignment_tests = runtime_dir / assignment / TESTS_FILENAME
    if per_assignment.is_file():
        entrypoint = per_assignment
        print(f"runner: using per-assignment entrypoint {entrypoint}")
    elif per_assignment_tests.is_file():
        print(f"runner: grading per-assignment declarative tests {per_assignment_tests}")
        return run_declarative(per_assignment_tests, finalize, runtime_dir / assignment)
    else:
        durl = classroom_default_autograder_url(pages_base_url, classroom)
        print(
            f"runner: no per-assignment {ENTRYPOINT_FILENAME}; "
            f"fetching classroom default from {durl}"
        )
        try:
            content = fetch_url(durl)
        except (urllib.error.HTTPError, urllib.error.URLError, ValueError) as exc:
            return finalize.error(f"classroom default {ENTRYPOINT_FILENAME} fetch failed: {exc}")
        if content is None:
            return finalize.no_autograder()
        entrypoint = runtime_dir / ENTRYPOINT_FILENAME
        entrypoint.write_bytes(content)
        print(f"runner: using classroom default entrypoint {entrypoint}")

    # 3) Exec with helper env vars and cwd at the student's checkout.
    env = dict(os.environ)
    env["USERNAME"] = username
    env["COMMIT_URL"] = commit_link
    env["RELEASE_URL"] = release_link
    env["REVIEW_URL"] = review_link
    try:
        proc = subprocess.run(
            [sys.executable, str(entrypoint)],
            cwd=str(workspace),
            env=env,
            check=False,
        )
    except OSError as exc:
        return finalize.error(f"failed to invoke {ENTRYPOINT_FILENAME}: {exc}")

    if proc.returncode != 0:
        return finalize.error(f"autograder exited {proc.returncode}")

    # 4) Validate result.json.
    result_path = workspace / RESULT_FILENAME
    if not result_path.is_file():
        return finalize.error(f"autograder did not produce {RESULT_FILENAME}")
    try:
        result = json.loads(result_path.read_text())
    except json.JSONDecodeError as exc:
        return finalize.error(f"{RESULT_FILENAME} is not valid JSON: {exc}")
    err = validate_result(result, classroom=classroom, assignment=assignment)
    if err is not None:
        return finalize.error(err)

    # 5) Synthesize release-body.md if the autograder didn't write one.
    body_path = workspace / RELEASE_BODY_FILENAME
    if not body_path.is_file():
        _, fallback = derive_status_and_summary(result)
        body_path.write_text(render_release_body(result, fallback))

    # 6) Synthesize status / summary if the autograder didn't write them.
    if not output_has_status(github_output):
        status, summary = derive_status_and_summary(result)
        append_outputs(github_output, status, summary)
        print(f"runner: derived status={status} summary={summary!r}")
    else:
        print("runner: autograder set status/summary; using as-is")

    return 0


if __name__ == "__main__":
    sys.exit(main())
