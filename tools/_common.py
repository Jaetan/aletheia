# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared helpers for the Aletheia developer tooling (the tools/ package).

Centralises the small boilerplate that several gate scripts would otherwise
duplicate -- stdout emission, content hashing, subprocess invocation, git
metadata, timestamps, artifact directories -- so each lives in exactly one
place.  Imported as ``from tools._common import ...``; the tools are invoked
as ``python -m tools.X`` (see ``tools/__init__.py``).

This module imports nothing outside the standard library, and must not.  The
pre-commit hook runs ``tools.run_ci --fast`` under its own interpreter rather
than the project's virtual environment, and ``run_ci`` reaches here through
``tools/_ci_steps.py``; a third-party import at this depth turns every commit
into a traceback on a machine whose bare interpreter lacks the package.  A
helper that needs one belongs in a module only the gates that use it import,
as the ratchet record reader does in ``tools/_ratchet.py``.
"""

from __future__ import annotations

import atexit
import contextlib
import errno
import fcntl
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path
from typing import TYPE_CHECKING, NewType

if TYPE_CHECKING:
    from collections.abc import Callable, Generator, Mapping

# A path relative to the repository root, spelled as git prints it: `git ls-files`
# and `git diff --name-only` both use this spelling, and only a git listing mints one.
RelPath = NewType("RelPath", str)


def match_paren_content(text: str, start: int) -> str | None:
    """Return the content from ``start`` up to its matching close parenthesis.

    ``start`` is the index just past an opening ``(`` (depth already 1).  Scans
    forward tracking nested parentheses and returns the substring up to (but not
    including) the ``)`` that closes the opener.  Returns None when the parens
    are unbalanced (the run reaches the end of ``text`` first).  Shared by the
    Agda import parser and scanner to locate ``using``/``renaming`` clause bodies.
    """
    depth = 1
    i = start
    while i < len(text) and depth > 0:
        ch = text[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return text[start:i]
        i += 1
    return None


def split_top_level_semicolons(content: str) -> list[str]:
    """Split an Agda ``using``/``renaming`` clause body on top-level ``;``.

    Walks ``content`` character by character, tracking parenthesis depth, and
    cuts on every ``;`` seen at depth 0 (so a ``;`` nested inside ``(...)`` --
    e.g. a mixfix argument grouping -- never splits a name).  Each resulting
    segment is stripped; empty segments are dropped.  Used by the
    grammar-complete open detector (``tools._agda_opens``) to split a
    ``using``/``renaming`` clause into its individual names.
    """
    parts: list[str] = []
    depth = 0
    buf: list[str] = []
    for ch in content:
        if ch == "(":
            depth += 1
            buf.append(ch)
        elif ch == ")":
            depth -= 1
            buf.append(ch)
        elif ch == ";" and depth == 0:
            item = "".join(buf).strip()
            if item:
                parts.append(item)
            buf = []
        else:
            buf.append(ch)
    item = "".join(buf).strip()
    if item:
        parts.append(item)
    return parts


def emit(message: str = "") -> None:
    """Write one line to stdout, the gate scripts' human-readable result channel.

    A single chokepoint for tool output: keeps bare ``print`` out of the package
    (ruff ``T201``) while still sending results to stdout exactly as ``print``
    would.  Use this for normal output; diagnostics go to ``sys.stderr``.

    Flushes per line: gate output is read live through pipes (the pre-push
    hook, CI), where block buffering would otherwise hold lines back until the
    buffer fills or the process exits.
    """
    _ = sys.stdout.write(message + "\n")
    sys.stdout.flush()


def sha256_file(path: Path) -> str:
    """Return the hex SHA-256 of ``path``, read in fixed-size chunks."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def now_iso() -> str:
    """Return the current UTC time as a timezone-aware ISO-8601 string."""
    return datetime.now(UTC).isoformat()


def find_executable(name: str) -> str:
    """Return the absolute path of ``name`` on PATH, raising if it is absent.

    Resolving to a full path keeps subprocess calls clear of ruff ``S607``
    (starting a process with a partial executable path).
    """
    resolved = shutil.which(name)
    if resolved is None:
        message = f"required executable not found on PATH: {name}"
        raise RuntimeError(message)
    return resolved


def run_capture(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    check: bool = False,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run ``cmd`` in text mode, capturing stdout and stderr.

    A thin wrapper over ``subprocess.run`` with the project's standard options.
    ``cmd[0]`` should be an absolute path (see ``find_executable``).  ``env``
    replaces the whole environment, as ``subprocess.run`` does, so a caller
    adding one variable passes ``os.environ | {...}``.
    """
    return subprocess.run(cmd, capture_output=True, text=True, cwd=cwd, check=check, env=env)


def run_streaming(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    sink: Callable[[str], object] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run ``cmd``, emitting each output line as it arrives and returning the whole.

    ``run_capture`` holds a child's output until the child exits, so a command
    killed by a wall clock -- a CI job's ``timeout-minutes``, a host reboot --
    takes its entire log with it, and while it runs there is no way to tell
    progress from a hang.  This helper writes every line out as the child
    produces it and accumulates the same text in the returned
    ``CompletedProcess``, so the caller parses what it always parsed.

    stderr is merged into stdout: interleaving is what makes a progress line
    and the diagnostic that follows it legible in one stream, and the returned
    object carries the merged text as ``stdout`` with ``stderr`` empty.

    ``sink`` receives one call per line, newline included (default: write to
    stderr and flush, which is where this package's own progress goes).  The
    child's environment gains ``PYTHONUNBUFFERED=1``: a Python child block
    buffers its stdout when it is a pipe rather than a terminal, which would
    defeat the whole point for a line this side flushes diligently.

    Text mode is what carries a progress bar: under universal newlines a bare
    carriage return ends a line, so a tool that redraws one line in place is
    read as a line per redraw rather than as one line at the end.  Both tools
    on the mutation lane draw one (mutmut a spinner, mull-runner a bar).
    """
    write_line = sink if sink is not None else _emit_progress
    child_env = (env if env is not None else os.environ.copy()) | {"PYTHONUNBUFFERED": "1"}
    lines: list[str] = []
    with subprocess.Popen(
        cmd,
        cwd=cwd,
        env=child_env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    ) as proc:
        # proc.stdout is not None because stdout=PIPE was requested.
        for line in proc.stdout:  # pyright: ignore[reportOptionalIterable]
            lines.append(line)
            _ = write_line(line)
        returncode = proc.wait()
    return subprocess.CompletedProcess(cmd, returncode, stdout="".join(lines), stderr="")


def _emit_progress(line: str) -> None:
    """Write one line to stderr, flushed, as ``run_streaming``'s default sink.

    A write that fails takes the filesystem's free space with it into the
    failure.  The one failure that reaches this sink is a full filesystem, and
    the traceback on its own names whichever progress line happened to be
    writing when the space ran out, which is never the cause.
    """
    try:
        _ = sys.stderr.write(line)
        sys.stderr.flush()
    except OSError as exc:
        message = f"cannot write progress: {exc}; {_stderr_space_note()}"
        raise RuntimeError(message) from exc


def _stderr_space_note() -> str:
    """Name what stderr writes to and the bytes left on its filesystem.

    ``fileno`` is absent under a capturing harness and on a stream that is not
    a file, so what cannot be measured is reported as unmeasured rather than
    raised over the failure it is there to describe.
    """
    try:
        fd = sys.stderr.fileno()
        stats = os.fstatvfs(fd)
    except (AttributeError, OSError, ValueError) as exc:
        return f"free space behind stderr is unknown ({exc})"
    try:
        target = str(Path(f"/proc/self/fd/{fd}").readlink())
    except OSError:
        target = f"file descriptor {fd}"
    return f"{target} has {stats.f_bavail * stats.f_frsize} bytes free"


def git_ls_files(repo: Path, *patterns: str) -> list[RelPath]:
    """Return git-tracked paths (repo-relative POSIX strings) under ``repo``.

    Optional ``patterns`` are passed as ``git ls-files`` pathspecs. The result is
    the set a fresh checkout contains, so resolving against it (rather than
    ``Path.exists()``) never sees an untracked / gitignored working-tree file.
    """
    listed = run_capture([find_executable("git"), "ls-files", *patterns], cwd=repo, check=True)
    return [RelPath(path) for path in listed.stdout.split()]


def git_toplevel(start: Path | None = None) -> Path:
    """Return the git work-tree root containing ``start`` (default: this file).

    Raises ``RuntimeError`` if ``start`` is not inside a git work tree.
    """
    anchor = start if start is not None else Path(__file__).resolve().parent
    result = run_capture(
        [find_executable("git"), "-C", str(anchor), "rev-parse", "--show-toplevel"],
    )
    if result.returncode != 0:
        message = f"not inside a git work tree: {anchor}"
        raise RuntimeError(message)
    return Path(result.stdout.strip())


def short_sha(repo_root: Path | None = None) -> str:
    """Return the short HEAD commit hash of the repository at ``repo_root``."""
    anchor = repo_root if repo_root is not None else git_toplevel()
    result = run_capture(
        [find_executable("git"), "-C", str(anchor), "rev-parse", "--short", "HEAD"],
        check=True,
    )
    return result.stdout.strip()


def prepare_artifact_dir(base: Path, sha: str) -> Path:
    """Return a fresh ``base / sha`` directory, removing any prior contents."""
    artifact_dir = base / sha
    if artifact_dir.exists():
        shutil.rmtree(artifact_dir)
    artifact_dir.mkdir(parents=True)
    return artifact_dir


def write_and_report_summary(artifact_dir: Path, summary: Mapping[str, object]) -> int:
    """Write ``summary.json`` under ``artifact_dir``, echo it, return the exit code.

    The exit code is 0 when ``summary["passed"]`` is truthy, else 1 -- the gate
    convention shared by the mutation and stability runners.
    """
    rendered = json.dumps(summary, indent=2)
    _ = (artifact_dir / "summary.json").write_text(rendered + "\n")
    emit(rendered)
    return 0 if summary["passed"] else 1


# --- crash-safe in-flight source restore ------------------------------------
# Shared by the warm-process tools that rewrite a source file in place to probe
# it (dead-import confirmation, IWYU narrowing) and must restore it even on an
# interrupt: track the original before each rewrite, untrack after restoring,
# and install handlers so SIGINT/SIGTERM/atexit restore anything still in flight.

_inflight: dict[str, str] = {}  # path -> original content
_restore_handlers_installed: list[bool] = []  # sentinel (mutated, not rebound)


def track_inflight(path: str, original: str) -> None:
    """Record `path`'s `original` content so an interrupt can restore it."""
    _inflight[path] = original


def untrack_inflight(path: str) -> None:
    """Drop `path` from the restore set (its rewrite has already been undone)."""
    _ = _inflight.pop(path, None)


def restore_inflight() -> None:
    """Restore every file left rewritten by an interrupted operation."""
    for path_str, original in list(_inflight.items()):
        with contextlib.suppress(OSError):
            _ = Path(path_str).write_text(original, encoding="utf-8")
    _inflight.clear()


def _signal_restore(signum: int, _frame: object) -> None:
    """SIGINT/SIGTERM handler: restore rewritten files, then exit."""
    restore_inflight()
    sys.exit(128 + signum)


def install_restore_handlers() -> None:
    """Install atexit + SIGINT/SIGTERM restore handlers once (idempotent)."""
    if _restore_handlers_installed:
        return
    _ = atexit.register(restore_inflight)
    for sig in (signal.SIGINT, signal.SIGTERM):
        _ = signal.signal(sig, _signal_restore)
    _restore_handlers_installed.append(True)


# --- repo-wide single-Agda lock ---------------------------------------------
# Every Agda-invoking tool acquires this one exclusive lock before it touches
# Agda over the source tree -- the read-only check-properties driver and the
# tools that rewrite-and-restore files in place to probe them (warm prune, the
# cold prune driver, warm dead-imports, warm IWYU) alike.  It enforces the
# project's standing "one agda -M16G at a time" rule and, more importantly,
# closes the read-during-write race: a second Agda op must not observe a file
# mid-prune-rewrite and draw a false verdict (the confound that corrupted an
# earlier prune validation run).
#
# Crash-safe BY CONSTRUCTION: the lock is an `flock` on an open fd, which the
# kernel releases when the holder exits for ANY reason -- including SIGKILL or a
# host crash -- so a crashed holder never leaves the tree locked.  The PID
# written into the file is purely diagnostic (it names the live holder in the
# contention message).  Release rides the context manager's `finally` (normal
# exit, or the SIGINT/SIGTERM `sys.exit` from `install_restore_handlers`).

_AGDA_LOCK_NAME = ".agda-tree.lock"


def _agda_lock_path() -> Path:
    """Return the repo-root sentinel path for the single-Agda lock."""
    return git_toplevel() / _AGDA_LOCK_NAME


def _process_alive(pid: int) -> bool:
    """Return True if `pid` names a live process (signal-0 probe)."""
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True  # exists, owned by another user
    return True


def _read_lock_pid(fd: int) -> int:
    """Read the PID recorded in the lock file (for the contention message)."""
    try:
        _ = os.lseek(fd, 0, os.SEEK_SET)
        text = os.read(fd, 32).decode(errors="replace").strip()
    except OSError:
        return -1
    try:
        return int(text)
    except ValueError:
        return -1


def _acquire_agda_lock(*, wait: bool) -> int | None:
    """Acquire the repo-wide Agda lock via flock.

    When a live tool holds it: with ``wait`` the caller blocks until the holder
    releases, saying so once on stderr with the holder's pid; without it the
    tool exits with that message instead, so an interactive sweep started over
    a running one fails at once rather than queueing behind it.

    Returns the held fd (closed by `agda_tree_lock` to release), or None when the
    filesystem cannot lock -- in which case the tool proceeds unlocked rather
    than blocking all Agda tooling on a missing kernel feature.
    """
    path = _agda_lock_path()
    fd = os.open(path, os.O_CREAT | os.O_RDWR, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        holder = _read_lock_pid(fd)
        liveness = "alive" if _process_alive(holder) else "stale?"
        if wait:
            _ = sys.stderr.write(
                f"waiting for {_AGDA_LOCK_NAME}, held by another Agda tool "
                + f"(pid {holder}, {liveness})...\n"
            )
            sys.stderr.flush()
            fcntl.flock(fd, fcntl.LOCK_EX)
        else:
            os.close(fd)
            message = (
                f"another Agda tool holds {_AGDA_LOCK_NAME} (pid {holder}, {liveness}); "
                + "refusing to start a concurrent Agda op -- wait for it to finish "
                + "(this guards the read-during-write prune race)."
            )
            sys.exit(message)
    except OSError as exc:
        os.close(fd)
        if exc.errno in (errno.ENOLCK, errno.ENOSYS, errno.EOPNOTSUPP):
            _ = sys.stderr.write(
                f"warning: {path} does not support flock ({exc}); "
                + "proceeding without the single-Agda lock\n"
            )
            return None
        raise
    _ = os.ftruncate(fd, 0)
    _ = os.write(fd, f"{os.getpid()}\n".encode())
    return fd


@contextlib.contextmanager
def agda_tree_lock(*, wait: bool = False) -> Generator[None]:
    """Hold the exclusive repo-wide "one Agda process at a time" lock.

    Wrap any Agda-invoking tool body in this.  Acquires the lock, aborting with
    a message naming the live holder unless ``wait`` asks to queue behind it;
    the `finally` closes the fd, which frees the `flock`.  See the section
    comment for the crash-safety rationale.
    """
    fd = _acquire_agda_lock(wait=wait)
    try:
        yield
    finally:
        if fd is not None:
            with contextlib.suppress(OSError):
                os.close(fd)  # closing the fd releases the flock


# ---------------------------------------------------------------------------
# Tree-scanning gates
#
# The gates that read the tracked tree as prose share what counts as prose: a
# tracked file that is not one of these binary shapes, with Markdown code
# masked so a string quoted as an example is documentation rather than the
# project speaking. One definition, so a new gate cannot disagree with the
# others about what it reads.
# ---------------------------------------------------------------------------

BINARY_SUFFIXES: frozenset[str] = frozenset(
    {
        ".png",
        ".jpg",
        ".jpeg",
        ".gif",
        ".ico",
        ".pdf",
        ".agdai",
        ".so",
        ".o",
        ".woff",
        ".woff2",
        ".ttf",
        ".zip",
        ".gz",
        ".sig",
        ".key",
        ".pub",
        ".wasm",
        ".xlsx",
    }
)

MARKDOWN_SUFFIXES: frozenset[str] = frozenset({".md", ".markdown"})

_INLINE_CODE = re.compile(r"`[^`]*`")
_FENCE = re.compile(r"^\s*(```|~~~)")


def prose_lines(rel: str, text: str) -> list[tuple[int, str]]:
    """Return ``(1-based lineno, line)`` pairs of ``text`` that are the project's prose.

    A Markdown file drops fenced blocks and masks inline-code spans; every other
    file is returned whole, because a comment in a source file is the project
    speaking.
    """
    is_markdown = Path(rel).suffix in MARKDOWN_SUFFIXES
    out: list[tuple[int, str]] = []
    in_fence = False
    for lineno, line in enumerate(text.splitlines(), start=1):
        if is_markdown and _FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        out.append((lineno, _INLINE_CODE.sub("", line) if is_markdown else line))
    return out
