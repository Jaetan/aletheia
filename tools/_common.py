"""Shared helpers for the Aletheia developer tooling (the tools/ package).

Centralises the small boilerplate that several gate scripts would otherwise
duplicate -- stdout emission, content hashing, subprocess invocation, git
metadata, timestamps, artifact directories -- so each lives in exactly one
place.  Imported as ``from tools._common import ...``; the tools are invoked
as ``python -m tools.X`` (see ``tools/__init__.py``).
"""

from __future__ import annotations

import hashlib
import shutil
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path


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
    segment is stripped; empty segments are dropped.  Shared verbatim by the
    dead-import parser (``prune_unused_imports``) and the regex scanner
    (``scan_dead_imports``) so the two agree on name boundaries.
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
    """
    _ = sys.stdout.write(message + "\n")


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
) -> subprocess.CompletedProcess[str]:
    """Run ``cmd`` in text mode, capturing stdout and stderr.

    A thin wrapper over ``subprocess.run`` with the project's standard options.
    ``cmd[0]`` should be an absolute path (see ``find_executable``).
    """
    return subprocess.run(cmd, capture_output=True, text=True, cwd=cwd, check=check)


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
