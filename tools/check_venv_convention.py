# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Enforce the single-venv convention: exactly one virtualenv, at python/.venv.

The project uses **one** Python virtual environment, living at ``python/.venv``.
Every tool resolves it there (``tools/run_ci.py``, the mutation/stability
runners, ``python/pyproject.toml``'s basedpyright ``venvPath``), so a second
venv — most commonly a repo-root ``.venv`` created by following a doc that
forgot to ``cd python`` first — silently diverges from what the gates use. That
exact drift once masked a basedpyright misconfiguration (a stray repo-root
``.venv`` shadowed the real one); this gate prevents its return.

Two enforcement checks, both needing no venv *packages* (only the stdlib) — this
gate *inspects* the venv, so it must not depend on one being installed:

1. **On-disk uniqueness** — the only ``pyvenv.cfg`` in the tree may live at
   ``python/.venv``. A stray venv anywhere else fails with a removal hint. (In a
   fresh CI checkout no venv exists yet, so this is a no-op there; it earns its
   keep locally, where strays accumulate.)

2. **Tracked-doc/script scan** — no committed file may instruct creating or
   entering a venv outside ``python/.venv``. Concretely, every ``python -m venv``
   target and every ``.venv/bin/...`` access must either name ``python/.venv``
   explicitly or sit in a scope that ``cd python`` first (a markdown fenced block
   or a single prose line). This stops the *source* of stray root venvs.

Run: ``python -m tools.check_venv_convention`` (exit 0 = clean, 1 = violations).
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

from tools._common import emit, find_executable, run_capture

# The one true venv, repo-root-relative.
CANONICAL_VENV = "python/.venv"

# Extensions whose contents are scanned for venv instructions.
_SCANNED_SUFFIXES = frozenset({".md", ".sh", ".bash", ".fish", ".yaml", ".yml", ".py", ".txt"})

# A venv-creation command: `python -m venv <target>` (any python spelling).
_CREATE_RE = re.compile(r"\bpython[0-9.]*\s+-m\s+venv\s+(?P<target>\S+)")
# Any access into a venv's bin/ directory: `<prefix>.venv/bin/...`.
_BIN_RE = re.compile(r"(?P<prefix>\S*)\.venv/bin/")
# A directory change into python/ (scopes a subsequent bare `.venv` correctly).
_CD_PYTHON_RE = re.compile(r"\bcd\s+\.?/?python\b")


def repo_root() -> Path:
    """Return the repository root (this file lives in ``<root>/tools``)."""
    return Path(__file__).resolve().parent.parent


def find_stray_venvs(root: Path) -> list[Path]:
    """Return directories holding a ``pyvenv.cfg`` other than ``python/.venv``."""
    allowed = (root / CANONICAL_VENV).resolve()
    strays: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        # Never descend into .git; it holds no venvs and is large.
        if ".git" in dirnames:
            dirnames.remove(".git")
        if "pyvenv.cfg" in filenames:
            here = Path(dirpath).resolve()
            if here != allowed:
                strays.append(here)
            # A venv's contents are never venvs — stop descending. Crucial for
            # python/.venv, which holds thousands of site-packages files.
            dirnames.clear()
    return sorted(strays)


def _norm(tok: str) -> str:
    """Normalise a venv path token: drop quotes/backticks, a ``./``, a trailing ``/``.

    ``removeprefix`` (not ``lstrip("./")``, which strips *characters* and would
    turn ``.venv`` into ``venv``) drops the leading ``./``.
    """
    return tok.strip("\"'`").removeprefix("./").rstrip("/")


def _target_is_canonical(target: str) -> bool:
    """Return True if a `-m venv` target names python/.venv explicitly."""
    return _norm(target) == CANONICAL_VENV


def _target_is_bare(target: str) -> bool:
    """Return True if a `-m venv` target is a bare `.venv` (resolves under the cwd)."""
    return _norm(target) == ".venv"


def _prefix_is_canonical(prefix: str) -> bool:
    """Return True if a `<prefix>.venv/bin/` access names python/.venv explicitly."""
    # prefix is everything up to ".venv"; canonical iff it ends with "python/".
    return prefix.strip("\"'`").endswith("python/")


def _scope_enters_python(scope: str) -> bool:
    """Return True if the scope `cd`s into python/ (so a bare `.venv` resolves there)."""
    return _CD_PYTHON_RE.search(scope) is not None


def _scan_scope(scope: str, lines: list[tuple[int, str]], rel: str) -> list[str]:
    """Flag root-venv create/access tokens in one scope (block or line)."""
    findings: list[str] = []
    enters_python = _scope_enters_python(scope)
    for lineno, line in lines:
        for m in _CREATE_RE.finditer(line):
            target = m.group("target")
            if _target_is_canonical(target) or (_target_is_bare(target) and enters_python):
                continue
            findings.append(
                f"{rel}:{lineno}: `python -m venv {target}` is not the canonical "
                + f"{CANONICAL_VENV} (and the scope does not `cd python` first)"
            )
        for m in _BIN_RE.finditer(line):
            prefix = m.group("prefix")
            if _prefix_is_canonical(prefix) or enters_python:
                continue
            findings.append(
                f"{rel}:{lineno}: `.venv/bin/...` access is not scoped to "
                + f"{CANONICAL_VENV} (use `python/.venv/bin/...` or `cd python` first)"
            )
    return findings


def _scan_markdown(text: str, rel: str) -> list[str]:
    """Scan a markdown file: each fenced ``` block is one scope; so is each line."""
    findings: list[str] = []
    in_fence = False
    block: list[tuple[int, str]] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        if line.lstrip().startswith("```"):
            if in_fence:  # closing fence — analyse the accumulated block
                scope = "\n".join(t for _, t in block)
                findings += _scan_scope(scope, block, rel)
                block = []
            in_fence = not in_fence
            continue
        if in_fence:
            block.append((lineno, line))
        else:
            # Prose line (may carry an inline `cd python && ... venv` recipe).
            findings += _scan_scope(line, [(lineno, line)], rel)
    if block:  # unterminated fence — analyse what we have
        scope = "\n".join(t for _, t in block)
        findings += _scan_scope(scope, block, rel)
    return findings


def _scan_plain(text: str, rel: str) -> list[str]:
    """Scan a non-markdown file as a single whole-file scope."""
    lines = list(enumerate(text.splitlines(), start=1))
    return _scan_scope(text, lines, rel)


def _tracked_files(root: Path) -> list[Path]:
    """Return git-tracked files (so generated/untracked artefacts are ignored)."""
    git = find_executable("git")
    out = run_capture([git, "ls-files", "-z"], cwd=root, check=True).stdout
    return [root / p for p in out.split("\0") if p]


def scan_tracked_docs(root: Path) -> list[str]:
    """Flag every tracked doc/script that points at a non-canonical venv."""
    findings: list[str] = []
    this_file = Path(__file__).resolve()
    for path in _tracked_files(root):
        if path.suffix not in _SCANNED_SUFFIXES:
            continue
        if path.resolve() == this_file:
            continue  # this gate names .venv in prose/patterns by necessity
        try:
            text = path.read_text(encoding="utf-8")
        except OSError, UnicodeDecodeError:
            continue
        rel = path.relative_to(root).as_posix()
        if path.suffix == ".md":
            findings += _scan_markdown(text, rel)
        else:
            findings += _scan_plain(text, rel)
    return findings


def main() -> int:
    """Run both checks; print findings; return 0 (clean) or 1 (violations)."""
    root = repo_root()
    strays = find_stray_venvs(root)
    doc_findings = scan_tracked_docs(root)

    if not strays and not doc_findings:
        emit(f"check-venv-convention: OK — single venv at {CANONICAL_VENV}")
        return 0

    if strays:
        emit("check-venv-convention: stray venv(s) found (only python/.venv allowed):")
        for s in strays:
            try:
                shown = s.relative_to(root).as_posix()
            except ValueError:
                shown = str(s)
            emit(f"  - {shown}/  →  remove it:  rm -rf {shown}")
    if doc_findings:
        emit("check-venv-convention: tracked files reference a non-canonical venv:")
        for f in doc_findings:
            emit(f"  - {f}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
