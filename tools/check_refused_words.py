# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Refused-word gate: words this project does not use about its own work.

A word that asserts a judgement the record cannot support reads as evidence
while carrying none. The tree is written so that a claim is either measured or
named as unverified, so the words below have no place in it, in prose, in a
comment, in a commit-adjacent document or in a probe's output.

## What it refuses, and what to write instead

* ``spurious`` — it calls an observation false without saying what makes it so.
  A measurement that no rerun reproduces is a measurement that no rerun
  reproduces; a report nothing attributes is unattributed. Write which it is:
  ``a leak report no rerun reproduces``, ``a failure no allocation is
  attributed to``, ``an unexplained wake-up``. If the cause is known, name the
  cause instead.

The list is meant to grow, one entry per word the project refuses, each with
the reason it is refused and what carries the meaning honestly.

## What it does not touch

* ``tools/check_refused_words.py`` and its unit test — they carry the words as
  detectors and fixtures.
* Markdown fenced blocks and inline-code spans — a word quoted as an example is
  documentation, not the project speaking.
* Untracked files and the vendored trees, which ``git ls-files`` never lists.

Run ``python -m tools.check_refused_words`` from the repository root. Its
parser is unit-tested by ``python/tests/test_check_refused_words.py``.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from tools._common import BINARY_SUFFIXES, emit, git_ls_files, prose_lines

REPO = Path(__file__).resolve().parent.parent

# The detectors and their fixtures carry the words themselves.
_EXEMPT_FILES = {
    "tools/check_refused_words.py",
    "python/tests/test_check_refused_words.py",
}

# One entry per refused word: the pattern that finds it and what to write.
_REFUSED: list[tuple[re.Pattern[str], str]] = [
    (
        re.compile(r"\bspurious\w*\b", re.IGNORECASE),
        "say what the observation is instead: not reproduced, unattributed, or the cause itself",
    ),
]


def is_exempt(rel: str) -> bool:
    """Return True for the detector and its fixtures."""
    return rel in _EXEMPT_FILES


def scan_text(rel: str, text: str) -> list[str]:
    """Return findings for ``text`` treated as file ``rel`` (empty = clean)."""
    findings: list[str] = []
    for lineno, line in prose_lines(rel, text):
        for pattern, instead in _REFUSED:
            findings.extend(
                f"{rel}:{lineno}: {match.group(0)!r} is refused; {instead}"
                for match in pattern.finditer(line)
            )
    return findings


def scan_file(rel: str) -> list[str]:
    """Return findings for one tracked file (empty = clean)."""
    try:
        text = (REPO / rel).read_text(encoding="utf-8", errors="replace")
    except OSError, ValueError:
        return []
    return scan_text(rel, text)


def check_tree() -> list[str]:
    """Return every refused word across the tracked, non-exempt tree."""
    findings: list[str] = []
    for rel in git_ls_files(REPO):
        if is_exempt(rel) or Path(rel).suffix in BINARY_SUFFIXES:
            continue
        findings.extend(scan_file(rel))
    return findings


def main() -> int:
    """Report every refused word in the tracked tree; non-zero when any is found."""
    findings = check_tree()
    if findings:
        emit(f"check_refused_words: {len(findings)} refused word(s):")
        for finding in findings:
            emit(f"  {finding}")
        return 1
    emit(f"check_refused_words: none of the {len(_REFUSED)} refused word(s) in the tracked tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
