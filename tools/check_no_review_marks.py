# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Review-mark gate: no internal review-process marks in the live source tree.

The review *process* (round numbers, cluster letters, per-agent finding IDs) is
remembered in the archive — ``.archive/reviews/`` + ``tools/review_db.py`` — so
the live tree should read as a product, not a review log. This gate fails
(exit 1) when an internal review-process mark appears in any tracked file
outside that archive.

It complements ``tools/check_docs.py`` (which owns link/anchor resolution and is
Markdown-only): this gate is language-agnostic and covers the WHOLE tree —
Agda / Go / C++ / Python / Rust / Haskell source comments, build files, and the
history/guidance docs.

## What it flags (unambiguous shapes only)

Only shapes with no legitimate non-review meaning, so a green tree stays green
without whitelisting innocent content:

* finding IDs — ``AGDA-D-30.1``, ``GO-A-6.1``, ``R20-GO-A-3.7``, ``CICD-A-5.4``,
  ``PY-S-20.1`` (the agent-letter segment ``-A-`` distinguishes a finding from a
  self-defined control ID like ``CICD-5.5``, which is kept)
* round context — ``R19 cluster 14``, ``pre-R23``, ``post-R18``, ``R19P2``,
  ``cluster I``
* plan/PR labels — ``Track E.10``, ``(PR C)``, ``Lever B``

Ambiguous terms that also have ratified engineering uses — a bare ``Track A``,
``cluster``, ``slice``, ``tracer-bullet`` — are intentionally NOT gated here;
they are handled by the one-time human-guided sweep, not a standing regex.

## What it does not touch

* ``.archive/reviews/`` and ``tools/review_db.py`` — the work record (exempt).
* This gate + its unit test + ``check_docs`` and ITS unit test — they carry
  mark-shaped strings as detector patterns / fixtures (exempt).
* Markdown fenced blocks and inline-code spans — a mark shown as an example is
  documentation, not a live mark.
* ``[[wikilink]]`` targets and ``memory/<name>.md`` pointers — these resolve to
  real agent-store files whose names embed round/track tokens and cannot be
  renamed by a repo change.
* GitHub PR references (``#171``) — kept by design.

Run ``python -m tools.check_no_review_marks`` from the repo root. Its parsers are
unit-tested by ``python/tests/test_check_no_review_marks.py``.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from pathlib import Path
from typing import cast

from tools._common import emit, git_ls_files

REPO = Path(__file__).resolve().parent.parent

# Files/dirs that legitimately carry mark-shaped strings (work record, detectors,
# fixtures) — scanned-around, never flagged.
_EXEMPT_FILES = {
    "tools/review_db.py",
    "tools/check_docs.py",
    "tools/check_no_review_marks.py",
    "python/tests/test_check_docs.py",
    "python/tests/test_check_no_review_marks.py",
}
_EXEMPT_PREFIXES = (".archive/reviews/",)

# Binary / non-text tracked files we never scan.
_BINARY_SUFFIXES = {
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
}

_MD_SUFFIXES = {".md", ".markdown"}

# Spans masked before matching, on EVERY file: agent-store pointers whose names
# embed round/track tokens but resolve to real out-of-repo files.
_KEEP_SPANS = [
    re.compile(r"\[\[[^\]]*\]\]"),  # [[project_r25_binding_review]]
    re.compile(r"memory/[\w./-]+\.md"),  # memory/project_r25_binding_review.md
]
_INLINE_CODE = re.compile(r"`[^`]*`")
_FENCE = re.compile(r"^\s*(```|~~~)")

# The unambiguous review-mark shapes. Context-anchored so a clean tree has zero
# hits (a bare ``R23`` is NOT here — too noisy; ``R19 cluster`` / ``pre-R23`` are).
_PATTERNS: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"\b[Rr]\d+ cluster\b"), "review-round cluster"),
    (re.compile(r"\b[Rr]\d+[Pp][0-9]\b"), "review-round phase"),
    (re.compile(r"\b(?:pre|post)-R\d+\b"), "pre/post review-round"),
    (re.compile(r"\bcluster [IVX]{1,4}\b"), "cluster (roman)"),
    (
        re.compile(r"\b(?:AGDA|GO|CPP|PY|RUST|XBINDING|DOCS|CICD)-[A-Z]-\d+(?:\.\d+)?\b"),
        "finding id",
    ),
    (re.compile(r"\bR\d+-(?:AGDA|GO|CPP|PY|RUST|DOCS|CICD)-[A-Z]"), "round-prefixed finding id"),
    (re.compile(r"\bPY-S-\d+\b"), "PY-S finding"),
    (re.compile(r"\bTrack [A-E]\.\d"), "track sub-label"),
    (re.compile(r"\(PR [A-Z]\d*\)"), "PR-letter label"),
    (re.compile(r"\bLever [AB]\b"), "lever label"),
]


def is_exempt(rel: str) -> bool:
    """Return True for the work-record, the detectors, and their test fixtures."""
    return rel in _EXEMPT_FILES or rel.startswith(_EXEMPT_PREFIXES)


def _mask_keeps(line: str) -> str:
    for pat in _KEEP_SPANS:
        line = pat.sub("", line)
    return line


def scannable_lines(rel: str, text: str) -> list[tuple[int, str]]:
    """Return ``(1-based lineno, masked line)`` pairs to scan for ``rel``.

    Markdown files drop fenced code and mask inline-code spans (a mark shown as
    an example is documentation). All files mask the ``[[…]]`` / ``memory/…``
    keep-spans. Non-Markdown files are otherwise scanned raw — a review mark in
    a source comment is exactly what this gate exists to catch.
    """
    is_md = Path(rel).suffix in _MD_SUFFIXES
    out: list[tuple[int, str]] = []
    in_fence = False
    for i, line in enumerate(text.splitlines(), start=1):
        if is_md and _FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        masked = _INLINE_CODE.sub("", line) if is_md else line
        out.append((i, _mask_keeps(masked)))
    return out


def scan_text(rel: str, text: str) -> list[str]:
    """Return finding suffixes for ``text`` treated as file ``rel`` (empty = clean).

    The pure core of the scan — no filesystem — so the detector is unit-testable
    on synthetic input (``python/tests/test_check_no_review_marks.py``).
    """
    findings: list[str] = []
    for lineno, line in scannable_lines(rel, text):
        for pat, why in _PATTERNS:
            findings.extend(f"{rel}:{lineno}: {why} -> {m.group(0)!r}" for m in pat.finditer(line))
    return findings


def scan_file(rel: str) -> list[str]:
    """Return finding suffixes for one tracked file (empty = clean)."""
    path = REPO / rel
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError, ValueError:
        return []
    return scan_text(rel, text)


def check_tree() -> list[str]:
    """Return every review-mark finding across the tracked, non-exempt tree."""
    findings: list[str] = []
    for rel in git_ls_files(REPO):
        if is_exempt(rel) or Path(rel).suffix in _BINARY_SUFFIXES:
            continue
        findings.extend(scan_file(rel))
    return findings


def main(argv: list[str] | None = None) -> int:
    """Scan the tracked tree; return 1 (and list the marks) if any are found, else 0."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--summary",
        action="store_true",
        help="print per-file hit counts (burn-down view) instead of every finding",
    )
    args = parser.parse_args(argv)
    summary = cast("bool", args.summary)

    findings = check_tree()
    if findings:
        if summary:
            per_file = Counter(f.split(":", 1)[0] for f in findings)
            emit(f"check_no_review_marks: {len(findings)} mark(s) in {len(per_file)} file(s):")
            for rel, n in sorted(per_file.items(), key=lambda kv: -kv[1]):
                emit(f"  {n:>4}  {rel}")
        else:
            emit(f"check_no_review_marks: {len(findings)} review-process mark(s):")
            for f in findings:
                emit(f"  {f}")
        return 1
    emit("check_no_review_marks: no internal review-process marks in the live tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
