# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the review-mark gate (``tools/check_no_review_marks.py``).

The mark-shaped strings in this file are deliberate FIXTURES for the detector.
The gate exempts this file by name (``_EXEMPT_FILES``), so they are never
flagged in the live tree — the same arrangement ``test_check_docs.py`` uses for
``check_docs``.
"""

from __future__ import annotations

import pytest

from tools.check_no_review_marks import is_exempt, scan_text


@pytest.mark.parametrize(
    "mark",
    [
        "AGDA-D-30.1",  # finding id
        "GO-A-6.1",
        "CPP-D-21.3",
        "CICD-A-5.4",  # finding id (agent-letter form)
        "R20-GO-A-3.7",  # round-prefixed finding id
        "PY-S-20",  # bare PY-S finding
        "R19 cluster 14",  # review-round cluster
        "R19P2",  # review-round phase
        "pre-R23",  # pre/post review round
        "post-R18",
        "cluster IV",  # roman-numeral cluster
        "Track E.10",  # track sub-label
        "(PR C)",  # PR-letter label
        "Lever B",  # lever label
    ],
)
def test_marks_are_flagged(mark: str) -> None:
    """Every unambiguous review-mark shape is detected in comment prose."""
    assert scan_text("src/Aletheia/Foo.agda", f"-- rationale: {mark} applies")


@pytest.mark.parametrize(
    "keep",
    [
        "cat 27",  # AGENTS coding-standard category
        "Agda cat 16",  # <LANG> cat <N>
        "G-A4",  # AGENTS guideline id
        "CICD-5.5",  # CI/CD security CONTROL (no agent letter)
        "CICD-2.2",
        "#171",  # GitHub PR number
        "Phase 6",  # project phase (capital-P, reserved)
        "DUMMY_NODE_VECTOR0",  # DBC domain identifier
        "ISO 11898-1:2015",  # domain clause reference
        "Mirrors Go aletheia.Backend",  # cross-binding pointer
    ],
)
def test_keeps_are_not_flagged(keep: str) -> None:
    """Legitimate references that merely resemble marks are not flagged."""
    assert not scan_text("src/Aletheia/Foo.agda", f"-- see {keep} for the rule")


def test_markdown_fenced_code_is_masked() -> None:
    """A mark shown inside a fenced code block is documentation, not a live mark."""
    assert scan_text("docs/x.md", "prose R19 cluster 14 here")
    assert not scan_text("docs/x.md", "```\nR19 cluster 99 in a fence\n```\n")


def test_markdown_inline_code_is_masked() -> None:
    """A mark shown as an inline `code` span in Markdown is skipped."""
    assert not scan_text("docs/x.md", "shown as `AGDA-C-6.2` inline")


def test_source_comment_is_not_masked() -> None:
    """In non-Markdown files a backtick does not mask — source comments are scanned."""
    assert scan_text("src/Aletheia/Foo.agda", "-- `AGDA-C-6.2` in a doc-comment")


def test_keep_spans_are_masked() -> None:
    """A mark inside a [[wikilink]] or a memory/*.md pointer is masked, not flagged."""
    assert not scan_text("CLAUDE.md", "see [[project pre-R23 notes]] next")
    assert not scan_text("CLAUDE.md", "see memory/project_pre-R23_notes.md here")
    # control: the same mark outside a keep-span IS flagged
    assert scan_text("CLAUDE.md", "the pre-R23 behavior described here")


@pytest.mark.parametrize(
    "rel",
    [
        "tools/review_db.py",
        "tools/check_docs.py",
        "tools/check_no_review_marks.py",
        "python/tests/test_check_docs.py",
        "python/tests/test_check_no_review_marks.py",
        ".archive/reviews/r20/round.yaml",
    ],
)
def test_exempt_files_are_exempt(rel: str) -> None:
    """The work-record, the detectors, and their fixtures are exempt."""
    assert is_exempt(rel)


@pytest.mark.parametrize("rel", ["src/Aletheia/Error.agda", "CHANGELOG.md"])
def test_live_files_are_not_exempt(rel: str) -> None:
    """Ordinary tracked files are in scope for the gate."""
    assert not is_exempt(rel)
