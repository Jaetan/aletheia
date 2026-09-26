# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the refused-word gate (``tools/check_refused_words.py``).

The refused words in this file are deliberate FIXTURES for the detector. The
gate exempts this file by name, the same arrangement the review-mark gate uses
for its own test.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import git, tracked_but_absent

from tools.check_refused_words import check_tree, is_exempt, main, scan_text

if TYPE_CHECKING:
    from pathlib import Path


@pytest.mark.parametrize(
    "line",
    [
        "a spurious wake-up",
        "it failed spuriously",
        "A Spurious report",
        "# the leak looks SPURIOUS",
    ],
)
def test_the_word_is_flagged_in_any_case_and_form(line: str) -> None:
    """Every case and inflection of a refused word is a finding."""
    assert scan_text("docs/x.md", line)


@pytest.mark.parametrize("line", ["a leak no rerun reproduces", "spur of the moment", "spurs"])
def test_other_words_are_not_flagged(line: str) -> None:
    """A word that merely starts the same way is not the refused one."""
    assert not scan_text("docs/x.md", line)


def test_the_finding_names_what_to_write_instead() -> None:
    """A finding carries the replacement, so the reader does not have to ask."""
    findings = scan_text("docs/x.md", "a spurious failure")
    assert len(findings) == 1
    assert "docs/x.md:1" in findings[0]
    assert "not reproduced" in findings[0]


def test_markdown_fenced_code_is_masked() -> None:
    """A word quoted inside a fenced block is documentation, not the project speaking."""
    assert not scan_text("docs/x.md", "```\nspurious\n```")


def test_markdown_inline_code_is_masked() -> None:
    """A word quoted inline is documentation too."""
    assert not scan_text("docs/x.md", "the flag `spurious` of another tool")


def test_source_comments_are_not_masked() -> None:
    """Source files are scanned whole: a comment is the project speaking."""
    assert scan_text("src/x.cpp", "// a spurious wake-up")


def test_the_detector_and_its_fixtures_are_exempt() -> None:
    """The two files that carry the words as data are not scanned."""
    assert is_exempt("tools/check_refused_words.py")
    assert is_exempt("python/tests/test_check_refused_words.py")
    assert not is_exempt("docs/architecture/PROTOCOL.md")


def test_the_tracked_tree_carries_none() -> None:
    """The gate's own subject: the live tree is clean, and every tracked file of it was read."""
    scan = check_tree()
    assert not scan.findings
    assert not scan.unreadable


def test_a_tracked_file_that_cannot_be_read_is_not_clean(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A tracked file the gate cannot read exits 2 and is named; the tree is not vouched for."""
    repo, rel = tracked_but_absent(tmp_path)
    assert main(repo=repo) == 2
    assert rel in capsys.readouterr().err


def test_an_unreadable_file_dominates_a_finding_and_the_finding_is_still_printed(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """With a refused word and an unreadable file, the exit is 2 and both are reported."""
    repo, rel = tracked_but_absent(tmp_path)
    _ = (repo / "prose.md").write_text("a spurious report\n", encoding="utf-8")
    git(repo, "add", "--", "prose.md")
    assert main(repo=repo) == 2
    captured = capsys.readouterr()
    assert "prose.md:1" in captured.out
    assert rel in captured.err
