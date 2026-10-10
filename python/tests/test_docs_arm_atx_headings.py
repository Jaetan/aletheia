# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The ATX-heading arm of the documentation gate, run over planted trees.

A tree whose headings all open on a run of ``#`` yields nothing; each setext
heading yields one finding naming its document and first line.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.atx_headings import findings

from aletheia.common_types import PositiveInt, Prose

if TYPE_CHECKING:
    from pathlib import Path

_README = RelPath("README.md")
_GUIDE = RelPath("docs/guide.md")


def _setext(rel: RelPath, line: PositiveInt) -> Prose:
    """Return the finding for the setext heading on ``line`` of ``rel``."""
    return Prose(
        f"{rel}: line {line} is a heading only because a line of = or - follows it; "
        + "write it with a run of #, or put a blank line before a thematic break"
    )


def test_atx_headings_and_breaks_are_clean(tmp_path: Path) -> None:
    """Headings opening on a run of # and a break after a blank line: nothing is found."""
    repo = plant(tmp_path / "repo", {_README: Prose("# A\n\n## B\n\nText\n\n---\n\nMore\n")})
    assert run_planted(findings, repo) == list[Prose]()


def test_each_setext_heading_is_a_finding(tmp_path: Path) -> None:
    """A paragraph over = or over - is a heading; each is named by its first line, in order."""
    guide = Prose("# Guide\n\nTitle\n===\n\n---\n**Version**: 1\n**Updated**: today\n---\n")
    repo = plant(tmp_path / "repo", {_README: Prose("Front\n---\n"), _GUIDE: guide})
    assert run_planted(findings, repo) == [
        _setext(_README, 1),
        _setext(_GUIDE, 3),
        _setext(_GUIDE, 7),
    ]


@pytest.mark.parametrize(
    "text",
    [Prose("```\nTitle\n---\n```\n"), Prose("    Title\n    ---\n"), Prose("- item\n---\n")],
    ids=["fenced", "indented-code", "list-item-then-break"],
)
def test_an_underline_commonmark_reads_otherwise_is_no_heading(tmp_path: Path, text: Prose) -> None:
    """An underline in code, or a break after a list item, makes no heading."""
    repo = plant(tmp_path / "repo", {_README: text})
    assert run_planted(findings, repo) == list[Prose]()


def test_a_tree_with_no_document_read_is_a_finding(tmp_path: Path) -> None:
    """With no document the scan holds nothing, which is reported."""
    repo = plant(tmp_path / "repo", {RelPath("src/main.py"): Prose("print()\n")})
    assert run_planted(findings, repo) == [
        Prose("README.md: no document was read, so no heading is checked")
    ]
