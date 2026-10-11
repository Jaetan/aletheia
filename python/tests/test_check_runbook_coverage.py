# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_runbook_coverage``: which log events the runbook's headings cover.

An event is covered by a level-four heading opening on its name as a code span,
read as CommonMark, so a heading-shaped line in code covers nothing.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from tools.check_runbook_coverage import covered_events

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path


def _covered(tmp_path: Path, runbook: Prose) -> set[Prose]:
    """Return the events among ``dbc.parsed`` and ``dbc`` the runbook ``runbook`` covers."""
    path = tmp_path / "RUNBOOK.md"
    _ = path.write_text(runbook, encoding="utf-8")
    return {Prose(name) for name in covered_events(path, ["dbc.parsed", "dbc"])}


@pytest.mark.parametrize(
    "runbook",
    [
        Prose("#### `dbc.parsed`\n"),
        Prose("#### `dbc.parsed` and what it means\n"),
        Prose("#### `dbc.parsed` ####\n"),
        Prose("   #### `dbc.parsed`\n"),
        Prose("#### ``dbc.parsed``\n"),
    ],
    ids=["bare", "trailing-text", "closing-run", "indented-three", "double-backticks"],
)
def test_a_level_four_heading_opening_on_the_name_covers_it(tmp_path: Path, runbook: Prose) -> None:
    """The heading may carry more text after the span, a closing run, or an indent under four."""
    assert _covered(tmp_path, runbook) == {Prose("dbc.parsed")}


@pytest.mark.parametrize(
    "runbook",
    [
        Prose("```\n#### `dbc.parsed`\n```\n"),
        Prose("####\n`dbc.parsed`\n"),
        Prose("##### `dbc.parsed`\n"),
        Prose("#### The `dbc.parsed` event\n"),
        Prose("#### `dbc.parsedx`\n"),
        Prose("#### `dbc.parsed``\n"),
    ],
    ids=[
        "fenced",
        "run-on-its-own-line",
        "level-five",
        "span-not-first",
        "longer-name",
        "unclosed",
    ],
)
def test_anything_else_covers_nothing(tmp_path: Path, runbook: Prose) -> None:
    """A fenced line, an empty heading over the name, another level or a later span: none."""
    assert _covered(tmp_path, runbook) == set[Prose]()
