# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.docs_arms.phase_word``: the phase table and the pitch name one current phase.

Each test plants a tree holding a status document with a phase
table and a pitch with its ``Phase <n> is <word>`` sentence, then asks the arm
for its findings over that tree's tracked Markdown.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.phase_word import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_TABLE = Prose(
    "# Status\n\n"
    + "| Phase | Title | Status | Key deliverables |\n"
    + "|---|---|---|---|\n"
    + "| 1   | Core | ✅ | The pipeline. |\n"
    + "| 5.1 | Gaps | ✅ | The proofs. |\n"
    + "| 6   | Extensions | In progress | See below. |\n"
)
_PITCH = Prose("# Pitch\n\nPhases 1 through 5.1 are complete and Phase 6 is in progress. More.\n")
# A table whose open row carries a decimal label, and a pitch agreeing with it.
_DECIMAL_TABLE = Prose(
    "# Status\n\n| Phase | Title | Status | Key |\n|---|---|---|---|\n"
    + "| 1 | Core | ✅ | X. |\n| 5.1 | Gaps | In progress | Y. |\n"
)
_DECIMAL_PITCH = Prose("# Pitch\n\nPhase 5.1 is in progress. More.\n")
# A sentence shown as a code example is not a claim about the current phase.
_FENCED = Prose("# Guide\n\n```\nPhase 6 is planned.\n```\n")


def _findings(tmp_path: Path, files: dict[RelPath, Prose]) -> list[Prose]:
    """Plant ``files`` in a fresh tree and run the arm over it as the gate does."""
    return run_planted(findings, plant(tmp_path / "repo", files))


def test_table_and_pitch_agree(tmp_path: Path) -> None:
    """One open row and a pitch using its word: no finding, a fenced sentence being code."""
    found = _findings(
        tmp_path,
        {
            RelPath("PROJECT_STATUS.md"): _TABLE,
            RelPath("docs/PITCH.md"): _PITCH,
            RelPath("docs/GUIDE.md"): _FENCED,
        },
    )
    assert found == list[Prose]()


def test_a_fenced_table_row_is_not_read(tmp_path: Path) -> None:
    """A table row inside a fenced code block is an example, not a row of the phase table."""
    status = Prose(_TABLE + "\n~~~\n| 7   | Protocols | Planned | Later. |\n~~~\n")
    found = _findings(
        tmp_path, {RelPath("PROJECT_STATUS.md"): status, RelPath("docs/PITCH.md"): _PITCH}
    )
    assert found == list[Prose]()


def test_pitch_uses_another_word(tmp_path: Path) -> None:
    """The pitch calling the open phase planned is the drift the arm holds against."""
    pitch = Prose("# Pitch\n\nPhase 6 is planned. More.\n")
    found = _findings(
        tmp_path, {RelPath("PROJECT_STATUS.md"): _TABLE, RelPath("docs/PITCH.md"): pitch}
    )
    assert found == [
        Prose("docs/PITCH.md: says phase 6 is 'planned'; the table says 'in progress'")
    ]


def test_another_document_uses_another_word(tmp_path: Path) -> None:
    """Any tracked document's sentence about the open phase is held to the table's word."""
    guide = Prose("# Guide\n\nPhase 6 is the active track: see the status.\n")
    found = _findings(
        tmp_path,
        {
            RelPath("PROJECT_STATUS.md"): _TABLE,
            RelPath("docs/PITCH.md"): _PITCH,
            RelPath("docs/development/GUIDE.md"): guide,
        },
    )
    assert found == [
        Prose(
            "docs/development/GUIDE.md: says phase 6 is 'the active track'; "
            + "the table says 'in progress'"
        )
    ]


@pytest.mark.parametrize(
    "line",
    [
        Prose("- Phase 6 is complete\n"),
        Prose("Phase 6 is complete; nothing is open.\n"),
        Prose("Phase 6 is complete!\n"),
    ],
    ids=["line end", "semicolon", "exclamation mark"],
)
def test_whatever_ends_the_word_ends_the_sentence(tmp_path: Path, line: Prose) -> None:
    """The word runs to the first character that is not a letter or a space, or to the line end."""
    found = _findings(
        tmp_path,
        {
            RelPath("PROJECT_STATUS.md"): _TABLE,
            RelPath("docs/PITCH.md"): _PITCH,
            RelPath("docs/OTHER.md"): Prose("# Other\n\n" + line),
        },
    )
    assert found == [
        Prose("docs/OTHER.md: says phase 6 is 'complete'; the table says 'in progress'")
    ]


def test_a_sentence_in_lower_case_is_read(tmp_path: Path) -> None:
    """A sentence opening on ``phase`` in lower case is held to the table's word too."""
    guide = Prose("# Guide\n\nOnce phase 6 is planned, nothing changes.\n")
    found = _findings(
        tmp_path,
        {
            RelPath("PROJECT_STATUS.md"): _TABLE,
            RelPath("docs/PITCH.md"): _PITCH,
            RelPath("docs/GUIDE.md"): guide,
        },
    )
    assert found == [
        Prose("docs/GUIDE.md: says phase 6 is 'planned'; the table says 'in progress'")
    ]


@pytest.mark.parametrize(
    "sentence",
    [
        Prose("Phase 6 is In Progress. More."),
        Prose("Phase 6 is in progress (see the table)."),
        Prose("Phase 6 is in progress. Phase 6 is 50% done."),
    ],
    ids=["capitalised", "space before a bracket", "no letter after is"],
)
def test_the_word_is_compared_trimmed_and_in_any_case(tmp_path: Path, sentence: Prose) -> None:
    """The table's word capitalised or before a space agrees; ``is`` with no word says none."""
    pitch = Prose("# Pitch\n\n" + sentence + "\n")
    found = _findings(
        tmp_path, {RelPath("PROJECT_STATUS.md"): _TABLE, RelPath("docs/PITCH.md"): pitch}
    )
    assert found == list[Prose]()


def test_a_decimal_phase_can_be_the_open_one(tmp_path: Path) -> None:
    """A row labelled ``5.1`` is a phase: open, it is the current one the pitch is held to."""
    found = _findings(
        tmp_path,
        {RelPath("PROJECT_STATUS.md"): _DECIMAL_TABLE, RelPath("docs/PITCH.md"): _DECIMAL_PITCH},
    )
    assert found == list[Prose]()


@pytest.mark.parametrize(
    "line",
    [Prose("SubPhase 5.1 is planned.\n"), Prose("Phase 5x1 is planned.\n")],
    ids=["word ending in phase", "another character for the dot"],
)
def test_a_lookalike_sentence_is_not_read(tmp_path: Path, line: Prose) -> None:
    """``Phase`` opens a word and the label's dot is a dot: a near miss is about no phase."""
    found = _findings(
        tmp_path,
        {
            RelPath("PROJECT_STATUS.md"): _DECIMAL_TABLE,
            RelPath("docs/PITCH.md"): _DECIMAL_PITCH,
            RelPath("docs/OTHER.md"): Prose("# Other\n\n" + line),
        },
    )
    assert found == list[Prose]()


def test_pitch_silent_about_the_phase(tmp_path: Path) -> None:
    """A pitch with no sentence about the open phase is a finding, not a pass."""
    pitch = Prose("# Pitch\n\nEverything is complete.\n")
    found = _findings(
        tmp_path, {RelPath("PROJECT_STATUS.md"): _TABLE, RelPath("docs/PITCH.md"): pitch}
    )
    assert found == [Prose("docs/PITCH.md: says nothing about phase 6")]


def test_pitch_missing(tmp_path: Path) -> None:
    """A tree without the pitch is a finding."""
    found = _findings(tmp_path, {RelPath("PROJECT_STATUS.md"): _TABLE})
    assert found == [Prose("docs/PITCH.md: not a tracked document")]


def test_no_phase_table(tmp_path: Path) -> None:
    """A status document without a phase table holds nothing, so the scan reports it."""
    status = Prose("# Status\n\nNo table here.\n")
    found = _findings(
        tmp_path, {RelPath("PROJECT_STATUS.md"): status, RelPath("docs/PITCH.md"): _PITCH}
    )
    assert found == [Prose("PROJECT_STATUS.md: no phase table")]


def test_status_document_missing(tmp_path: Path) -> None:
    """A tree without the status document holds nothing, so the scan reports it."""
    found = _findings(tmp_path, {RelPath("docs/PITCH.md"): _PITCH})
    assert found == [Prose("PROJECT_STATUS.md: not a tracked document")]


def test_several_open_phases(tmp_path: Path) -> None:
    """Two rows not complete leave no one current phase, so the table itself is the finding."""
    status = Prose(_TABLE + "| 7   | Protocols | Planned | Later. |\n")
    found = _findings(
        tmp_path, {RelPath("PROJECT_STATUS.md"): status, RelPath("docs/PITCH.md"): _PITCH}
    )
    assert found == [
        Prose(
            "PROJECT_STATUS.md: 2 phases are not complete, so there is no one current phase: "
            + "6 (In progress), 7 (Planned)"
        )
    ]


def test_every_phase_complete(tmp_path: Path) -> None:
    """A table with every row complete names no current phase, so the table is the finding."""
    status = Prose(
        "# Status\n\n| Phase | Title | Status | Key |\n|---|---|---|---|\n| 1 | Core | ✅ | X. |\n"
    )
    found = _findings(
        tmp_path, {RelPath("PROJECT_STATUS.md"): status, RelPath("docs/PITCH.md"): _PITCH}
    )
    assert found == [
        Prose("PROJECT_STATUS.md: 0 phases are not complete, so there is no one current phase: ")
    ]


@pytest.mark.parametrize(
    ("line", "word"),
    [
        (Prose("Phase 6 is in-progress.\n"), Prose("in")),
        (Prose("Phase 6 is x.\n"), Prose("x")),
    ],
    ids=["a hyphen ends the word", "one letter"],
)
def test_the_word_is_its_run_of_letters_and_spaces(
    tmp_path: Path, line: Prose, word: Prose
) -> None:
    """Any other character ends the word, and a word of one letter is still a word."""
    found = _findings(
        tmp_path,
        {
            RelPath("PROJECT_STATUS.md"): _TABLE,
            RelPath("docs/PITCH.md"): _PITCH,
            RelPath("docs/OTHER.md"): Prose("# Other\n\n" + line),
        },
    )
    assert found == [
        Prose(f"docs/OTHER.md: says phase 6 is {word!r}; the table says 'in progress'")
    ]
