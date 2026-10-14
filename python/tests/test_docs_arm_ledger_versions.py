# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The documentation gate's arm holding the building guide's dependency ledger free of versions.

A version number on any line of the ``## Dependencies and Licenses`` section,
its subsections included, in prose, a table cell, a code span or a fenced
block, is a finding naming the line and the version, a leading ``v`` with it,
in line order; an SPDX licence identifier is no version, and a line outside the
section is not read.  A table header of the section with a ``Version`` or
``Versions`` column, in any case, is a finding naming the header's line.  A
section whose lines lost the pointer ``Versions are not repeated here`` is a
finding.  The findings come as columns, then versions, then the pointer; a guide
without the section, untracked, or tracked and absent from the work tree is a
finding alone.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools.docs_arms import BUILDING_GUIDE
from tools.docs_arms.ledger_versions import findings

from aletheia.common_types import PositiveInt, Prose

if TYPE_CHECKING:
    from pathlib import Path

# Line numbers: 7 the ledger heading, 9 its lead, 11 a prose line, 13 a
# subsection, 15 its table header, 17 and 18 its rows, 21 a fenced line, 23 the
# ledger's last line, 24 the next section's heading, 26 that section's line.
_GUIDE = Prose("""# Building

## Prerequisites

The toolchain is listed here.

## Dependencies and Licenses

What Aletheia depends on. Versions are not repeated here: each pin is in its build file.

Aletheia is licensed under **BSD-2-Clause**; its test framework is under BSL-1.0.

### Runtime

| Dependency | License | Role |
|---|---|---|
| GHC RTS | BSD-3-Clause | Runtime system |
| libgmp | LGPL-3.0 | Bignum arithmetic |

```sh
ldd build/libaletheia-ffi.so
```

## Troubleshooting

Rebuild from clean.
""")
_PROSE = Prose("Aletheia is licensed under **BSD-2-Clause**; its test framework is under BSL-1.0.")
_HEADER = Prose("| Dependency | License | Role |")
_ROW = Prose("| GHC RTS | BSD-3-Clause | Runtime system |")
_SECOND_ROW = Prose("| libgmp | LGPL-3.0 | Bignum arithmetic |")
_FENCED = Prose("ldd build/libaletheia-ffi.so")
_POINTER = Prose("Versions are not repeated here: each")
_LOST_POINTER = Prose(
    f"{BUILDING_GUIDE}: the ledger no longer says 'Versions are not repeated here'"
)


def _edited(*edits: tuple[Prose, Prose]) -> Prose:
    """Return the planted guide with each ``(old, new)`` text replaced, refusing a no-op edit."""
    text = str(_GUIDE)
    for old, new in edits:
        assert old in text, old
        text = text.replace(old, new)
    return Prose(text)


def _run(tmp_path: Path, guide: Prose) -> list[Prose]:
    """Run the arm over a tree holding ``guide`` as the building guide."""
    return run_planted(findings, plant(tmp_path, {BUILDING_GUIDE: guide}))


def _stated(line: PositiveInt, version: Prose) -> Prose:
    """Return the finding for ``version`` stated on ``line`` of the guide."""
    return Prose(f"{BUILDING_GUIDE}:{line}: the ledger states the version {version}")


def test_a_version_column_right_under_the_heading_is_read(tmp_path: Path) -> None:
    """A table on the line after the ledger's heading is the ledger's, its header read."""
    guide = Prose(
        "# Building\n\n## Dependencies and Licenses\n| Package | Version |\n|---|---|\n"
        + "| a | b |\n\nVersions are not repeated here.\n"
    )
    assert _run(tmp_path, guide) == [_column(4)]


def _column(line: PositiveInt) -> Prose:
    """Return the finding for the version column of the table header on ``line``."""
    return Prose(f"{BUILDING_GUIDE}:{line}: a ledger table has a version column")


def test_a_ledger_stating_no_version_has_no_finding(tmp_path: Path) -> None:
    """A ledger naming licences, a table and a command, and keeping its pointer, is clean."""
    assert _run(tmp_path, _GUIDE) == list[Prose]()


def test_a_version_in_prose_is_a_finding(tmp_path: Path) -> None:
    """A version a prose line states is named with its line."""
    guide = _edited((Prose("its test framework"), Prose("its test framework Catch2 3.7.1")))
    assert _run(tmp_path, guide) == [_stated(11, Prose("3.7.1"))]


def test_a_version_in_a_table_cell_of_a_subsection_is_a_finding(tmp_path: Path) -> None:
    """A version in a cell of a table under a subsection of the ledger is named with its row."""
    guide = _edited((_ROW, Prose("| GHC RTS 9.6.7 | BSD-3-Clause | Runtime system |")))
    assert _run(tmp_path, guide) == [_stated(17, Prose("9.6.7"))]


def test_a_version_in_a_code_span_is_a_finding(tmp_path: Path) -> None:
    """A version inside a code span is read as the line spells it."""
    guide = _edited((_PROSE, Prose("The header is `nlohmann/json 3.11.3`, under MIT.")))
    assert _run(tmp_path, guide) == [_stated(11, Prose("3.11.3"))]


def test_a_version_in_a_fenced_block_is_a_finding(tmp_path: Path) -> None:
    """A version in a fenced code block of the ledger is read like prose."""
    guide = _edited((_FENCED, Prose("pip install 'hypothesis>=6.100.1'")))
    assert _run(tmp_path, guide) == [_stated(21, Prose("6.100.1"))]


def test_a_leading_v_is_taken_with_the_version(tmp_path: Path) -> None:
    """A version written with a leading v is named with it."""
    guide = _edited(
        (Prose("its test framework"), Prose("its test framework, built by Clang v23.1,"))
    )
    assert _run(tmp_path, guide) == [_stated(11, Prose("v23.1"))]


def test_a_number_joined_to_a_word_before_it_is_no_version(tmp_path: Path) -> None:
    """A number whose v is joined to a word before it, as in rev1.0, is not read."""
    guide = _edited((Prose("its test framework"), Prose("its test framework at rev1.0")))
    assert _run(tmp_path, guide) == list[Prose]()


def test_versions_are_named_in_line_order_and_in_order_within_a_line(tmp_path: Path) -> None:
    """Several versions are named one each, by line, and by position on one line."""
    guide = _edited(
        (_FENCED, Prose("cabal install shake ==0.19.8")),
        (_ROW, Prose("| GHC RTS 9.6.7 | BSD-3-Clause | Runtime system |")),
        (Prose("its test framework"), Prose("Agda 2.7.0.1 and its test framework 3.7.1")),
    )
    assert _run(tmp_path, guide) == [
        _stated(11, Prose("2.7.0.1")),
        _stated(11, Prose("3.7.1")),
        _stated(17, Prose("9.6.7")),
        _stated(21, Prose("0.19.8")),
    ]


@pytest.mark.parametrize(
    "licence",
    [
        Prose("LGPL-3.0"),
        Prose("BSL-1.0"),
        Prose("GPL-2.0+"),
        Prose("Apache-2.0"),
        Prose("LGPL-2.1-or-later"),
    ],
    ids=["lgpl", "bsl", "gpl-plus", "apache", "or-later"],
)
def test_an_spdx_identifier_is_no_version(tmp_path: Path, licence: Prose) -> None:
    """A licence identifier's number is joined to its name, so it is not read as a version."""
    guide = _edited((_SECOND_ROW, Prose(f"| libgmp | {licence} | Bignum arithmetic |")))
    assert _run(tmp_path, guide) == list[Prose]()


def test_a_version_outside_the_ledger_is_not_read(tmp_path: Path) -> None:
    """A version in the section before the ledger, or the one after, is no finding."""
    guide = _edited(
        (Prose("The toolchain is listed here."), Prose("Install GHC 9.6.7 and Cabal 3.10.3.")),
        (Prose("Rebuild from clean."), Prose("Cabal 3.12 fails; rebuild from clean.")),
    )
    assert _run(tmp_path, guide) == list[Prose]()


def test_the_ledgers_first_and_last_lines_are_read_and_the_next_heading_is_not(
    tmp_path: Path,
) -> None:
    """The line after the ledger's heading and the line before the next heading are read."""
    guide = _edited(
        (
            Prose("## Dependencies and Licenses\n\n"),
            Prose("## Dependencies and Licenses\nGHC 9.6.7\n"),
        ),
        (Prose("```\n\n## Troubleshooting"), Prose("```\nCabal 3.12\n## Troubleshooting 6.0")),
    )
    assert _run(tmp_path, guide) == [_stated(8, Prose("9.6.7")), _stated(23, Prose("3.12"))]


@pytest.mark.parametrize(
    "cell",
    [Prose("Version"), Prose("versions"), Prose("VERSION"), Prose("**Versions**")],
    ids=["capital", "plural-lower", "upper", "emphasised"],
)
def test_a_version_column_is_a_finding(tmp_path: Path, cell: Prose) -> None:
    """A table header with a Version or Versions column, in any case, is named with its line."""
    guide = _edited((_HEADER, Prose(f"| Dependency | License | {cell} |")))
    assert _run(tmp_path, guide) == [_column(15)]


def test_a_body_cell_reading_versions_is_no_version_column(tmp_path: Path) -> None:
    """A row listing a package named versions heads no column, so it is no finding."""
    guide = _edited((_SECOND_ROW, Prose("| versions | BSD-3-Clause | Version parsing |")))
    assert _run(tmp_path, guide) == list[Prose]()


def test_a_version_column_outside_the_ledger_is_not_read(tmp_path: Path) -> None:
    """A table with a Version column in another section is no finding."""
    table = Prose("| Tool | Version |\n|---|---|\n| cabal | pinned |\n")
    guide = _edited((Prose("Rebuild from clean.\n"), Prose(f"Rebuild from clean.\n\n{table}")))
    assert _run(tmp_path, guide) == list[Prose]()


def test_a_lead_without_its_pointer_is_a_finding(tmp_path: Path) -> None:
    """A ledger whose lines no longer say where the versions are is a finding."""
    guide = _edited((_POINTER, Prose("Each")))
    assert _run(tmp_path, guide) == [_LOST_POINTER]


def test_a_pointer_outside_the_ledger_does_not_hold_it(tmp_path: Path) -> None:
    """The pointer moved to another section leaves the ledger without it."""
    guide = _edited(
        (_POINTER, Prose("Each")),
        (Prose("Rebuild from clean."), Prose("Versions are not repeated here.")),
    )
    assert _run(tmp_path, guide) == [_LOST_POINTER]


def test_findings_come_as_columns_then_versions_then_the_pointer(tmp_path: Path) -> None:
    """A version column is named before the versions, though a version stands above it."""
    guide = _edited(
        (_POINTER, Prose("Each")),
        (Prose("its test framework"), Prose("its test framework 3.7.1")),
        (_HEADER, Prose("| Dependency | License | Version |")),
        (_FENCED, Prose("ldd build/libaletheia-ffi.so.5.0 v1.2")),
    )
    assert _run(tmp_path, guide) == [
        _column(15),
        _stated(11, Prose("3.7.1")),
        _stated(21, Prose("v1.2")),
        _LOST_POINTER,
    ]


@pytest.mark.parametrize(
    "heading",
    [Prose("## Dependencies"), Prose("### Dependencies and Licenses")],
    ids=["renamed", "demoted"],
)
def test_a_guide_without_the_ledger_section_is_a_finding(tmp_path: Path, heading: Prose) -> None:
    """A guide whose ledger heading is renamed or demoted has no ledger, and says so alone."""
    guide = _edited(
        (Prose("## Dependencies and Licenses"), heading),
        (_ROW, Prose("| GHC RTS 9.6.7 | BSD-3-Clause | Runtime system |")),
    )
    assert _run(tmp_path, guide) == [
        Prose(f"{BUILDING_GUIDE}: has no ## Dependencies and Licenses section")
    ]


def test_an_untracked_guide_is_a_finding(tmp_path: Path) -> None:
    """A building guide git does not track leaves the ledger unchecked."""
    root = plant(tmp_path, {BUILDING_GUIDE: _GUIDE})
    assert run_planted(findings, root, untracked={BUILDING_GUIDE}) == [
        Prose(f"{BUILDING_GUIDE}: not tracked, so its dependency ledger is unchecked")
    ]


def test_a_tracked_guide_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A building guide git tracks and the work tree lacks is unread, and its ledger unchecked."""
    assert run_planted(findings, tmp_path, absent={BUILDING_GUIDE}) == [
        Prose(f"{BUILDING_GUIDE}: could not be read, so what it says is unchecked"),
        Prose(f"{BUILDING_GUIDE}: could not be read, so its dependency ledger is unchecked"),
    ]
