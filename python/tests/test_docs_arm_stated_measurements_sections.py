# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""How the stated-measurements arm reads BENCHMARKS.md: its sections and tables, as CommonMark.

A section runs from its heading to the next heading of level two or shallower,
code neither ending it nor adding a row; its lines are read from the first and
stay apart; and a table row is a row of a table inside it.  The arm's claims about
what each measurement must equal are tested in
``python/tests/test_docs_arm_stated_measurements.py``.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _benchmarks_tree import DOCUMENT, edited_files, planted_findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

    from tools._common import RelPath


@pytest.mark.parametrize(
    "files",
    [
        pytest.param(
            edited_files(
                DOCUMENT, Prose("## Canonical Results\n"), Prose("## Canonical Results ##\n")
            ),
            id="closing-run-on-the-heading",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("## Canonical Results\n"),
                Prose("## Canonical Results\n\n```\n## Not a heading\n```\n"),
            ),
            id="fenced-heading-shaped-line",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("## Canonical Results\n"),
                Prose("## Canonical Results\n\n```\n| Lane C | 1 | 2 |\n```\n"),
            ),
            id="fenced-row",
        ),
    ],
)
def test_the_section_and_its_table_are_read_as_commonmark_reads_them(
    tmp_path: Path, files: Mapping[RelPath, Prose]
) -> None:
    """A closed heading opens the section, and code inside it neither ends it nor adds a row."""
    assert planted_findings(tmp_path, files) == list[Prose]()


@pytest.mark.parametrize(
    "files",
    [
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose(
                    "## Canonical Results\n\nPer-binding throughput, the committed baseline set.\n"
                    + "No lane's standard deviation exceeds 2.0% of its mean.\n"
                ),
                Prose(
                    "## Canonical Results\nNo lane's standard deviation exceeds 2.0% of its mean.\n"
                    + "Per-binding throughput, the committed baseline set.\n"
                ),
            ),
            id="bound-on-the-first-line",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.14\n.0 and the runtime that"),
            ),
            id="a-line-break-ends-a-version",
        ),
    ],
)
def test_the_sections_lines_are_read_whole_and_apart(
    tmp_path: Path, files: Mapping[RelPath, Prose]
) -> None:
    """A section's first line is read, and its lines stay apart when joined."""
    assert planted_findings(tmp_path, files) == list[Prose]()


def test_a_bound_stated_in_another_section_is_not_the_tables(tmp_path: Path) -> None:
    """The bound moved under the next heading leaves the canonical section without one."""
    bound = Prose("No lane's standard deviation exceeds 2.0% of its mean.\n")
    files = edited_files(
        DOCUMENT,
        Prose("## Local baselines\n"),
        Prose(f"## Local baselines\n{bound}"),
        edited_files(DOCUMENT, bound, Prose("")),
    )
    assert planted_findings(tmp_path, files) == [
        Prose(f"{DOCUMENT}: the section no longer states a standard-deviation bound")
    ]


def test_a_table_right_under_the_heading_is_read_from_its_header(tmp_path: Path) -> None:
    """A header row on the section's first line is a row of the section."""
    prose = Prose(
        "Per-binding throughput, the committed baseline set.\n"
        + "No lane's standard deviation exceeds 2.0% of its mean.\n\n"
    )
    files = edited_files(
        DOCUMENT,
        Prose("| Lane B | 50,000 | 25,000 |\n"),
        Prose(f"| Lane B | 50,000 | 25,000 |\n\n{prose}"),
        edited_files(
            DOCUMENT, Prose(f"## Canonical Results\n\n{prose}"), Prose("## Canonical Results\n")
        ),
    )
    assert planted_findings(tmp_path, files) == list[Prose]()


def test_a_narrower_second_table_is_a_finding(tmp_path: Path) -> None:
    """A row with fewer cells than the header's columns, from a second table, is named."""
    files = edited_files(
        DOCUMENT,
        Prose("| 50,000 | 25,000 |\n"),
        Prose("| 50,000 | 25,000 |\n\n| Lane A | 1 |\n|---|---|\n"),
    )
    assert planted_findings(tmp_path, files) == [
        Prose(f"{DOCUMENT}: Lane A: 1 cells under 2 columns")
    ]


def test_the_sections_last_line_is_read(tmp_path: Path) -> None:
    """A bound stated on the line right before the next heading is in the section."""
    bound = Prose("No lane's standard deviation exceeds 2.0% of its mean.\n")
    files = edited_files(
        DOCUMENT,
        Prose("\n## Local baselines\n"),
        Prose(f"\n{bound}## Local baselines\n"),
        edited_files(DOCUMENT, bound, Prose("")),
    )
    assert planted_findings(tmp_path, files) == list[Prose]()


def test_a_bound_broken_across_lines_is_not_stated(tmp_path: Path) -> None:
    """The section's lines are joined by line ends, so a number split over two is no number."""
    files = edited_files(DOCUMENT, Prose("exceeds 2.0% of"), Prose("exceeds 2.\n0% of"))
    assert planted_findings(tmp_path, files) == [
        Prose(f"{DOCUMENT}: the section no longer states a standard-deviation bound")
    ]


def test_a_version_opening_a_line_is_stated(tmp_path: Path) -> None:
    """The prose's lines are joined by line ends alone, so a runtime opening a line is read."""
    files = edited_files(
        DOCUMENT, Prose("records the runtime that"), Prose("records\nPython 3.99, the runtime that")
    )
    assert planted_findings(tmp_path, files) == [
        Prose(f"{DOCUMENT}: states Python 3.99; the baselines record ['3.14.5']")
    ]
