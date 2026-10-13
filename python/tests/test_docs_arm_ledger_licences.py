# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.docs_arms.ledger_licences``: each Python ledger row names its licence.

``licence_findings`` is called over planted guide texts with a stand-in for the
installed distributions, so each finding it words is shown exactly;
``installed_licence`` is held to what ``importlib.metadata`` reports for
distributions this venv installs and for distributions planted on ``sys.path``;
``findings`` is run the way the documentation gate runs it.
"""

from __future__ import annotations

import importlib.metadata
import sys
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools._manifests import DistributionName
from tools.docs_arms import BUILDING_GUIDE
from tools.docs_arms.ledger_licences import findings, installed_licence, licence_findings
from tools.docs_arms.ledger_packages import PYTHON_LAYER

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence
    from pathlib import Path

_HEADER = Prose("| Package | Extra | License |\n|---|---|---|\n")
# The guide `_guide` builds holds its first table row on this line.
_FIRST_ROW = 7
_PYTEST = DistributionName("pytest")
_ABSENT = DistributionName("aletheia-no-such-distribution")
_NOTHING_AFTER = Prose("")
_TWO_COLUMNS = Prose("| Package | Extra |\n|---|---|\n")


def _guide(
    rows: Sequence[Prose], *, header: Prose = _HEADER, after: Prose = _NOTHING_AFTER
) -> Prose:
    """Return a building guide whose Python section holds a table of ``rows`` under ``header``."""
    return Prose(
        "# Building\n\n"
        + f"{PYTHON_LAYER}\n\n"
        + header
        + "".join(f"{row}\n" for row in rows)
        + "\n### License obligations\n\nAttribution only.\n"
        + after
    )


def _installed(
    licences: Mapping[DistributionName, Prose],
) -> Callable[[DistributionName], Prose | None]:
    """Return a stand-in answering each distribution's licence from ``licences``, None if absent."""

    def lookup(name: DistributionName) -> Prose | None:
        """Answer ``name``'s licence, or None for a distribution ``licences`` does not hold."""
        return licences.get(name)

    return lookup


def _recorded(name: DistributionName) -> Prose:
    """Read the licence ``importlib.metadata`` reports: License-Expression, else License."""
    recorded = importlib.metadata.metadata(name)
    return Prose(recorded.get("License-Expression") or recorded.get("License") or "")


def _plant_distribution(root: Path, name: DistributionName, headers: Prose) -> None:
    """Plant an installed distribution ``name`` under ``root`` whose metadata adds ``headers``."""
    dist_info = RelPath(f"{name.replace('-', '_')}-1.0.dist-info/METADATA")
    _ = plant(
        root,
        {dist_info: Prose(f"Metadata-Version: 2.4\nName: {name}\nVersion: 1.0\n{headers}")},
    )


def test_a_ledger_matching_the_installed_licences_has_no_finding() -> None:
    """Every row's licence equal to the installed one passes, the header row unread."""
    guide = _guide([Prose("| pyyaml | `[yaml]` | MIT |"), Prose("| openpyxl | `[excel]` | MIT |")])
    installed = _installed(
        {DistributionName("pyyaml"): Prose("MIT"), DistributionName("openpyxl"): Prose("MIT")}
    )
    assert licence_findings(guide, installed) == list[Prose]()


def test_a_licence_the_metadata_does_not_record_is_a_finding() -> None:
    """A row whose licence differs from the installed one names both, the recorded one quoted."""
    guide = _guide([Prose("| pyyaml | `[yaml]` | BSD-3-Clause |")])
    assert licence_findings(guide, _installed({DistributionName("pyyaml"): Prose("MIT")})) == [
        Prose(
            f"{BUILDING_GUIDE}:{_FIRST_ROW}: the ledger says pyyaml is BSD-3-Clause, "
            + "its metadata records 'MIT'"
        )
    ]


def test_a_distribution_not_installed_is_a_finding() -> None:
    """A row naming a distribution the venv does not install is reported, not skipped."""
    guide = _guide([Prose("| pyyaml | `[yaml]` | MIT |")])
    assert licence_findings(guide, _installed({})) == [
        Prose(
            f"{BUILDING_GUIDE}:{_FIRST_ROW}: pyyaml is not installed, "
            + "so its licence is unchecked"
        )
    ]


def test_a_row_with_no_licence_cell_is_a_finding() -> None:
    """A row of a table with no third column states no licence; its distribution is not asked."""
    guide = _guide([Prose("| pyyaml | `[yaml]` |")], header=_TWO_COLUMNS)
    assert licence_findings(guide, _installed({})) == [
        Prose(f"{BUILDING_GUIDE}:{_FIRST_ROW}: the row for pyyaml states no licence")
    ]


def test_an_empty_licence_cell_states_no_licence() -> None:
    """A row whose licence cell is empty states no licence, whatever the metadata records."""
    guide = _guide([Prose("| pyyaml | `[yaml]` | |")])
    assert licence_findings(guide, _installed({DistributionName("pyyaml"): Prose("")})) == [
        Prose(f"{BUILDING_GUIDE}:{_FIRST_ROW}: the row for pyyaml states no licence")
    ]


def test_the_findings_follow_the_rows_in_order() -> None:
    """Each row's finding names its own line, in the order the rows are written."""
    guide = _guide([Prose("| zlib-wrapper | `[z]` | MIT |"), Prose("| attrs | `[a]` | MIT |")])
    assert licence_findings(guide, _installed({DistributionName("attrs"): Prose("BSD")})) == [
        Prose(
            f"{BUILDING_GUIDE}:{_FIRST_ROW}: zlib-wrapper is not installed, "
            + "so its licence is unchecked"
        ),
        Prose(
            f"{BUILDING_GUIDE}:{_FIRST_ROW + 1}: the ledger says attrs is MIT, "
            + "its metadata records 'BSD'"
        ),
    ]


def test_a_guide_without_the_python_section_is_a_finding() -> None:
    """A guide lacking the section is one finding naming the section."""
    guide = Prose("# Building\n\n### Runtime, Rust layer\n\n" + _HEADER + "| serde | - | MIT |\n")
    assert licence_findings(guide, _installed({})) == [
        Prose(f"{BUILDING_GUIDE}: has no {PYTHON_LAYER} section")
    ]


def test_a_table_past_the_python_section_is_not_read() -> None:
    """Only the rows the Python section opens are held, not a table under the next heading."""
    guide = _guide(
        [Prose("| pyyaml | `[yaml]` | MIT |")],
        after=Prose("\n" + _HEADER + "| not-installed | - | MIT |\n"),
    )
    assert licence_findings(guide, _installed({DistributionName("pyyaml"): Prose("MIT")})) == (
        list[Prose]()
    )


def test_emphasis_in_the_cells_reads_as_the_rendered_text() -> None:
    """``**python-can**`` and ``**LGPL-3.0-only**`` are read as a reader sees them."""
    guide = _guide([Prose("| **python-can** | `[can]` | **LGPL-3.0-only** |")])
    installed = _installed({DistributionName("python-can"): Prose("LGPL-3.0-only")})
    assert licence_findings(guide, installed) == list[Prose]()


def test_a_code_span_in_the_cells_reads_as_its_content() -> None:
    """A distribution and a licence in code spans are read without their backticks."""
    guide = _guide([Prose("| `pyyaml` | `[yaml]` | `MIT` |")])
    assert licence_findings(guide, _installed({DistributionName("pyyaml"): Prose("MIT")})) == (
        list[Prose]()
    )


@pytest.mark.parametrize("name", [_PYTEST, DistributionName("openpyxl")])
def test_installed_licence_is_what_the_metadata_records(name: DistributionName) -> None:
    """A distribution this venv installs answers the licence ``importlib.metadata`` reports."""
    assert installed_licence(name) == _recorded(name)


def test_installed_licence_of_a_name_no_distribution_has_is_none() -> None:
    """A name no installed distribution carries answers None."""
    assert installed_licence(_ABSENT) is None


def test_installed_licence_prefers_the_licence_expression(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A distribution recording both fields answers its License-Expression."""
    name = DistributionName("aletheia-planted-both")
    _plant_distribution(tmp_path, name, Prose("License-Expression: BSD-2-Clause\nLicense: MIT\n"))
    monkeypatch.setattr(sys, "path", [tmp_path.as_posix(), *sys.path])
    assert installed_licence(name) == Prose("BSD-2-Clause")


def test_installed_licence_falls_back_to_the_license_field(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A distribution recording no License-Expression answers its License."""
    name = DistributionName("aletheia-planted-license")
    _plant_distribution(tmp_path, name, Prose("License: Apache-2.0\n"))
    monkeypatch.setattr(sys, "path", [tmp_path.as_posix(), *sys.path])
    assert installed_licence(name) == Prose("Apache-2.0")


def test_the_arm_holds_the_guide_to_the_installed_distributions(tmp_path: Path) -> None:
    """A planted guide naming pytest with the licence its metadata records passes."""
    row = Prose(f"| pytest | `[dev]` | {_recorded(_PYTEST)} |")
    root = plant(tmp_path, {BUILDING_GUIDE: _guide([row])})
    assert run_planted(findings, root) == list[Prose]()


def test_the_arm_reports_a_licence_the_installed_metadata_does_not_record(tmp_path: Path) -> None:
    """A planted guide giving pytest a licence it does not record is a finding from its metadata."""
    root = plant(tmp_path, {BUILDING_GUIDE: _guide([Prose("| pytest | `[dev]` | GPL-3.0-only |")])})
    assert run_planted(findings, root) == [
        Prose(
            f"{BUILDING_GUIDE}:{_FIRST_ROW}: the ledger says pytest is GPL-3.0-only, "
            + f"its metadata records {_recorded(_PYTEST)!r}"
        )
    ]


def test_an_untracked_guide_is_a_finding(tmp_path: Path) -> None:
    """A guide on disk that git does not track leaves the licences unchecked, and says so."""
    root = plant(tmp_path, {BUILDING_GUIDE: _guide([Prose("| pytest | `[dev]` | MIT |")])})
    assert run_planted(findings, root, untracked=[BUILDING_GUIDE]) == [
        Prose(f"{BUILDING_GUIDE}: not tracked, so its Python licences are unchecked")
    ]


def test_a_tracked_guide_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A tracked guide that cannot be read is named by the gate's read and by the arm."""
    root = plant(tmp_path, {RelPath("README.md"): Prose("# Readme\n")})
    assert run_planted(findings, root, absent=[BUILDING_GUIDE]) == [
        Prose(f"{BUILDING_GUIDE}: could not be read, so what it says is unchecked"),
        Prose(f"{BUILDING_GUIDE}: could not be read, so its Python licences are unchecked"),
    ]
