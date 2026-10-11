# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The drift lines the C++ merge prints beside its verdict (``mutation_cpp_runs.weight_drift``).

The slices are cut on the suite runs the files' mutants cost when the weights
were last recorded, and the surface grows without anything refusing, so the
cut goes stale quietly.  The lines are the one instrument the scheduled review
of those weights reads, and nothing in the lane parses them, so their text is
held here: what the heaviest slice costs under the recorded cut, run over the
sweep just measured, against what it costs under the partition cut on that
sweep's own figures.  Five arms: a sweep that is its own record, a file that
grew where no cut could place it better, none recorded, a file costing runs
the record does not count, and a record whose cut the sweep's figures no
longer fit.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import mutation_cpp_runs
from tools._common import RelPath
from tools.mutation_cpp_runs import weight_drift
from tools.mutation_cpp_slices import SuiteRuns

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

    from tools.mutation_cpp_slices import FileRuns

# Four files, three of them weighed, cut into three slices: the two heaviest
# alone, the lightest beside the one the record does not name.
_A, _B, _C, _D = (RelPath(f"cpp/src/{name}.cpp") for name in ("a", "b", "c", "d"))
_DOMAIN = [_A, _B, _C, _D]
_RECORDED: FileRuns = {_A: SuiteRuns(4.0), _B: SuiteRuns(4.0), _C: SuiteRuns(3.0)}


def _cut_on(monkeypatch: pytest.MonkeyPatch, recorded: FileRuns) -> None:
    """Cut the partition on the weights given, over the fixture's domain."""

    def domain(_repo_root: Path, _config_path: Path) -> list[RelPath]:
        return list(_DOMAIN)

    monkeypatch.setattr(mutation_cpp_runs, "recorded_runs", lambda: dict(recorded))
    monkeypatch.setattr(mutation_cpp_runs, "slice_domain", domain)


def test_a_sweep_that_is_its_own_record_reads_no_drift(monkeypatch: pytest.MonkeyPatch) -> None:
    """Cut on the record and cut on its own figures are one cut, and the line says 0.0 over."""
    _cut_on(monkeypatch, _RECORDED)
    assert weight_drift(_RECORDED) == (
        "weights: the heaviest slice costs 4.0 of 11.0 suite runs under the recorded cut,"
        + " 4.0 under a cut on this run's own figures, 0.0% over\n"
    )


def test_a_file_that_grew_alone_in_its_slice_is_no_drift(monkeypatch: pytest.MonkeyPatch) -> None:
    """A file that outgrew its slice is the heaviest slice under any cut, so the record still fits.

    An equal share would read it as drift; the cut on the sweep's own figures
    carries the file alone too, and no cut goes below it.
    """
    _cut_on(monkeypatch, _RECORDED)
    grown = {**_RECORDED, _C: SuiteRuns(6.0)}
    assert weight_drift(grown) == (
        "weights: the heaviest slice costs 6.0 of 14.0 suite runs under the recorded cut,"
        + " 6.0 under a cut on this run's own figures, 0.0% over\n"
    )


def test_no_weights_recorded_is_said(monkeypatch: pytest.MonkeyPatch) -> None:
    """A record with no figures is cut on nothing, and the line says so, not a figure."""
    _cut_on(monkeypatch, {})
    assert weight_drift(_RECORDED) == "weights: none recorded, so the slices are cut on nothing\n"


def test_a_file_the_record_does_not_count_is_named(monkeypatch: pytest.MonkeyPatch) -> None:
    """A file weighing nothing lands beside the lightest; its runs count there and it is named.

    The record puts d beside c for 8.0; its own figures would give d a slice
    of its own and put b beside c for 7.0.
    """
    _cut_on(monkeypatch, _RECORDED)
    added = {**_RECORDED, _D: SuiteRuns(5.0)}
    assert weight_drift(added) == (
        "weights: the heaviest slice costs 8.0 of 16.0 suite runs under the recorded cut,"
        + " 7.0 under a cut on this run's own figures, 14.3% over\n"
        + "weights: 1 file(s) cost runs the record does not count: cpp/src/d.cpp\n"
    )


# A record that weighs c and d heavy, so its cut puts a and b in one slice.
_C_AND_D_HEAVY: FileRuns = {
    _C: SuiteRuns(9.0),
    _D: SuiteRuns(9.0),
    _A: SuiteRuns(1.0),
    _B: SuiteRuns(1.0),
}


def test_the_partition_is_cut_on_the_record_and_read_against_the_sweep(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The line is the recorded cut costed with the measured runs, against the sweep's own cut.

    The figures that cut even on their own are lopsided under a record that
    puts a and b in one slice: twice the heaviest slice their own cut gives.
    """
    _cut_on(monkeypatch, _C_AND_D_HEAVY)
    assert weight_drift(_RECORDED) == (
        "weights: the heaviest slice costs 8.0 of 11.0 suite runs under the recorded cut,"
        + " 4.0 under a cut on this run's own figures, 100.0% over\n"
    )
