# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The drift lines the C++ merge prints beside its verdict (``mutation_cpp_runs.weight_drift``).

Each tree's slices are cut on the suite runs its files' mutants cost when the
weights were last recorded, and the surface grows without anything refusing,
so the cut goes stale quietly.  The lines are the one instrument the scheduled
review of those weights reads, and nothing in the lane parses them, so their
text is held here: per tree, what the heaviest slice would cost today, against
an equal share, if the partition were cut on the recorded figures and run over
the sweep just measured.  The share keeps a decimal, because a total that does
not divide by the slice count otherwise prints a heaviest slice "over" a share
it equals.  Five arms: weights recorded, none recorded, a file costing runs
the record does not count, and each tree cut on its own record and read
against its own sweep.
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

    from tools.mutation_cpp_legs import CppTree, CppTreeName
    from tools.mutation_cpp_slices import TreeRuns

# Four files, three of them weighed, cut into three slices: the two heaviest
# alone, the lightest beside the one the record does not name.
_A, _B, _C, _D = (RelPath(f"cpp/src/{name}.cpp") for name in ("a", "b", "c", "d"))
_DOMAIN = [_A, _B, _C, _D]
_RECORDED: TreeRuns = {_A: SuiteRuns(4.0), _B: SuiteRuns(4.0), _C: SuiteRuns(3.0)}

# What the merge says of the trees a test records nothing for.
_NO_PLAIN = "weights (plain): none recorded, so its slices are cut on nothing\n"
_NO_ADDRESS = "weights (address): none recorded, so its slices are cut on nothing\n"


def _cut_on(monkeypatch: pytest.MonkeyPatch, recorded: dict[CppTreeName, TreeRuns]) -> None:
    """Cut each tree's partition on the weights given it, over the fixture's domain."""

    def domain(_repo_root: Path, _config_path: Path) -> list[RelPath]:
        return list(_DOMAIN)

    def runs(tree: CppTree) -> TreeRuns:
        return dict(recorded.get(tree.key, {}))

    monkeypatch.setattr(mutation_cpp_runs, "recorded_runs", runs)
    monkeypatch.setattr(mutation_cpp_runs, "slice_domain", domain)


def test_fresh_weights_read_the_share_to_a_decimal(monkeypatch: pytest.MonkeyPatch) -> None:
    """A sweep that is its own record reads its heaviest slice against the exact share."""
    _cut_on(monkeypatch, {"leak": _RECORDED})
    assert weight_drift({"leak": _RECORDED}) == (
        "weights (leak): the heaviest slice costs 4.0 of 11.0 suite runs,"
        + " 9.1% over an equal share of 3.7\n"
        + _NO_PLAIN
        + _NO_ADDRESS
    )


def test_a_file_that_grew_moves_the_figure(monkeypatch: pytest.MonkeyPatch) -> None:
    """Runs added to one recorded file land in its slice, and the line says by how much."""
    _cut_on(monkeypatch, {"leak": _RECORDED})
    grown = {**_RECORDED, _B: SuiteRuns(6.0)}
    assert weight_drift({"leak": grown}) == (
        "weights (leak): the heaviest slice costs 6.0 of 13.0 suite runs,"
        + " 38.5% over an equal share of 4.3\n"
        + _NO_PLAIN
        + _NO_ADDRESS
    )


def test_no_weights_recorded_is_said(monkeypatch: pytest.MonkeyPatch) -> None:
    """A tree with no figures is cut on nothing, and its line says so, not a figure."""
    _cut_on(monkeypatch, {})
    assert weight_drift({"leak": _RECORDED}) == (
        "weights (leak): none recorded, so its slices are cut on nothing\n"
        + _NO_PLAIN
        + _NO_ADDRESS
    )


def test_a_file_the_record_does_not_count_is_named(monkeypatch: pytest.MonkeyPatch) -> None:
    """A file weighing nothing still lands in a slice; its runs count there and it is named."""
    _cut_on(monkeypatch, {"leak": _RECORDED})
    added = {**_RECORDED, _D: SuiteRuns(2.0)}
    assert weight_drift({"leak": added}) == (
        "weights (leak): the heaviest slice costs 5.0 of 13.0 suite runs,"
        + " 15.4% over an equal share of 4.3\n"
        + "weights (leak): 1 file(s) cost runs the record does not count: cpp/src/d.cpp\n"
        + _NO_PLAIN
        + _NO_ADDRESS
    )


# A record that weighs c and d heavy, so its cut puts a and b in one slice.
_C_AND_D_HEAVY: TreeRuns = {
    _C: SuiteRuns(9.0),
    _D: SuiteRuns(9.0),
    _A: SuiteRuns(1.0),
    _B: SuiteRuns(1.0),
}


def test_each_tree_is_cut_on_its_own_record(monkeypatch: pytest.MonkeyPatch) -> None:
    """One sweep read under two trees' records: each tree's line is its own partition's.

    The figures that are even under the leak tree's cut are lopsided under
    the plain tree's, which puts a and b in one slice.
    """
    _cut_on(monkeypatch, {"leak": _RECORDED, "plain": _C_AND_D_HEAVY})
    assert weight_drift({"leak": _RECORDED, "plain": _RECORDED}) == (
        "weights (leak): the heaviest slice costs 4.0 of 11.0 suite runs,"
        + " 9.1% over an equal share of 3.7\n"
        + "weights (plain): the heaviest slice costs 8.0 of 11.0 suite runs,"
        + " 118.2% over an equal share of 3.7\n"
        + _NO_ADDRESS
    )


def test_each_tree_is_read_against_its_own_sweep(monkeypatch: pytest.MonkeyPatch) -> None:
    """A tree's line sums that tree's measured runs, not another tree's."""
    _cut_on(monkeypatch, {"leak": _RECORDED, "plain": _C_AND_D_HEAVY})
    plain = {_A: SuiteRuns(2.0), _B: SuiteRuns(2.0), _C: SuiteRuns(3.0)}
    assert weight_drift({"leak": _RECORDED, "plain": plain}) == (
        "weights (leak): the heaviest slice costs 4.0 of 11.0 suite runs,"
        + " 9.1% over an equal share of 3.7\n"
        + "weights (plain): the heaviest slice costs 4.0 of 7.0 suite runs,"
        + " 71.4% over an equal share of 2.3\n"
        + _NO_ADDRESS
    )
