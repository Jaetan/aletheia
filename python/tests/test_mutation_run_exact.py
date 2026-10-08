# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the drift gate's exactness, the arms no single ledger owns.

The record is a measurement of the tree, so a run must agree with it both
ways: a run worse than the record is a regression, and a run better than the
record is a stale record, which fails too, the change that improved the tree
lowering the record in the same commit.  Held here: the survivor count, the
mutants judged, every mutant the tool made, the C++ census by kill route, and
a mutant in every file the hot path names, together with the order the two
verdicts outrank each other in.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from tools import mutation_run
from tools._common import RelPath
from tools.mutation_report import KillRoute, MutantCount, MutationReport, Observed

if TYPE_CHECKING:
    from tools.mutation_report import Baseline, BindingSpec, DriftEntry, DriftStatus, RouteCensus

_ROUTES: RouteCensus = {
    KillRoute("test"): MutantCount(7),
    KillRoute("fault"): MutantCount(1),
    KillRoute("timeout"): MutantCount(0),
    KillRoute("survived"): MutantCount(2),
}
_A = RelPath("cpp/src/a.cpp")
_RECORDED = MutantCount(2)
_B = RelPath("cpp/src/b.cpp")


def _binding(baseline: Baseline, hot_path: list[RelPath] | None = None) -> BindingSpec:
    binding: BindingSpec = {"tool": "mull", "baseline": {"survivors": _RECORDED, **baseline}}
    if hot_path is not None:
        binding["hot_path"] = hot_path
    return binding


def _drift(
    binding: BindingSpec,
    *,
    survived: MutantCount = _RECORDED,
    generated: MutantCount | None = None,
    routes: RouteCensus | None = None,
    files: frozenset[RelPath] | None = None,
) -> DriftEntry:
    observed = Observed(timeouts=0, generated=generated, routes=routes, mutated_files=files)
    rep = MutationReport("cpp", "mull", 8, survived, "", observed=observed)
    return mutation_run.drift_for(rep, {"cpp": binding})


def test_a_run_that_matches_the_record_passes() -> None:
    """Every count equal and every route equal is the one passing run."""
    baseline: Baseline = {
        "total_mutants": 10,
        "generated": MutantCount(12),
        "kill_routes": _ROUTES,
    }
    entry = _drift(
        _binding(baseline, [_A]), generated=MutantCount(12), routes=_ROUTES, files=frozenset({_A})
    )
    assert entry["status"] == "ok"


@pytest.mark.parametrize(
    ("survived", "status"), [(MutantCount(3), "regression"), (MutantCount(1), "stale")]
)
def test_the_survivor_count_is_held_both_ways(survived: MutantCount, status: DriftStatus) -> None:
    """One more survivor is a regression; one fewer is a record the run has outgrown."""
    entry = _drift(_binding({}), survived=survived)
    assert entry["status"] == status
    assert entry.get("delta") == survived - _RECORDED


@pytest.mark.parametrize("recorded", [MutantCount(9), MutantCount(11)])
def test_a_total_off_the_record_is_a_stale_record(recorded: MutantCount) -> None:
    """The mutants judged are a property of the source and the tool, held exactly."""
    entry = _drift(_binding({"total_mutants": recorded}))
    assert entry["status"] == "stale"
    assert entry.get("observed_total_mutants") == 10
    assert entry.get("baseline_total_mutants") == recorded


@pytest.mark.parametrize("observed", [MutantCount(11), MutantCount(13), None])
def test_a_generated_count_off_the_record_is_a_stale_record(observed: MutantCount | None) -> None:
    """Every mutant the tool made, a bucket no other count reads included, is held exactly.

    A run that reports no such count, where the record holds one, is off the
    record too: a count compared against nothing holds nothing.
    """
    entry = _drift(_binding({"generated": MutantCount(12)}), generated=observed)
    assert entry["status"] == "stale"
    assert entry.get("baseline_generated") == 12
    assert entry.get("observed_generated") == observed


def test_a_record_without_a_generated_count_holds_none() -> None:
    """The tools whose record carries no such count are not held to one."""
    assert _drift(_binding({}), generated=MutantCount(99))["status"] == "ok"


def test_a_kill_that_moved_route_is_a_stale_record() -> None:
    """A kill moving between a test and a signal changes what the census says, either way."""
    moved: RouteCensus = {
        **_ROUTES,
        KillRoute("test"): MutantCount(6),
        KillRoute("fault"): MutantCount(2),
    }
    entry = _drift(_binding({"kill_routes": _ROUTES}), routes=moved)
    assert entry["status"] == "stale"
    assert entry.get("observed_kill_routes") == moved
    assert entry.get("baseline_kill_routes") == _ROUTES


def test_a_route_one_side_does_not_name_counts_as_zero() -> None:
    """A route the run took and the record has no row for is off the record; a zero is not."""
    leaked: RouteCensus = {**_ROUTES, KillRoute("leak"): MutantCount(1)}
    assert _drift(_binding({"kill_routes": _ROUTES}), routes=leaked)["status"] == "stale"
    absent = {route: count for route, count in _ROUTES.items() if route != "timeout"}
    assert _drift(_binding({"kill_routes": _ROUTES}), routes=absent)["status"] == "ok"


def test_a_census_is_held_only_where_the_record_and_the_run_carry_one() -> None:
    """A binding whose tool has no routes, or a record without them, judges none."""
    assert _drift(_binding({}), routes=_ROUTES)["status"] == "ok"
    assert _drift(_binding({"kill_routes": _ROUTES}))["status"] == "ok"


def test_a_hot_path_file_without_a_mutant_is_a_regression() -> None:
    """A listed file no mutant reaches is surface the lane does not have."""
    entry = _drift(_binding({}, [_A, _B]), files=frozenset({_A}))
    assert entry["status"] == "regression"
    assert entry.get("hot_path_without_mutants") == [_B]
    assert _drift(_binding({}, [_A]))["status"] == "ok"


def test_a_regression_outranks_a_stale_record() -> None:
    """A run worse somewhere reads as worse, whatever else it improved, in either order."""
    # Eight killed and three survived judge 11 mutants, off the recorded 12.
    entry = _drift(_binding({"total_mutants": 12}), survived=MutantCount(3))
    assert entry["status"] == "regression"
    assert entry.get("baseline_total_mutants") == 12
    entry = _drift(_binding({"total_mutants": 11}, [_A]), files=frozenset())
    assert entry["status"] == "regression"
    assert entry.get("baseline_total_mutants") == 11
