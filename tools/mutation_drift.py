# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The drift gate: one binding's mutation run held to its record, both ways.

``drift_for`` holds a run's survivors, its timeouts and crashes, its counts,
its C++ kill routes, the files it mutated and its ledgers to the binding's
block in ``docs/MUTATION_BENCH.yaml``; ``tools/mutation_run.py`` calls it for
each binding it ran.
"""

from __future__ import annotations

import collections
from typing import TYPE_CHECKING, Literal

from tools.mutation_cpp_legs import is_cpp_leg
from tools.mutation_go import Binding, is_go_shard
from tools.mutation_report import (
    Baseline,
    BindingSpec,
    DriftEntry,
    LedgerRow,
    MutantCount,
    MutationReport,
    RouteCensus,
    SurvivorKey,
    UnobservedKey,
    unobserved_ledger_to_rows,
    unobserved_rows_to_ledger,
)
from tools.mutation_rust import RustBinding, is_rust_job

if TYPE_CHECKING:
    from tools._common import RelPath


def rows_to_ledger(rows: dict[SurvivorKey, int]) -> list[LedgerRow]:
    """Render survivor rows in the ledger's row shape, sorted by identity."""
    return [
        {"mutator": mutator, "file": file, "text": text, "count": count}
        for (mutator, file, text), count in sorted(rows.items())
    ]


def ledger_to_rows(ledger: list[LedgerRow]) -> dict[SurvivorKey, int]:
    """Read a ledger back into survivor rows keyed by identity."""
    rows: dict[SurvivorKey, int] = collections.Counter()
    for row in ledger:
        rows[(row["mutator"], row["file"], row["text"])] += row["count"]
    return rows


def _ungated(rep: MutationReport) -> DriftEntry | None:
    """Return the verdict no baseline enters into, or None where one does.

    A C++ leg is one slice of the tree: its count is recorded and the merge
    over the slices is what is gated.
    A Go shard is one part of the package, and a Rust job one part of the
    crate's sweep, each judged with the others by the merge in the same way.
    """
    if rep.error:
        return {"status": "error", "error": rep.error}
    if (
        is_cpp_leg(rep.binding)
        or is_go_shard(Binding(rep.binding))
        or is_rust_job(RustBinding(rep.binding))
    ):
        return {"status": "leg", "observed_survivors": rep.survived}
    return None


def _fail(entry: DriftEntry, status: Literal["regression", "stale"]) -> None:
    """Mark the run off its record, a regression outranking a stale record."""
    if entry["status"] != "regression":
        entry["status"] = status


def drift_for(
    rep: MutationReport,
    bindings: dict[str, BindingSpec],
    survivor_rows: dict[SurvivorKey, int] | None = None,
    unobserved_rows: dict[UnobservedKey, int] | None = None,
    not_covered_rows: dict[SurvivorKey, int] | None = None,
) -> DriftEntry:
    """Compute one binding's drift verdict against its YAML baseline.

    The record is a measurement of the tree, held exactly both ways: a run
    worse than the record is a regression, and a run better than it is a
    stale record, which fails too, so the change that improves the tree
    lowers the record in the same commit and the record never names a figure
    no run gives.  ``survivor_rows`` are the run's survivors by identity where
    the tool reports them, held to a ``survivors_ledger``.  ``unobserved_rows``
    are the kills no test observes by behaviour, held to an
    ``unobserved_ledger``: a line whose mutation runs into an operation the
    language does not define, with no test saying so, is a gap somebody has
    to look at rather than a number to carry.  ``not_covered_rows`` are the
    mutants on lines no test executes, held to a ``not_covered`` count and a
    ``not_covered_ledger``.  The report's own counts are held too: the
    mutants judged, every mutant the tool made, the C++ census by kill route,
    and the files it made a mutant in, which must hold every file of the
    binding's ``hot_path``.  Where the tool makes no such observation it is
    ``None`` and holds nothing.
    """
    spec = bindings.get(rep.binding, {})
    spec_baseline = spec.get("baseline", {})
    early = _ungated(rep) or _over_ceiling(rep, spec_baseline)
    if early is not None:
        return early
    baseline = spec_baseline.get("survivors")
    if baseline is None:
        return {"status": "first_run", "observed_survivors": rep.survived}
    entry: DriftEntry = {
        "status": "ok",
        "observed_survivors": rep.survived,
        "baseline_survivors": baseline,
    }
    if rep.survived != baseline:
        entry["delta"] = rep.survived - baseline
        _fail(entry, "regression" if rep.survived > baseline else "stale")
    _judge_counts(entry, spec_baseline, rep)
    _judge_routes(entry, spec_baseline, rep.observed.routes)
    _judge_hot_path(entry, spec.get("hot_path", []), rep.observed.mutated_files)
    _judge_not_covered(entry, spec_baseline, not_covered_rows)
    _judge_unobserved(entry, spec_baseline, unobserved_rows)
    # A survivor the ledger does not name is a regression even at an unchanged
    # count; a recorded row the run no longer leaves alive is a stale record,
    # deleted by the change that kills or removes its mutant.
    ledger = spec_baseline.get("survivors_ledger")
    if ledger is None or survivor_rows is None:
        return entry
    recorded = collections.Counter(ledger_to_rows(ledger))
    observed = collections.Counter(survivor_rows)
    unrecorded = rows_to_ledger(dict(observed - recorded))
    stale = rows_to_ledger(dict(recorded - observed))
    if stale:
        entry["stale_ledger"] = stale
        _fail(entry, "stale")
    if unrecorded:
        entry["unrecorded_survivors"] = unrecorded
        _fail(entry, "regression")
    return entry


def _over_ceiling(rep: MutationReport, spec_baseline: Baseline) -> DriftEntry | None:
    """Refuse a run past the record's timeout or crash ceiling, whatever else it reports.

    A mutant that timed out is neither killed nor survived, so a sweep whose
    timeouts hide survivors reports fewer of them than the tree has, and the
    survivor count alone cannot tell it from a clean run: the ceiling is
    checked first.  A mutant whose process ended on a signal is a kill no test
    observed, held to its own ceiling and named.
    """
    ceiling = spec_baseline.get("timeout_ceiling")
    timeouts = rep.observed.timeouts
    if ceiling is not None and timeouts is not None and timeouts > ceiling:
        return {
            "status": "regression",
            "observed_survivors": rep.survived,
            "observed_timeouts": timeouts,
            "timeout_ceiling": ceiling,
        }
    crash_ceiling = spec_baseline.get("crash_ceiling")
    crashes = rep.observed.crashes
    if crash_ceiling is None or crashes is None or len(crashes) <= crash_ceiling:
        return None
    return {
        "status": "regression",
        "observed_survivors": rep.survived,
        "observed_crashes": list(crashes),
        "crash_ceiling": crash_ceiling,
    }


def _judge_counts(entry: DriftEntry, spec_baseline: Baseline, rep: MutationReport) -> None:
    """Hold the mutants the run judged, and every mutant the tool made, to the record.

    Both are the surface, a property of the source, its tests and the tool, so
    a count off the record either way is a record that no longer describes
    the tree.  A run that reports no generated count where the record holds
    one is off the record too: a count compared against nothing holds nothing.
    """
    recorded_total = spec_baseline.get("total_mutants")
    if recorded_total is not None:
        entry["observed_total_mutants"] = MutantCount(rep.total_mutants)
        entry["baseline_total_mutants"] = MutantCount(recorded_total)
        if rep.total_mutants != recorded_total:
            _fail(entry, "stale")
    recorded_generated = spec_baseline.get("generated")
    if recorded_generated is not None:
        entry["observed_generated"] = rep.observed.generated
        entry["baseline_generated"] = recorded_generated
        if rep.observed.generated != recorded_generated:
            _fail(entry, "stale")


def _judge_routes(entry: DriftEntry, spec_baseline: Baseline, routes: RouteCensus | None) -> None:
    """Hold the C++ census to the record route by route, a route one side lacks counting zero.

    A kill moving from a test to a check or a signal is a test that stopped
    observing it, which the unobserved ledger names; one moving the other way
    is a test that learned to.  Either changes what the census says, and
    either fails until the record follows.
    """
    recorded = spec_baseline.get("kill_routes")
    if recorded is None or routes is None:
        return
    if any(routes.get(r, 0) != recorded.get(r, 0) for r in routes.keys() | recorded.keys()):
        entry["observed_kill_routes"] = routes
        entry["baseline_kill_routes"] = recorded
        _fail(entry, "stale")


def _judge_hot_path(
    entry: DriftEntry, hot_path: list[RelPath], mutated_files: frozenset[RelPath] | None
) -> None:
    """Refuse a run with no mutant in a file the binding's hot path names.

    The list names the files the lane exists to mutate.  One no mutant
    reaches, because no suite the mutation build links reaches it or the
    tool drops its mutants, is surface the lane does not have.
    """
    if mutated_files is None:
        return
    missing = [path for path in hot_path if path not in mutated_files]
    if missing:
        entry["hot_path_without_mutants"] = missing
        _fail(entry, "regression")


def _judge_not_covered(
    entry: DriftEntry,
    spec_baseline: Baseline,
    not_covered_rows: dict[SurvivorKey, int] | None,
) -> None:
    """Hold the run's not-covered mutants to the record, by count and by row.

    The count is the rows' sum, one per mutant the tool named.  More of them
    than recorded is a line that lost its test, and so is a row the ledger
    does not name, at any count: a regression.  Fewer, or a recorded row the
    run no longer produces, is a line that gained a test, which lowers the
    record in the change that wrote the test.
    """
    recorded_count = spec_baseline.get("not_covered")
    if recorded_count is not None and not_covered_rows is not None:
        observed_count = sum(not_covered_rows.values())
        entry["observed_not_covered"] = observed_count
        entry["baseline_not_covered"] = recorded_count
        if observed_count != recorded_count:
            _fail(entry, "regression" if observed_count > recorded_count else "stale")
    ledger = spec_baseline.get("not_covered_ledger")
    if ledger is None or not_covered_rows is None:
        return
    recorded = collections.Counter(ledger_to_rows(ledger))
    observed = collections.Counter(not_covered_rows)
    stale = rows_to_ledger(dict(recorded - observed))
    unrecorded = rows_to_ledger(dict(observed - recorded))
    if stale:
        entry["stale_not_covered_ledger"] = stale
        _fail(entry, "stale")
    if unrecorded:
        entry["unrecorded_not_covered"] = unrecorded
        _fail(entry, "regression")


def _judge_unobserved(
    entry: DriftEntry,
    spec_baseline: Baseline,
    unobserved_rows: dict[UnobservedKey, int] | None,
) -> None:
    """Hold the run's unobserved kills to the recorded ledger, both ways.

    A row the record does not name is a regression, as an unrecorded survivor
    is.  A recorded row the run no longer produces is a stale record: a test
    that learned to observe a kill lowers the record in the change that
    taught it.
    """
    ledger = spec_baseline.get("unobserved_ledger")
    if ledger is None or unobserved_rows is None:
        return
    recorded = collections.Counter(unobserved_ledger_to_rows(ledger))
    observed = collections.Counter(unobserved_rows)
    stale = unobserved_rows_to_ledger(dict(recorded - observed))
    unrecorded = unobserved_rows_to_ledger(dict(observed - recorded))
    if stale:
        entry["stale_unobserved_ledger"] = stale
        _fail(entry, "stale")
    if unrecorded:
        entry["unrecorded_unobserved_kills"] = unrecorded
        _fail(entry, "regression")
