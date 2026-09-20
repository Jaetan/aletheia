# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_run``'s survivor ledger.

The C++ baseline records every survivor by mutator, file and source-line
text; the drift gate refuses a survivor the ledger does not name even when
the count is unchanged, and reports a ledger row that no longer survives
without failing, as it does a lower count.
"""

from __future__ import annotations

from tools import mutation_run
from tools.mutation_cpp import elements_survivor_rows
from tools.mutation_report import (
    Baseline,
    BindingSpec,
    DriftEntry,
    LedgerRow,
    MutationReport,
    SurvivorKey,
)
from tools.mutation_run import ledger_to_rows, rows_to_ledger

_ROW: LedgerRow = {
    "mutator": "cxx_replace_scalar_call",
    "file": "cpp/src/client.cpp",
    "text": "if (!diags_.empty())",
    "count": 1,
}


def _bindings(ledger: list[LedgerRow] | None) -> dict[str, BindingSpec]:
    baseline: Baseline = {"survivors": 1}
    if ledger is not None:
        baseline["survivors_ledger"] = ledger
    return {"cpp": {"tool": "mull", "baseline": baseline}}


def _drift(rows: dict[SurvivorKey, int] | None, ledger: list[LedgerRow] | None) -> DriftEntry:
    survived = 0 if rows is None else sum(rows.values())
    return mutation_run.drift_for(
        MutationReport("cpp", "mull", 10, survived, ""), _bindings(ledger), rows
    )


def test_elements_rows_count_survivors_by_identity() -> None:
    """Survivors are keyed by mutator, cpp-relative file and stripped line text."""
    report = {
        "files": {
            "/abs/cpp/src/a.cpp": {
                "mutants": [
                    {"status": "Survived", "mutatorName": "m", "location": {"start": {"line": 3}}},
                    {"status": "Survived", "mutatorName": "m", "location": {"start": {"line": 3}}},
                    {"status": "Killed", "mutatorName": "m", "location": {"start": {"line": 3}}},
                    {"status": "Survived", "mutatorName": "n", "location": {"start": {"line": 4}}},
                ]
            }
        }
    }
    lines = {3: "    x = y;   ", 4: "z"}
    rows = elements_survivor_rows(report, lambda _file, line: lines[line])
    assert rows == {("m", "cpp/src/a.cpp", "x = y;"): 2, ("n", "cpp/src/a.cpp", "z"): 1}


def test_ledger_round_trips_through_rows() -> None:
    """The ledger's row shape and the runner's rows carry the same information."""
    rows = {("m", "cpp/src/a.cpp", "x"): 2, ("n", "cpp/src/b.cpp", "y"): 1}
    assert ledger_to_rows(rows_to_ledger(rows)) == rows


def test_recorded_survivors_pass() -> None:
    """A run whose survivors are exactly the ledger's rows is ok."""
    entry = _drift(
        {("cxx_replace_scalar_call", "cpp/src/client.cpp", "if (!diags_.empty())"): 1}, [_ROW]
    )
    assert entry["status"] == "ok"
    assert "stale_ledger" not in entry


def test_a_traded_survivor_is_a_regression_at_equal_count() -> None:
    """A survivor the ledger does not name fails the lane, the count unchanged."""
    entry = _drift({("cxx_gt_to_ge", "cpp/src/client.cpp", "if (a > b)"): 1}, [_ROW])
    assert entry["status"] == "regression"
    assert entry.get("unrecorded_survivors") == [
        {"mutator": "cxx_gt_to_ge", "file": "cpp/src/client.cpp", "text": "if (a > b)", "count": 1}
    ]
    assert entry.get("stale_ledger") == [_ROW]


def test_a_vanished_survivor_is_stale_and_not_a_failure() -> None:
    """A ledger row that no longer survives is reported, as a lower count is allowed."""
    entry = _drift({}, [_ROW])
    assert entry["status"] == "ok"
    assert entry.get("stale_ledger") == [_ROW]


def test_without_a_ledger_the_count_alone_decides() -> None:
    """A baseline with no ledger gates on the count, as before."""
    entry = _drift({("cxx_gt_to_ge", "cpp/src/client.cpp", "if (a > b)"): 1}, None)
    assert entry["status"] == "ok"
