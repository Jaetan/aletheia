# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the ledger of kills no test observes by behaviour.

The C++ baseline records every mutant that only the standard library's own
check or a bare signal ended, by mutator, file, source-line text, route and
the invariant the check refused.  Three layers hold it: the rows are built
from the sweep's endings, the drift gate refuses a row the record does not
name and reports one the sweep no longer produces, and the always-on static
gate refuses a row whose line the tree no longer holds.
"""

from __future__ import annotations

from typing import cast

import pytest
import yaml

from tools import mutation_run
from tools.check_mutation_setup import ledger_rows_still_name_their_line
from tools.mutation_cpp import unobserved_kill_rows
from tools.mutation_report import (
    SPEC_PATH,
    Baseline,
    BindingSpec,
    DriftEntry,
    MutationReport,
    UnobservedKey,
    UnobservedRow,
    unobserved_ledger_to_rows,
    unobserved_rows_to_ledger,
)
from tools.mutation_routes import Ending

_GUARD = "cxx_replace_scalar_call:/t/cpp/src/excel.cpp:214:12:214:14:4aafce37.0"
_CLONE = "cxx_replace_scalar_call:/t/cpp/src/excel.cpp:214:12:214:14:4aafce37.1"
_SIGNAL = "cxx_ne_to_eq:/t/cpp/src/dbc.cpp:71:15:71:17:47616a88.0"
_SEEN = "cxx_add_to_sub:/t/cpp/src/client.cpp:350:54:350:55:5eb68e41.0"
_PAST_THE_END = "attempt to dereference a past-the-end iterator."

_ROW: UnobservedRow = {
    "mutator": "cxx_replace_scalar_call",
    "file": "cpp/src/excel.cpp",
    "text": "if (it == cells.end())",
    "route": "check",
    "refused": _PAST_THE_END,
    "count": 1,
}


def _read_line(file: str, line: int) -> str:
    """Stand in for the repository's source, one line per site the tests use."""
    return {
        ("cpp/src/excel.cpp", 214): "    if (it == cells.end())",
        ("cpp/src/dbc.cpp", 71): "        m != nullptr && seen.insert(m->multiplexor).second) {",
        ("cpp/src/client.cpp", 350): "    auto const slice = buf.subspan(off + bound);",
    }[(file, line)]


def test_a_mutant_a_test_observed_in_any_lane_is_not_a_row() -> None:
    """The route is attributed across the lanes first, and only a check or a fault is recorded."""
    lanes = [
        {_GUARD: Ending("check", _PAST_THE_END), _SEEN: Ending("check", "__count <= size()")},
        {_GUARD: Ending("check", _PAST_THE_END), _SEEN: Ending("test", "")},
    ]
    rows = unobserved_kill_rows(lanes, _read_line)
    assert list(rows) == [
        (
            "cxx_replace_scalar_call",
            "cpp/src/excel.cpp",
            "if (it == cells.end())",
            "check",
            _PAST_THE_END,
        )
    ]


def test_the_instantiations_of_one_template_are_one_row_with_their_count() -> None:
    """Mull names each clone of a template's mutant apart; they share a line and a claim."""
    lanes = [{_GUARD: Ending("check", _PAST_THE_END), _CLONE: Ending("check", _PAST_THE_END)}]
    assert list(unobserved_kill_rows(lanes, _read_line).values()) == [2]


def test_a_row_carries_the_route_and_the_refusal_apart() -> None:
    """A signal records no refusal, and a check records the invariant it reported."""
    lanes = [{_GUARD: Ending("check", _PAST_THE_END), _SIGNAL: Ending("fault", "")}]
    rows = unobserved_kill_rows(lanes, _read_line)
    assert {(key[0], key[3], key[4]) for key in rows} == {
        ("cxx_replace_scalar_call", "check", _PAST_THE_END),
        ("cxx_ne_to_eq", "fault", ""),
    }


def test_a_ledger_round_trips_through_its_rows() -> None:
    """What the lane writes is what the record is read back into, field for field."""
    rows = unobserved_ledger_to_rows([_ROW])
    assert unobserved_rows_to_ledger(rows) == [_ROW]


def _bindings(ledger: list[UnobservedRow] | None) -> dict[str, BindingSpec]:
    baseline: Baseline = {"survivors": 1}
    if ledger is not None:
        baseline["unobserved_ledger"] = ledger
    return {"cpp": {"tool": "mull", "baseline": baseline}}


def _drift(rows: dict[UnobservedKey, int] | None, ledger: list[UnobservedRow] | None) -> DriftEntry:
    return mutation_run.drift_for(
        MutationReport("cpp", "mull", 10, 0, ""), _bindings(ledger), None, rows
    )


def test_a_kill_the_record_does_not_name_fails_the_lane() -> None:
    """A new line whose mutation runs into undefined behaviour unobserved is a regression."""
    entry = _drift(unobserved_ledger_to_rows([_ROW]), [])
    assert entry["status"] == "regression"
    assert entry.get("unrecorded_unobserved_kills") == [_ROW]


def test_a_row_the_sweep_no_longer_produces_is_reported_and_does_not_fail() -> None:
    """A test that learned to observe a kill is an improvement; the record is lowered by it."""
    entry = _drift({}, [_ROW])
    assert entry["status"] == "ok"
    assert entry.get("stale_unobserved_ledger") == [_ROW]
    assert "unrecorded_unobserved_kills" not in entry


def test_a_count_that_grew_on_a_recorded_line_fails_the_lane() -> None:
    """The count is part of the claim: a second mutant of that line is a second gap."""
    grown = dict(unobserved_ledger_to_rows([_ROW]))
    for key in grown:
        grown[key] = 2
    entry = _drift(grown, [_ROW])
    assert entry["status"] == "regression"
    assert entry.get("unrecorded_unobserved_kills") == [{**_ROW, "count": 1}]


def test_a_record_without_the_ledger_judges_nothing() -> None:
    """The ledger is opt-in per binding, as the survivors' is."""
    entry = _drift(unobserved_ledger_to_rows([_ROW]), None)
    assert entry["status"] == "ok"
    assert "unrecorded_unobserved_kills" not in entry
    assert "stale_unobserved_ledger" not in entry


def _spec(row: UnobservedRow, ledger: str = "unobserved_ledger") -> dict[str, object]:
    return {"cpp": {"baseline": {ledger: [row]}}}


def test_a_row_whose_line_the_tree_still_holds_passes_the_static_gate() -> None:
    """The recorded text is sought in the recorded file, stripped, anywhere in it."""
    row: UnobservedRow = {**_ROW, "file": "cpp/src/excel.cpp", "text": "if (it == cells.end())"}
    assert not ledger_rows_still_name_their_line(_spec(row))


def test_a_reworded_line_fails_the_static_gate() -> None:
    """The one drift nothing else notices: the row goes on claiming a line that is gone."""
    row: UnobservedRow = {**_ROW, "text": "if (it == cells.cend())"}
    failures = ledger_rows_still_name_their_line(_spec(row))
    assert len(failures) == 1
    assert "holds no line reading" in failures[0]


def test_a_renamed_file_fails_the_static_gate() -> None:
    """A row against a source the tree no longer has records nothing about the tree."""
    row: UnobservedRow = {**_ROW, "file": "cpp/src/excel_reader.cpp"}
    failures = ledger_rows_still_name_their_line(_spec(row))
    assert len(failures) == 1
    assert "is not a file of the tree" in failures[0]


@pytest.mark.parametrize("ledger", ["survivors_ledger", "unobserved_ledger"])
def test_both_ledgers_are_held_to_their_lines(ledger: str) -> None:
    """The survivors' rows carry the same exposure and are checked the same way."""
    row: UnobservedRow = {**_ROW, "text": "a line no source of this tree has"}
    assert len(ledger_rows_still_name_their_line(_spec(row, ledger))) == 1


def test_the_record_s_own_rows_name_lines_the_tree_holds() -> None:
    """The gate runs over the record itself, so a stale row cannot ship unnoticed."""
    record = cast("dict[str, object]", yaml.safe_load(SPEC_PATH.read_text(encoding="utf-8")))
    spec = cast("dict[str, object]", record["bindings"])
    assert not ledger_rows_still_name_their_line(spec)
