# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_mutation_setup``: each check refuses what it names, ``main`` runs all.

A check reading the tree is pointed at a planted one, the module's paths
monkeypatched to files the test writes; one reading the record alone is handed
a literal mapping; each one's diagnostics are compared whole.  The wiring test
stands every check in for one returning its own name, so a check ``main``
stops calling is a name missing from its output, and a check handed anything
but the record ``main`` read is a call the test refuses.  The lanes' checks,
invariants 6, 8 and 9, are held by ``test_check_mutation_setup_lanes.py`` and
``test_check_mutation_setup_cpp_lane.py``, the Python-test checks, invariants 2
and 3, by ``test_check_mutation_setup_python_tests.py``, the slice weights by
``test_check_mutation_slices.py``, and a ledger row naming a line the tree no
longer holds by ``test_mutation_unobserved_ledger.py``.
"""

from __future__ import annotations

import sys
from typing import TYPE_CHECKING, Final, Literal, NewType
from unittest.mock import Mock

import pytest
from _gate_exit import stderr_of_exit_2
from _planted_tree import plant

from tools import check_mutation_setup
from tools._common import RelPath
from tools.check_mutation_setup import BindingName

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

# A check of the gate as its module names it.
CheckName = NewType("CheckName", str)


# The record: one block per runner, each naming its tool and hot paths that exist.


def test_one_block_per_runner_passes() -> None:
    """A record with a block for each binding the runner sweeps, and none other, is clean."""
    assert not check_mutation_setup.every_runner_has_a_block(
        {"python": {}, "go": {}, "cpp": {}, "rust": {}}
    )


def test_a_runner_without_a_block_and_a_block_without_a_runner_are_named() -> None:
    """The Rust block renamed to a binding no runner has: one block missing, one unread."""
    assert check_mutation_setup.every_runner_has_a_block(
        {"python": {}, "go": {}, "cpp": {}, "haskell": {}}
    ) == [
        "[bindings] no block for rust, which the runner sweeps: its first run would "
        + "report first_run and gate nothing",
        "[bindings/haskell] the runner has no such binding, so nothing reads this block",
    ]


def test_a_hot_path_that_is_not_there_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Of two listed hot-path sources, the one the tree does not hold is named."""
    _ = plant(tmp_path, {RelPath("go/aletheia/client.go"): Prose("package aletheia\n")})
    monkeypatch.setattr(check_mutation_setup, "REPO_ROOT", tmp_path)
    assert check_mutation_setup.every_block_names_its_tool_and_hot_paths(
        {
            "go": {
                "tool": "gremlins",
                "hot_path": ["go/aletheia/client.go", "go/aletheia/moved_away.go"],
            }
        }
    ) == ["[go] hot-path source does not exist: go/aletheia/moved_away.go"]


def test_a_block_without_its_tool_or_its_hot_paths_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A block no mapping, naming no tool, listing no hot path or a hot path no path is named."""
    _ = plant(tmp_path, {RelPath("go/aletheia/client.go"): Prose("package aletheia\n")})
    monkeypatch.setattr(check_mutation_setup, "REPO_ROOT", tmp_path)
    assert check_mutation_setup.every_block_names_its_tool_and_hot_paths(
        {
            "a": "gremlins",
            "b": {"hot_path": ["go/aletheia/client.go"]},
            "c": {"tool": "", "hot_path": ["go/aletheia/client.go"]},
            "d": {"tool": "gremlins"},
            "e": {"tool": "gremlins", "hot_path": []},
            "f": {"tool": "gremlins", "hot_path": [3, "go/aletheia/client.go"]},
        }
    ) == [
        "[a] binding spec must be a mapping",
        "[b] missing 'tool' field in spec",
        "[c] missing 'tool' field in spec",
        "[d] missing or empty 'hot_path' field",
        "[e] missing or empty 'hot_path' field",
        "[f] hot-path entry is not a path: 3",
    ]


@pytest.mark.parametrize(
    ("record", "reason"),
    [
        pytest.param(None, Prose("No such file or directory"), id="missing"),
        pytest.param(
            Prose("bindings: [python\n"),
            Prose(
                'while parsing a flow sequence in "<unicode string>", line 1, column 11: '
                + "bindings: [python ^ expected ',' or ']', but got '<stream end>' in "
                + '"<unicode string>", line 2, column 1: ^'
            ),
            id="no YAML",
        ),
        pytest.param(
            Prose("- bindings\n"),
            Prose("it holds no mapping with a bindings entry"),
            id="a list",
        ),
        pytest.param(
            Prose("python: {}\n"),
            Prose("it holds no mapping with a bindings entry"),
            id="no bindings",
        ),
        pytest.param(
            Prose("bindings: [python]\n"),
            Prose("its bindings entry is not a mapping"),
            id="bindings a list",
        ),
    ],
)
def test_a_record_the_gate_cannot_read_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    record: Prose | None,
    reason: Prose,
) -> None:
    """A record missing, no YAML, or holding no mapping of bindings stops the gate with exit 2."""
    spec = tmp_path / "MUTATION_BENCH.yaml"
    if record is not None:
        _ = plant(tmp_path, {RelPath(spec.name): record})
    monkeypatch.setattr(check_mutation_setup, "SPEC_PATH", spec)
    monkeypatch.setattr(sys, "argv", ["check_mutation_setup"])
    assert stderr_of_exit_2(capsys, check_mutation_setup.main) == (
        f"ERROR: cannot read {spec}: {reason}\n"
    )


# Every measured block records the counts its lane is judged by.


def _no_count(binding: BindingName, count: Literal["total_mutants", "generated"]) -> Prose:
    """Return the diagnostic for a block recording its survivors and not ``count``."""
    return Prose(
        f"[{binding}/baseline] records its survivors and no {count} count, so the "
        + f"lane holds a sweep's {count} to nothing"
    )


def test_every_measured_block_recording_its_counts_passes() -> None:
    """Each lane's counts recorded, and a block measuring nothing, are clean."""
    assert not check_mutation_setup.every_block_records_its_counts(
        {
            "python": {"baseline": {"survivors": 0, "total_mutants": 12}},
            "go": {"baseline": {"survivors": 1, "total_mutants": 30, "generated": 34}},
            "rust": {"baseline": {"survivors": 0, "total_mutants": 9, "generated": 9}},
            "cpp": {"baseline": {"survivors": 0, "total_mutants": 40}},
            "unmeasured": {"baseline": {}},
            "no baseline": {"tool": "mull"},
            "no block": "mull",
        }
    )


def test_a_measured_block_missing_a_count_is_named() -> None:
    """A count absent, a boolean, or text where its lane is judged by it is named."""
    assert check_mutation_setup.every_block_records_its_counts(
        {
            "python": {"baseline": {"survivors": 0}},
            "go": {"baseline": {"survivors": 0}},
            "rust": {"baseline": {"survivors": 0, "total_mutants": 9, "generated": True}},
            "cpp": {"baseline": {"survivors": 0, "total_mutants": "40"}},
        }
    ) == [
        _no_count(BindingName("python"), "total_mutants"),
        _no_count(BindingName("go"), "total_mutants"),
        _no_count(BindingName("go"), "generated"),
        _no_count(BindingName("rust"), "generated"),
        _no_count(BindingName("cpp"), "total_mutants"),
    ]


# The ledgers: every row is a mapping naming a file and a text.


def test_a_misshapen_ledger_or_row_is_named() -> None:
    """A ledger no list, a row no mapping and a row without a file or a text are named."""
    assert check_mutation_setup.ledger_rows_still_name_their_line(
        {
            "go": {
                "baseline": {
                    "unobserved_ledger": {"file": "go/aletheia/client.go"},
                    "not_covered_ledger": ["return x + 1", {"file": "go/aletheia/client.go"}],
                }
            },
            "rust": "not a block",
        }
    ) == [
        "[go/unobserved_ledger] must be a list of rows",
        "[go/not_covered_ledger] every row must be a mapping",
        "[go/not_covered_ledger] a row must carry a 'file' and a 'text'",
    ]


# main runs every check, each record-reading one on the record it read.

# Each check, in main's order, and whether it reads the record.
_CHECKS: Final = (
    (CheckName("every_block_names_its_tool_and_hot_paths"), True),
    (CheckName("every_tools_importing_test_is_ignored"), False),
    (CheckName("every_above_tree_test_skips_or_is_ignored"), False),
    (CheckName("cpp_slice_weights_are_of_the_domain"), True),
    (CheckName("every_runner_has_a_block"), True),
    (CheckName("ledger_rows_still_name_their_line"), True),
    (CheckName("python_lane_runs_no_doc_harness"), False),
    (CheckName("go_lane_runs_no_doc_harness"), False),
    (CheckName("rust_lane_runs_no_doc_harness"), False),
    (CheckName("cpp_lane_runs_no_doc_harness"), False),
    (CheckName("go_lane_turns_on_the_default_off_mutators"), False),
    (CheckName("cpp_lane_links_the_library_statically"), False),
    (CheckName("every_block_records_its_counts"), True),
)
# The record the stand-in loader returns, held by identity.
_RECORD: Final = {"python": "a block"}


def _stand_in(monkeypatch: pytest.MonkeyPatch, *, failing: bool) -> list[Mock]:
    """Stand ``_RECORD`` and every check in, each returning its own name if ``failing``."""
    monkeypatch.setattr(sys, "argv", ["check_mutation_setup"])
    monkeypatch.setattr(check_mutation_setup, "_load_bindings", Mock(return_value=_RECORD))
    checks: list[Mock] = []
    for name, _reads_record in _CHECKS:
        check = Mock(return_value=[Prose(name)] if failing else [])
        monkeypatch.setattr(check_mutation_setup, name, check)
        checks.append(check)
    return checks


def _each_called_once_as_main_should(checks: list[Mock]) -> None:
    """Hold every check to one call: on the record ``main`` read, or on nothing."""
    for (_name, reads_record), check in zip(_CHECKS, checks, strict=True):
        if reads_record:
            assert check.call_count == 1
            assert len(check.call_args.args) == 1
            assert check.call_args.args[0] is _RECORD
            assert not check.call_args.kwargs
        else:
            check.assert_called_once_with()


def test_main_runs_every_check_and_names_each_failure(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Every check's diagnostic reaches stderr, in order, and the gate exits 1."""
    checks = _stand_in(monkeypatch, failing=True)
    assert check_mutation_setup.main() == 1
    err = capsys.readouterr().err
    assert [line.removeprefix("  - ") for line in err.splitlines() if line.startswith("  - ")] == [
        name for name, _reads_record in _CHECKS
    ]
    assert f"\n{len(_CHECKS)} issue(s) above." in err
    _each_called_once_as_main_should(checks)


def test_main_passes_when_every_check_does(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With every check clean the gate exits 0 and says so on stdout."""
    checks = _stand_in(monkeypatch, failing=False)
    assert check_mutation_setup.main() == 0
    captured = capsys.readouterr()
    assert captured.err == ""
    assert captured.out.startswith("Mutation-setup coverage gate OK: 1 bindings, 0 hot-path ")
    _each_called_once_as_main_should(checks)
