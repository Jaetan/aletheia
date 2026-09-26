# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the Rust lane's reading of cargo-mutants and the drift gate over it.

cargo-mutants puts every mutant in one of four buckets and writes them to
``outcomes.json``; the console prints only what was missed.  What is held
here: the counts are read from the file, a survivor is keyed on the mutation
and its source line the way the C++ ledger keys one, a sweep that reached no
mutant is an error rather than a clean run of nothing, the tool's version is
read off its banner, and the verdict refuses a survivor the record does not
name.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from tools import mutation_run, mutation_rust
from tools.mutation_report import MutationReport

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path

    from tools.mutation_report import BindingSpec


def _mutant(file: str, line: int, name: str, summary: str) -> dict[str, object]:
    """One outcome in the shape cargo-mutants 27 writes."""
    return {
        "scenario": {
            "Mutant": {
                "name": f"{file}:{line}:5: {name}",
                "package": "aletheia",
                "file": file,
                "function": {"function_name": "f", "return_type": "", "span": {}},
                "span": {"start": {"line": line, "column": 5}, "end": {"line": line, "column": 9}},
                "replacement": "()",
                "genre": "FnValue",
            }
        },
        "summary": summary,
        "log_path": "log/x.log",
        "diff_path": "diff/x.diff",
        "phase_results": [],
    }


_OUTCOMES: dict[str, object] = {
    "outcomes": [
        {"scenario": "Baseline", "summary": "Success", "phase_results": []},
        _mutant("src/backend.rs", 2, "replace > with >= in frame_len", "MissedMutant"),
        _mutant("src/backend.rs", 2, "replace > with == in frame_len", "MissedMutant"),
        _mutant("src/types.rs", 3, "replace Dlc::new -> Self with 0", "CaughtMutant"),
        _mutant("src/types.rs", 1, "replace as_u8 -> u8 with 0", "Unviable"),
        _mutant("src/types.rs", 1, "replace as_u8 -> u8 with 1", "Timeout"),
    ],
    "total_mutants": 5,
    "missed": 2,
    "caught": 1,
    "timeout": 1,
    "unviable": 1,
    "success": 0,
    "cargo_mutants_version": "27.1.0",
}


def _tree(tmp_path: Path) -> Path:
    crate = tmp_path / "rust" / "src"
    crate.mkdir(parents=True)
    _ = (crate / "backend.rs").write_text("fn frame_len() {\n    if data.len() > MAX {\n}\n")
    _ = (crate / "types.rs").write_text("a\nb\nc\n")
    return tmp_path


def _read_line(root: Path) -> Callable[[str, int], str]:
    def read(file: str, line: int) -> str:
        return (root / file).read_text(encoding="utf-8").split("\n")[line - 1]

    return read


def _spec(survivors: int = 2, **baseline: object) -> dict[str, BindingSpec]:
    return {"rust": cast("BindingSpec", {"baseline": {"survivors": survivors, **baseline}})}


def test_the_counts_are_read_from_the_outcomes() -> None:
    """Caught is killed, missed is survived, and the timeouts travel with the report."""
    rep = mutation_rust.parse_outcomes(_OUTCOMES, "", "exit 2")
    assert rep.error is None
    assert (rep.killed, rep.survived, rep.timeouts) == (1, 2, 1)
    assert rep.total_mutants == 3


def test_a_sweep_that_reached_no_mutant_is_an_error() -> None:
    """A failed baseline leaves every bucket empty, which is not a clean run."""
    empty: dict[str, object] = {
        **_OUTCOMES,
        "outcomes": [],
        "missed": 0,
        "caught": 0,
        "timeout": 0,
        "unviable": 0,
    }
    rep = mutation_rust.parse_outcomes(empty, "", "exit 1")
    assert rep.error is not None
    assert "no mutant" in rep.error
    absent = mutation_rust.parse_outcomes({"outcomes": []}, "", "exit 1")
    assert absent.error is not None
    assert "no counts" in absent.error


def test_survivors_are_keyed_on_the_mutation_and_the_source_line(tmp_path: Path) -> None:
    """The position is stripped from the name; the line's text is read from the tree."""
    rows = mutation_rust.outcomes_survivor_rows(_OUTCOMES, _read_line(_tree(tmp_path)))
    assert rows == {
        ("replace > with >= in frame_len", "rust/src/backend.rs", "if data.len() > MAX {"): 1,
        ("replace > with == in frame_len", "rust/src/backend.rs", "if data.len() > MAX {"): 1,
    }


def test_the_version_is_read_off_the_banner() -> None:
    """``cargo mutants --version`` prints the name and the version; anything else is none."""
    assert mutation_rust.cargo_mutants_version("cargo-mutants 27.1.0\n") == "27.1.0"
    assert mutation_rust.cargo_mutants_version("error: no such command: `mutants`") is None


def test_a_survivor_the_ledger_does_not_name_fails(tmp_path: Path) -> None:
    """At an unchanged count, a survivor traded for another is still a regression."""
    rows = mutation_rust.outcomes_survivor_rows(_OUTCOMES, _read_line(_tree(tmp_path)))
    rep = MutationReport("rust", "cargo-mutants", 1, 2, "", timeouts=1)
    ledger = [
        {
            "mutator": "replace > with >= in frame_len",
            "file": "rust/src/backend.rs",
            "text": "if data.len() > MAX {",
            "count": 1,
        },
        {"mutator": "replace a with b in g", "file": "rust/src/types.rs", "text": "a", "count": 1},
    ]
    entry = mutation_run.drift_for(rep, _spec(survivors_ledger=ledger), survivor_rows=rows)
    assert entry["status"] == "regression"
    assert entry.get("unrecorded_survivors") == [
        {
            "mutator": "replace > with == in frame_len",
            "file": "rust/src/backend.rs",
            "text": "if data.len() > MAX {",
            "count": 1,
        }
    ]
    assert entry.get("stale_ledger") == [ledger[1]]


def test_the_timeout_ceiling_is_read_before_the_count() -> None:
    """A run that timed out on nearly everything is refused whatever else it reports."""
    rep = MutationReport("rust", "cargo-mutants", 3, 0, "", timeouts=300)
    entry = mutation_run.drift_for(rep, _spec(survivors=0, timeout_ceiling=20))
    assert entry["status"] == "regression"
    assert entry.get("observed_timeouts") == 300
