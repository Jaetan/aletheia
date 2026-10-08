# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Rust lane's shards merge into one sweep's outcomes, or are refused.

The sweep runs as shards side by side, each a cargo-mutants process in a
scratch copy of its own, and their ``outcomes.json`` files are merged into the
one the survivor ledger reads.  The merge holds the shards to the listing the
same tool prints: every listed mutant swept once, none twice, none unlisted.
Each refusal is staged by a fixture that breaks exactly the claim it holds.
"""

from __future__ import annotations

from tools.mutation_report import MutantCount
from tools.mutation_rust import (
    CrateFile,
    ListedMutant,
    MutantOutcome,
    MutationName,
    OutcomeSummary,
    SourceIndex,
    SourceSpan,
    SweepOutcomes,
    merge_shard_outcomes,
    outcomes_survivor_rows,
)


def _listed(line: SourceIndex) -> ListedMutant:
    span: SourceSpan = {
        "start": {"line": line, "column": SourceIndex(1)},
        "end": {"line": line, "column": SourceIndex(2)},
    }
    return {
        "file": CrateFile("src/lib.rs"),
        "name": MutationName(f"src/lib.rs:{line}:1: replace {line}"),
        "span": span,
    }


def _shard(mutants: list[ListedMutant], summary: OutcomeSummary) -> SweepOutcomes:
    swept: list[MutantOutcome] = [
        {"scenario": {"Mutant": mutant}, "summary": summary} for mutant in mutants
    ]
    baseline: MutantOutcome = {"scenario": "Baseline", "summary": OutcomeSummary("Success")}
    outcomes = [baseline, *swept]
    missed = len(mutants) if summary == "MissedMutant" else 0
    return {
        "outcomes": outcomes,
        "total_mutants": MutantCount(len(mutants)),
        "caught": MutantCount(len(mutants) - missed),
        "missed": MutantCount(missed),
        "timeout": MutantCount(0),
        "unviable": MutantCount(0),
        "success": MutantCount(0),
    }


_A, _B, _C = _listed(SourceIndex(1)), _listed(SourceIndex(2)), _listed(SourceIndex(3))
_CAUGHT = OutcomeSummary("CaughtMutant")
_MISSED = OutcomeSummary("MissedMutant")


def test_shards_that_partition_the_listing_merge_into_one_sweep() -> None:
    """Every bucket summed, one baseline kept, every mutant's outcome carried."""
    merged = merge_shard_outcomes([_A, _B, _C], [_shard([_A, _C], _CAUGHT), _shard([_B], _MISSED)])
    assert isinstance(merged, dict)
    assert (merged["total_mutants"], merged["caught"], merged["missed"]) == (3, 2, 1)
    assert [outcome["scenario"] for outcome in merged["outcomes"]].count("Baseline") == 1
    assert len(merged["outcomes"]) == 4


def test_the_merged_outcomes_read_as_one_sweep_s_survivors() -> None:
    """The ledger reader takes the merged file unchanged: the one missed mutant is one row."""
    merged = merge_shard_outcomes([_A, _B], [_shard([_A], _CAUGHT), _shard([_B], _MISSED)])
    assert isinstance(merged, dict)
    rows = outcomes_survivor_rows(merged, lambda _file, line: f"line {line}")
    assert rows == {("replace 2", "rust/src/lib.rs", "line 2"): 1}


def test_a_mutant_swept_by_two_shards_is_refused() -> None:
    """A shard that swept another's part, which a sum of counts would double."""
    refusal = merge_shard_outcomes([_A, _B], [_shard([_A, _B], _CAUGHT), _shard([_B], _CAUGHT)])
    assert isinstance(refusal, str)
    assert "more than one shard" in refusal


def test_a_listed_mutant_no_shard_swept_is_refused() -> None:
    """A shard that stopped short, which reads as a clean, smaller sweep."""
    refusal = merge_shard_outcomes([_A, _B, _C], [_shard([_A], _CAUGHT), _shard([_B], _CAUGHT)])
    assert isinstance(refusal, str)
    assert "1 unswept" in refusal


def test_a_mutant_the_listing_does_not_name_is_refused() -> None:
    """A shard of another tree, or of another version of the tool."""
    refusal = merge_shard_outcomes([_A], [_shard([_A], _CAUGHT), _shard([_B], _CAUGHT)])
    assert isinstance(refusal, str)
    assert "1 not listed" in refusal
