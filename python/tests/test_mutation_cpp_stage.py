# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the C++ lane in stages (``tools.mutation_cpp``).

Unset, the stage sweeps every tree whole in one process and merges them.  A
leg sweeps one slice of one tree, reports as its own binding, and is never
judged: it has read neither the rest of its tree nor the other trees, where the
mutant it let live may die.  The merge sweeps nothing, reads the legs' reports
from a directory, unions each tree's slices and intersects the trees, and
refuses a leg that is missing, doubled, or from another commit.  The merge of
the legs must equal the one-process run over the same trees.

Two refusals belong to slicing alone, and both stand for a file the partition
never claimed: two slices carrying one identifier, which is that file mutated
by every slice, and a union under the recorded census, which is that file
mutated by none.
"""

from __future__ import annotations

import json
import sqlite3
from typing import TYPE_CHECKING

import pytest

from tools import mutation_cpp, mutation_run
from tools.mutation_cpp import (
    CPP_LEGS_ENV,
    CPP_MERGE_STAGE,
    CPP_SLICE_ENV,
    CPP_STAGE_ENV,
    CppLeg,
    CppTree,
    elements_counts,
    is_cpp_leg,
    merge_elements,
    run_cpp,
    sliced_legs,
    union_slices,
)
from tools.mutation_cpp_slices import CPP_SLICES

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

_SHA = "testsha"

# What each slice carries. The slices of a tree partition the files, so no
# identifier is in two of them; that is the property the merge checks, and the
# fixture is built to have it so that breaking it is a test of its own.
_SLICE_MUTANTS: Mapping[int, tuple[str, ...]] = {
    number: tuple(f"m{number}{which}" for which in (1, 2, 3)) for number in range(1, CPP_SLICES + 1)
}
_ALL_MUTANTS = tuple(mutant for mutants in _SLICE_MUTANTS.values() for mutant in mutants)

# What each tree lets live: m11 survives every tree, m21 the leak tree alone.
# Read over ``CppTree`` rather than listed tree by tree, so a tree the lane
# gains is a tree this fixture covers rather than one it raises on.
_SURVIVORS: Mapping[CppTree, set[str]] = {
    tree: {"m11", "m21"} if tree is CppTree.LEAK else {"m11"} for tree in CppTree
}


def _elements(mutants: Sequence[str], survivors: set[str]) -> dict[str, object]:
    """Build an Elements report over the mutants given, those named surviving."""
    return {
        "files": {
            "/tree/cpp/src/a.cpp": {
                "mutants": [
                    {
                        "id": mutant,
                        "status": "Survived" if mutant in survivors else "Killed",
                        "mutatorName": "m",
                        "location": {"start": {"line": 1}},
                    }
                    for mutant in mutants
                ]
            }
        }
    }


def _leg_mutants(leg: CppLeg) -> tuple[str, ...]:
    """Name the mutants a leg's build carries: its slice's, or the tree's whole surface."""
    return _ALL_MUTANTS if leg.slice_no is None else _SLICE_MUTANTS[leg.slice_no]


def _write_leg_reports(artifact_dir: Path, leg: CppLeg) -> Mapping[str, object]:
    """Write the three reports Mull writes for one leg, and return its Elements report."""
    elements = _elements(_leg_mutants(leg), _SURVIVORS[leg.tree])
    _ = (artifact_dir / f"{leg.report_name}.json").write_text(json.dumps(elements))
    _ = (artifact_dir / f"{leg.report_name}.txt").write_text("[info] Mutation score: 66%\n")
    with sqlite3.connect(artifact_dir / f"{leg.report_name}.sqlite") as conn:
        _ = conn.execute(
            "CREATE TABLE mutant (mutant_id TEXT, execution_status INT, stdout TEXT, stderr TEXT)"
        )
    return elements


def _fixture_census(_tree: CppTree | None = None) -> int:
    """Stand in for ``recorded_total_mutants`` with the fixture's own surface."""
    return len(_ALL_MUTANTS)


def _one_over_the_fixture(_tree: CppTree | None = None) -> int:
    """Stand in for it with one mutant more than the fixture sweeps, which the merge refuses."""
    return len(_ALL_MUTANTS) + 1


def _fixed_sha(_root: Path | None = None) -> str:
    """Stand in for ``short_sha`` with a constant under the sandbox."""
    return _SHA


def _fake_sweeps(monkeypatch: pytest.MonkeyPatch, swept: list[str]) -> None:
    """Replace the build-and-sweep of a leg by writing its reports, recording which ran."""

    def sweep(
        _cmake: str, _mull: str, _build_dir: Path, artifact_dir: Path, leg: CppLeg
    ) -> tuple[str, Mapping[str, object]]:
        swept.append(str(leg))
        return f"=== {leg} leg ===\n", _write_leg_reports(artifact_dir, leg)

    monkeypatch.setattr(mutation_cpp, "_check_cpp_tools", lambda: ("cmake", "mull-runner-23"))
    monkeypatch.setattr(mutation_cpp, "_sweep_cpp_lane", sweep)
    monkeypatch.setattr(mutation_cpp, "short_sha", _fixed_sha)
    # The fixture's surface is nine mutants, not the repository's census, so
    # the floor is the fixture's; the refusal it exists for has its own test.
    monkeypatch.setattr(mutation_cpp, "recorded_total_mutants", _fixture_census)


def _stage(monkeypatch: pytest.MonkeyPatch, value: str | None, slice_no: str = "") -> None:
    for name, wanted in ((CPP_STAGE_ENV, value), (CPP_SLICE_ENV, slice_no or None)):
        if wanted is None:
            monkeypatch.delenv(name, raising=False)
        else:
            monkeypatch.setenv(name, wanted)


def test_unset_stage_sweeps_every_tree_whole_and_merges(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The whole lane in one process: every tree swept whole, in order, one merged verdict."""
    swept: list[str] = []
    _fake_sweeps(monkeypatch, swept)
    _stage(monkeypatch, None)
    report = run_cpp(tmp_path)
    assert swept == [tree.value for tree in CppTree]
    assert report.error is None
    assert report.binding == "cpp"
    assert (report.total_mutants, report.survived) == (len(_ALL_MUTANTS), 1)
    merged = json.loads((tmp_path / "cpp-mull.json").read_text())
    statuses = {m["id"]: m["status"] for m in merged["files"]["/tree/cpp/src/a.cpp"]["mutants"]}
    assert statuses["m11"] == "Survived"
    assert statuses["m21"] == "Killed"


@pytest.mark.parametrize("leg", sliced_legs(), ids=str)
def test_a_leg_sweeps_its_slice_alone_and_is_its_own_binding(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, leg: CppLeg
) -> None:
    """A leg sweeps one slice of one tree, reports as ``cpp-<leg>``, writes no merged report."""
    swept: list[str] = []
    _fake_sweeps(monkeypatch, swept)
    _stage(monkeypatch, leg.tree.value, str(leg.slice_no))
    report = run_cpp(tmp_path)
    assert swept == [str(leg)]
    assert report.error is None
    assert report.binding == leg.binding
    assert report.total_mutants == len(_SLICE_MUTANTS[leg.slice_no or 1])
    assert not (tmp_path / "cpp-mull.json").exists()
    assert (tmp_path / f"{leg.report_name}.json").is_file()


def test_a_leg_is_recorded_and_never_judged() -> None:
    """A leg's survivors exceed the baseline and the verdict is still not a regression."""
    leg = sliced_legs()[0]
    report = mutation_run.MutationReport(leg.binding, "mull", 1, 2, "")
    bindings: dict[str, mutation_run.BindingSpec] = {"cpp": {"baseline": {"survivors": 0}}}
    verdict = mutation_run.drift_for(report, bindings)
    assert verdict == {"status": "leg", "observed_survivors": 2}
    assert is_cpp_leg(report.binding)
    assert not is_cpp_leg("cpp")
    assert not is_cpp_leg(f"cpp-{CPP_MERGE_STAGE}")
    assert not is_cpp_leg(f"cpp-leak-{CPP_SLICES + 1}")


def test_a_leg_that_did_not_build_is_an_error() -> None:
    """A leg's pass means the slice built and swept; a failure is an error, not a leg."""
    report = mutation_run.MutationReport(sliced_legs()[-1].binding, "mull", 0, 0, "", error="x")
    assert mutation_run.drift_for(report, {})["status"] == "error"


def test_a_leg_that_never_swept_reports_under_its_own_name(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A leg missing its tools fails under ``cpp-<leg>``, so the report says which leg."""
    leg = sliced_legs()[0]
    _fake_sweeps(monkeypatch, [])
    monkeypatch.setattr(mutation_cpp, "_check_cpp_tools", lambda: "mull-runner-23 not in PATH")
    _stage(monkeypatch, leg.tree.value, str(leg.slice_no))
    report = run_cpp(tmp_path)
    assert report.binding == leg.binding
    assert report.error == "mull-runner-23 not in PATH"
    assert mutation_run.drift_for(report, {})["status"] == "error"


def test_a_stage_that_is_no_tree_is_an_error(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A misspelt tree fails the run rather than sweeping nothing."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, "leaks", "1")
    report = run_cpp(tmp_path)
    assert report.error is not None
    assert CPP_STAGE_ENV in report.error
    assert "leak, plain, address, merge" in report.error


def test_a_slice_that_is_no_slice_is_an_error(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A slice past the last one would sweep a tree whole under a leg's name."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, CppTree.LEAK.value, str(CPP_SLICES + 1))
    report = run_cpp(tmp_path)
    assert report.error is not None
    assert CPP_SLICE_ENV in report.error
    assert f"1 to {CPP_SLICES}" in report.error


def test_a_slice_of_no_tree_is_an_error(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """A job that names a slice and forgets the tree would sweep every tree whole."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, None, "1")
    report = run_cpp(tmp_path)
    assert report.error is not None
    assert CPP_SLICE_ENV in report.error
    assert CPP_STAGE_ENV in report.error


def _leg_summary(commit: str, leg: CppLeg, elapsed: float) -> str:
    return json.dumps(
        {
            "commit": commit,
            "elapsed_s": {"cpp": elapsed},
            "runs": [{"binding": leg.binding, "tool": "mull"}],
        }
    )


def _elapsed_of(leg: CppLeg) -> float:
    """Give each leg a wall clock of its own, so the recorded map is checked per leg."""
    return 100.0 + len(str(leg))


def _download(legs_dir: Path, *legs: CppLeg, commit: str = _SHA) -> None:
    """Lay the legs' artifacts out the way the download does: one directory per leg."""
    for leg in legs:
        leg_dir = legs_dir / f"mutation-{leg.binding}" / commit
        leg_dir.mkdir(parents=True)
        _ = _write_leg_reports(leg_dir, leg)
        _ = (leg_dir / "summary.json").write_text(_leg_summary(commit, leg, _elapsed_of(leg)))


def _merge(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> mutation_run.MutationReport:
    """Run the merge stage over ``tmp_path / legs`` into ``tmp_path / out``."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, CPP_MERGE_STAGE)
    monkeypatch.setenv(CPP_LEGS_ENV, str(tmp_path / "legs"))
    out = tmp_path / "out"
    out.mkdir(exist_ok=True)
    return run_cpp(out)


def test_the_merge_of_the_legs_is_the_one_process_run(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The legs merged read exactly what one process sweeping every tree whole reads."""
    _download(tmp_path / "legs", *sliced_legs())
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is None
    assert merged.binding == "cpp"

    whole = tmp_path / "whole"
    whole.mkdir()
    _stage(monkeypatch, None)
    one_process = run_cpp(whole)
    assert (merged.total_mutants, merged.survived) == (
        one_process.total_mutants,
        one_process.survived,
    )
    for name in ("cpp-mull.json", "cpp-routes.json", "cpp-files.json"):
        assert (tmp_path / "out" / name).read_text() == (whole / name).read_text()
    legs = json.loads((tmp_path / "out" / "cpp-legs.json").read_text())
    assert legs == {str(leg): _elapsed_of(leg) for leg in sliced_legs()}
    assert mutation_run.drift_for(merged, {"cpp": {"baseline": {"survivors": 1}}})["status"] == "ok"


def test_the_merge_refuses_a_missing_leg(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """A slice's reports missing is a tree read in part, and a part is no verdict."""
    _download(tmp_path / "legs", *sliced_legs()[1:])
    merged = _merge(monkeypatch, tmp_path)
    missing = sliced_legs()[0]
    assert merged.error is not None
    assert f"0 copies of {missing.report_name}.json" in merged.error


def test_the_merge_refuses_a_doubled_leg(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """Two copies of one leg's report is a download that cannot be trusted."""
    legs = sliced_legs()
    _download(tmp_path / "legs", *legs)
    _download(tmp_path / "legs" / "again", legs[-1])
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert f"2 copies of {legs[-1].report_name}.json" in merged.error


def test_the_merge_refuses_a_leg_of_another_commit(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A leg swept at another commit merges into a verdict about nothing."""
    legs = sliced_legs()
    _download(tmp_path / "legs", *legs[:-1])
    _download(tmp_path / "legs", legs[-1], commit="othersha")
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert "is a run at othersha, this merge is at testsha" in merged.error


def test_the_merge_refuses_a_leg_without_its_summary(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The summary carries the leg's commit and wall clock; without it the leg is not one."""
    legs = sliced_legs()
    _download(tmp_path / "legs", *legs)
    (tmp_path / "legs" / f"mutation-{legs[-1].binding}" / _SHA / "summary.json").unlink()
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert f"no summary of the {legs[-1]} leg" in merged.error


def test_the_merge_refuses_two_slices_carrying_one_mutant(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A file no slice holds out is mutated by all of them, and arrives once per slice.

    The shape a file the partition never claimed takes at the merge, and the
    reason the slices state what they hold out rather than what they claim: a
    slice stating what it claims would drop that file and report the smaller
    census as a clean sweep.
    """
    legs = sliced_legs()
    _download(tmp_path / "legs", *legs)
    doubled = legs[1]
    leg_dir = tmp_path / "legs" / f"mutation-{doubled.binding}" / _SHA
    report = leg_dir / f"{doubled.report_name}.json"
    shared = _SLICE_MUTANTS[1][0]
    _ = report.write_text(
        json.dumps(_elements((*_leg_mutants(doubled), shared), _SURVIVORS[doubled.tree]))
    )
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert shared in merged.error
    assert "no slice held that file out" in merged.error


def test_the_merge_refuses_a_union_under_the_recorded_census(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A union short of the record is a slice that carried fewer files than it was given.

    Growth is ordinary work and passes; a census that shrank is either a hole
    in the slices or a deliberate removal, and a removal lowers the record in
    the same commit.
    """
    _download(tmp_path / "legs", *sliced_legs())
    _fake_sweeps(monkeypatch, [])
    # After the fixture, which sets the floor to what the fixture sweeps.
    monkeypatch.setattr(mutation_cpp, "recorded_total_mutants", _one_over_the_fixture)
    _stage(monkeypatch, CPP_MERGE_STAGE)
    monkeypatch.setenv(CPP_LEGS_ENV, str(tmp_path / "legs"))
    out = tmp_path / "out"
    out.mkdir()
    merged = run_cpp(out)
    assert merged.error is not None
    assert f"union to {len(_ALL_MUTANTS)} mutants, under the recorded" in merged.error


def test_the_census_floor_is_the_tree_s_own(monkeypatch: pytest.MonkeyPatch) -> None:
    """A tree is held to what the record says that tree carries, not to the merged surface.

    The trees do not all carry one surface: one that cannot read a mutator
    carries none of its mutants, and holding it to the merged figure would
    refuse every sweep it ever ran.
    """
    spec = {
        "bindings": {
            "cpp": {
                "baseline": {
                    "total_mutants": 100,
                    "mutants_by_tree": {CppTree.ADDRESS.value: 30},
                }
            }
        }
    }
    monkeypatch.setattr(mutation_cpp, "load_spec", lambda: spec)
    assert mutation_cpp.recorded_total_mutants() == 100
    assert mutation_cpp.recorded_total_mutants(CppTree.ADDRESS) == 30
    # A tree the record names no figure for is held to the merged one.
    assert mutation_cpp.recorded_total_mutants(CppTree.PLAIN) == 100


def test_a_tree_that_does_not_carry_a_mutant_says_nothing_about_it() -> None:
    """A mutant absent from a tree's report is not a mutant that tree killed.

    A tree drops the mutators it cannot read, so it carries none of their
    mutants: the address tree drops the two over calls, whose mutants there
    are the sanitizer's own inserted checks rather than the program's calls.
    Judging a survivor on every report alike would read that absence as a
    kill, which is the one direction a merge must not invent.
    """
    carried_by_both = _elements(("m1", "m2"), {"m1", "m2"})
    narrower = _elements(("m2",), {"m2"})
    merged = merge_elements([carried_by_both, narrower])
    assert elements_counts(merged) == (2, 2)

    # And a tree that does carry it, and killed it, still kills it.
    killed_there = _elements(("m1", "m2"), {"m2"})
    assert elements_counts(merge_elements([carried_by_both, killed_there])) == (2, 1)


def test_a_merged_report_carries_the_score_of_its_own_mutants() -> None:
    """A merge produces a report no sweep did, so the score must follow the merge.

    Mull writes the score of the sweep behind each input, and the field is
    what the Elements viewer renders: the cross-tree merge revives every
    mutant another tree killed, and a tree's slices each scored their own
    share of the surface. Carrying the first input's score forward states a
    number nothing measured.
    """
    left = {**_elements(("m1", "m2"), {"m1"}), "mutationScore": 50.0}
    right = {**_elements(("m1", "m2"), set()), "mutationScore": 99.0}
    merged = merge_elements([left, right])
    assert elements_counts(merged) == (2, 0)
    assert merged["mutationScore"] == 100.0

    # A tree's slices: one killed its only mutant, the other let its own live.
    first = {**_elements(("m1",), set()), "mutationScore": 100.0}
    second = {**_elements(("m2",), {"m2"}), "mutationScore": 0.0}
    unioned = union_slices([first, second])
    assert not isinstance(unioned, str)
    assert elements_counts(unioned) == (2, 1)
    assert unioned["mutationScore"] == 50.0


def test_the_merge_needs_the_legs_directory(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The merge stage without a legs directory is a misconfigured job, and says so."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, CPP_MERGE_STAGE)
    monkeypatch.delenv(CPP_LEGS_ENV, raising=False)
    merged = run_cpp(tmp_path)
    assert merged.error is not None
    assert CPP_LEGS_ENV in merged.error
