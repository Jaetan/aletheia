# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the C++ lane in stages (``tools.mutation_cpp``).

Unset, the stage sweeps the tree whole in one process.  A leg sweeps one
slice of it, reports as its own binding, and is never judged: it has read
none of the other slices.  The merge sweeps nothing, reads the legs' reports
from a directory, unions the slices, and refuses a leg that is missing,
doubled, or from another commit.  The merge of the legs must equal the
one-process run over the tree.

Two refusals belong to slicing alone, and both stand for a file the partition
never claimed: two slices carrying one identifier, which is that file mutated
by every slice, and a union short of the recorded census, which is that file
mutated by none.
"""

from __future__ import annotations

import contextlib
import json
import sqlite3
from typing import TYPE_CHECKING

import pytest

from tools import mutation_cpp, mutation_run
from tools._common import RelPath
from tools.mutation_cpp import elements_counts, run_cpp, union_slices
from tools.mutation_cpp_legs import (
    CPP_LEGS_ENV,
    CPP_MERGE_STAGE,
    CPP_STAGE_ENV,
    CppLeg,
    is_cpp_leg,
    sliced_legs,
)
from tools.mutation_cpp_runs import CPP_LEG_RUNS_SUFFIX, CPP_RUNS_REPORT
from tools.mutation_cpp_slices import CPP_SLICES, SuiteRuns
from tools.mutation_report import MutantCount
from tools.mutation_routes import MULL_TIMEDOUT

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

_SHA = "testsha"

# What each slice carries. The slices partition the files, so no
# identifier is in two of them; that is the property the merge checks, and the
# fixture is built to have it so that breaking it is a test of its own.
_SLICE_MUTANTS: Mapping[int, tuple[str, ...]] = {
    number: tuple(f"m{number}{which}" for which in (1, 2, 3)) for number in range(1, CPP_SLICES + 1)
}
_ALL_MUTANTS = tuple(mutant for mutants in _SLICE_MUTANTS.values() for mutant in mutants)

# What the sweep lets live, whichever leg reads it.
_SURVIVORS = {"m11"}


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
    """Name the mutants a leg's build carries: its slice's, or the whole surface."""
    return _ALL_MUTANTS if leg.slice_no is None else _SLICE_MUTANTS[leg.slice_no]


def _write_leg_reports(artifact_dir: Path, leg: CppLeg) -> Mapping[str, object]:
    """Write the three reports Mull writes for one leg and the runs it writes, return its Elements.

    Every mutant costs one suite run, so the slices sum to what the whole
    sweep costs.
    """
    elements = _elements(_leg_mutants(leg), _SURVIVORS)
    _ = (artifact_dir / f"{leg.report_name}.json").write_text(json.dumps(elements))
    _ = (artifact_dir / f"{leg.report_name}.txt").write_text("[info] Mutation score: 66%\n")
    runs = {RelPath("cpp/src/a.cpp"): SuiteRuns(len(_leg_mutants(leg)))}
    _ = (artifact_dir / f"{leg.report_name}{CPP_LEG_RUNS_SUFFIX}").write_text(json.dumps(runs))
    # closing() closes the connection; sqlite3's own context manager only
    # commits, which would leave the file open until a collection.
    with contextlib.closing(sqlite3.connect(artifact_dir / f"{leg.report_name}.sqlite")) as conn:
        _ = conn.execute(
            "CREATE TABLE mutant (mutant_id TEXT, execution_status INT, exit_status INT,"
            + " stdout TEXT, stderr TEXT)"
        )
        conn.commit()
    return elements


def _fixture_census() -> int:
    """Stand in for ``recorded_total_mutants`` with the fixture's own surface."""
    return len(_ALL_MUTANTS)


def _fixed_sha(_root: Path | None = None) -> str:
    """Stand in for ``short_sha`` with a constant under the sandbox."""
    return _SHA


# The mutant a sweep can be told the runner ended at its cap.
_TIMED_OUT_MUTANT = "m12"


def _time_out(sqlite_path: Path) -> None:
    """Record in one leg's census that the runner ended the timed-out mutant at its cap."""
    with contextlib.closing(sqlite3.connect(sqlite_path)) as conn:
        _ = conn.execute(
            "INSERT INTO mutant VALUES (?, ?, ?, ?, ?)",
            (_TIMED_OUT_MUTANT, MULL_TIMEDOUT, -1, "", ""),
        )
        conn.commit()


def _fake_sweeps(
    monkeypatch: pytest.MonkeyPatch, swept: list[str], *, timed_out: bool = False
) -> None:
    """Replace the build-and-sweep of a leg by writing its reports, recording which ran."""

    def sweep(
        _cmake: str, _mull: str, _build_dir: Path, artifact_dir: Path, leg: CppLeg
    ) -> tuple[str, Mapping[str, object]]:
        swept.append(str(leg))
        elements = _write_leg_reports(artifact_dir, leg)
        if timed_out and _TIMED_OUT_MUTANT in _leg_mutants(leg):
            _time_out(artifact_dir / f"{leg.report_name}.sqlite")
        return f"=== {leg} leg ===\n", elements

    monkeypatch.setattr(mutation_cpp, "_check_cpp_tools", lambda: ("cmake", "mull-runner-23"))
    monkeypatch.setattr(mutation_cpp, "_sweep_cpp_lane", sweep)
    monkeypatch.setattr(mutation_cpp, "short_sha", _fixed_sha)
    # The fixture's surface is nine mutants, not the repository's census, so
    # the census is the fixture's; the refusal it exists for has its own test.
    monkeypatch.setattr(mutation_cpp, "recorded_total_mutants", _fixture_census)


def _stage(monkeypatch: pytest.MonkeyPatch, value: str | None) -> None:
    if value is None:
        monkeypatch.delenv(CPP_STAGE_ENV, raising=False)
    else:
        monkeypatch.setenv(CPP_STAGE_ENV, value)


def test_unset_stage_sweeps_the_tree_whole(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """The whole lane in one process: the tree swept whole, one verdict."""
    swept: list[str] = []
    _fake_sweeps(monkeypatch, swept)
    _stage(monkeypatch, None)
    report = run_cpp(tmp_path)
    assert swept == ["cpp"]
    assert report.error is None
    assert report.binding == "cpp"
    assert (report.total_mutants, report.survived) == (len(_ALL_MUTANTS), 1)
    merged = json.loads((tmp_path / "cpp-mull.json").read_text())
    statuses = {m["id"]: m["status"] for m in merged["files"]["/tree/cpp/src/a.cpp"]["mutants"]}
    assert statuses["m11"] == "Survived"
    assert statuses["m21"] == "Killed"


def test_a_mutant_that_timed_out_is_neither_killed_nor_survived(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The census's timeout route reaches the report, and a ceiling of 0 refuses the sweep.

    The lane reads a mutant ended at the runner's cap as no verdict: it
    leaves the killed count, and the drift gate refuses the run.
    """
    _fake_sweeps(monkeypatch, [], timed_out=True)
    _stage(monkeypatch, None)
    report = run_cpp(tmp_path)
    assert report.error is None
    assert (report.killed, report.survived, report.observed.timeouts) == (
        len(_ALL_MUTANTS) - 2,
        1,
        1,
    )
    verdict = mutation_run.drift_for(
        report, {"cpp": {"baseline": {"survivors": 1, "timeout_ceiling": 0}}}
    )
    assert verdict["status"] == "regression"


@pytest.mark.parametrize("leg", sliced_legs(), ids=str)
def test_a_leg_sweeps_its_slice_alone_and_is_its_own_binding(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, leg: CppLeg
) -> None:
    """A leg sweeps one slice, reports as ``cpp-<slice>``, writes no merged report."""
    swept: list[str] = []
    _fake_sweeps(monkeypatch, swept)
    _stage(monkeypatch, str(leg.slice_no))
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
    assert not is_cpp_leg(f"cpp-{CPP_SLICES + 1}")


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
    _stage(monkeypatch, str(leg.slice_no))
    report = run_cpp(tmp_path)
    assert report.binding == leg.binding
    assert report.error == "mull-runner-23 not in PATH"
    assert mutation_run.drift_for(report, {})["status"] == "error"


@pytest.mark.parametrize("stage", ["merges", "plain", str(CPP_SLICES + 1), "0"])
def test_a_stage_that_is_no_slice_and_no_merge_is_an_error(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, stage: str
) -> None:
    """A misspelt stage, or a slice past the last one, fails the run instead of sweeping nothing."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, stage)
    report = run_cpp(tmp_path)
    assert report.error is not None
    assert CPP_STAGE_ENV in report.error
    assert f"1 to {CPP_SLICES} or {CPP_MERGE_STAGE!r}" in report.error


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
    """The legs merged read exactly what one process sweeping the tree whole reads."""
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
    for name in ("cpp-mull.json", "cpp-routes.json", CPP_RUNS_REPORT):
        assert (tmp_path / "out" / name).read_text() == (whole / name).read_text()
    legs = json.loads((tmp_path / "out" / "cpp-legs.json").read_text())
    assert legs == {str(leg): _elapsed_of(leg) for leg in sliced_legs()}
    runs = json.loads((tmp_path / "out" / CPP_RUNS_REPORT).read_text())
    assert runs == {"cpp/src/a.cpp": len(_ALL_MUTANTS)}
    # The report carries the census it wrote and the files it made a mutant in.
    assert merged.observed.routes == json.loads((tmp_path / "out" / "cpp-routes.json").read_text())
    assert merged.observed.routes == one_process.observed.routes
    assert (
        merged.observed.mutated_files
        == one_process.observed.mutated_files
        == {RelPath("cpp/src/a.cpp")}
    )
    assert mutation_run.drift_for(merged, {"cpp": {"baseline": {"survivors": 1}}})["status"] == "ok"


def test_the_merge_refuses_a_missing_leg(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """A slice's reports missing is the tree read in part, and a part is no verdict."""
    _download(tmp_path / "legs", *sliced_legs()[1:])
    merged = _merge(monkeypatch, tmp_path)
    missing = sliced_legs()[0]
    assert merged.error is not None
    assert f"0 copies of {missing.report_name}.json" in merged.error


def test_the_merge_refuses_a_leg_without_its_runs(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A leg whose runs are missing leaves the weights unknowable, and is refused."""
    legs = sliced_legs()
    _download(tmp_path / "legs", *legs)
    runs = f"{legs[0].report_name}{CPP_LEG_RUNS_SUFFIX}"
    for path in (tmp_path / "legs").rglob(runs):
        path.unlink()
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert f"0 copies of {runs}" in merged.error


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
    _ = report.write_text(json.dumps(_elements((*_leg_mutants(doubled), shared), _SURVIVORS)))
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert shared in merged.error
    assert "no slice held that file out" in merged.error


@pytest.mark.parametrize(
    "census", [MutantCount(len(_ALL_MUTANTS) + 1), MutantCount(len(_ALL_MUTANTS) - 1)]
)
def test_the_merge_refuses_a_union_off_the_recorded_census(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, census: MutantCount
) -> None:
    """A union off the record is a hole in the slices, or a surface the record does not follow.

    Short of the record is a slice that carried fewer files than it was
    given; past it, or short by a deliberate removal, is a surface that moved,
    and the change that moved it records the new census in the same commit.
    """
    _download(tmp_path / "legs", *sliced_legs())
    _fake_sweeps(monkeypatch, [])

    # After the fixture, which sets the census to what the fixture sweeps.
    def recorded() -> MutantCount:
        return census

    monkeypatch.setattr(mutation_cpp, "recorded_total_mutants", recorded)
    _stage(monkeypatch, CPP_MERGE_STAGE)
    monkeypatch.setenv(CPP_LEGS_ENV, str(tmp_path / "legs"))
    out = tmp_path / "out"
    out.mkdir()
    merged = run_cpp(out)
    assert merged.error is not None
    assert f"union to {len(_ALL_MUTANTS)} mutants, where the record holds {census}" in merged.error


def test_a_unioned_report_carries_the_score_of_its_own_mutants() -> None:
    """A union produces a report no sweep did, so the score must follow the union.

    Mull writes the score of the sweep behind each input, and the field is
    what the Elements viewer renders: each slice scored its own share of the
    surface, and carrying the first input's score forward states a number
    nothing measured.
    """
    # One slice killed its only mutant, the other let its own live.
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
