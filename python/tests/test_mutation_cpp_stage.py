# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the C++ lane in stages (``tools.mutation_cpp``).

Unset, the stage sweeps both trees in one process and merges them.  A leg
sweeps one tree, reports as its own binding, and is never judged: a mutant
one tree let live may die in the other.  The merge sweeps nothing, reads the
legs' reports from a directory, refuses a leg that is missing, doubled, or
from another commit, and is gated as the whole lane is.  The merge of two
legs must equal the one-process run over the same trees.
"""

from __future__ import annotations

import json
import sqlite3
from typing import TYPE_CHECKING

import pytest

from tools import mutation_cpp, mutation_run
from tools.mutation_cpp import (
    CPP_LANES,
    CPP_LEGS_ENV,
    CPP_STAGE_ENV,
    CppStage,
    is_cpp_leg,
    leg_binding,
    run_cpp,
)

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

_SHA = "testsha"


def _elements(survivors: set[str]) -> dict[str, object]:
    """Build an Elements report over three mutants, those named surviving."""
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
                    for mutant in ("m1", "m2", "m3")
                ]
            }
        }
    }


# What each tree lets live: m1 survives both, m2 only the leak tree.
_SURVIVORS = {"leak": {"m1", "m2"}, "plain": {"m1"}}


def _write_lane_reports(artifact_dir: Path, lane: str) -> Mapping[str, object]:
    """Write the three reports Mull writes for one tree, and return its Elements report."""
    name = f"cpp-mull-{lane}"
    elements = _elements(_SURVIVORS[lane])
    _ = (artifact_dir / f"{name}.json").write_text(json.dumps(elements))
    _ = (artifact_dir / f"{name}.txt").write_text("[info] Mutation score: 66%\n")
    with sqlite3.connect(artifact_dir / f"{name}.sqlite") as conn:
        _ = conn.execute(
            "CREATE TABLE mutant (mutant_id TEXT, execution_status INT, stdout TEXT, stderr TEXT)"
        )
    return elements


def _fixed_sha(_root: Path | None = None) -> str:
    """Stand in for ``short_sha`` with a constant under the sandbox."""
    return _SHA


def _fake_sweeps(monkeypatch: pytest.MonkeyPatch, swept: list[str]) -> None:
    """Replace the build-and-sweep of a tree by writing its reports, recording which ran."""

    def sweep(
        _cmake: str, _mull: str, _build_dir: Path, artifact_dir: Path, sanitizer: str
    ) -> tuple[str, Mapping[str, object]]:
        lane = sanitizer or "plain"
        swept.append(lane)
        return f"=== {lane} lane ===\n", _write_lane_reports(artifact_dir, lane)

    monkeypatch.setattr(mutation_cpp, "_check_cpp_tools", lambda: ("cmake", "mull-runner-23"))
    monkeypatch.setattr(mutation_cpp, "_sweep_cpp_lane", sweep)
    monkeypatch.setattr(mutation_cpp, "short_sha", _fixed_sha)


def _stage(monkeypatch: pytest.MonkeyPatch, value: str | None) -> None:
    if value is None:
        monkeypatch.delenv(CPP_STAGE_ENV, raising=False)
    else:
        monkeypatch.setenv(CPP_STAGE_ENV, value)


def test_unset_stage_sweeps_both_trees_and_merges(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The whole lane in one process: every tree swept, in order, one merged verdict."""
    swept: list[str] = []
    _fake_sweeps(monkeypatch, swept)
    _stage(monkeypatch, None)
    report = run_cpp(tmp_path)
    assert swept == [sanitizer or "plain" for sanitizer, _ in CPP_LANES]
    assert report.error is None
    assert report.binding == "cpp"
    assert (report.total_mutants, report.survived) == (3, 1)
    merged = json.loads((tmp_path / "cpp-mull.json").read_text())
    statuses = {m["id"]: m["status"] for m in merged["files"]["/tree/cpp/src/a.cpp"]["mutants"]}
    assert statuses == {"m1": "Survived", "m2": "Killed", "m3": "Killed"}


@pytest.mark.parametrize("stage", [CppStage.LEAK, CppStage.PLAIN])
def test_a_leg_sweeps_its_tree_alone_and_is_its_own_binding(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, stage: CppStage
) -> None:
    """A leg sweeps one tree, reports as ``cpp-<leg>``, and writes no merged report."""
    swept: list[str] = []
    _fake_sweeps(monkeypatch, swept)
    _stage(monkeypatch, stage.value)
    report = run_cpp(tmp_path)
    assert swept == [stage.value]
    assert report.error is None
    assert report.binding == leg_binding(stage)
    assert report.survived == len(_SURVIVORS[stage.value])
    assert not (tmp_path / "cpp-mull.json").exists()
    assert (tmp_path / f"cpp-mull-{stage.value}.json").is_file()


def test_a_leg_is_recorded_and_never_judged() -> None:
    """A leg's survivors exceed the baseline and the verdict is still not a regression."""
    report = mutation_run.MutationReport(leg_binding(CppStage.LEAK), "mull", 1, 2, "")
    bindings: dict[str, mutation_run.BindingSpec] = {"cpp": {"baseline": {"survivors": 0}}}
    verdict = mutation_run.drift_for(report, bindings)
    assert verdict == {"status": "leg", "observed_survivors": 2}
    assert is_cpp_leg(report.binding)
    assert not is_cpp_leg("cpp")
    assert not is_cpp_leg(leg_binding(CppStage.MERGE))


def test_a_leg_that_did_not_build_is_an_error() -> None:
    """A leg's pass means the tree built and swept; a failure is an error, not a leg."""
    report = mutation_run.MutationReport(leg_binding(CppStage.PLAIN), "mull", 0, 0, "", error="x")
    assert mutation_run.drift_for(report, {})["status"] == "error"


def test_a_stage_that_is_no_stage_is_an_error(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A misspelt stage fails the run rather than sweeping nothing."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, "leaks")
    report = run_cpp(tmp_path)
    assert report.error is not None
    assert CPP_STAGE_ENV in report.error
    assert "leak, plain, merge" in report.error


def _leg_summary(commit: str, stage: CppStage, elapsed: float) -> str:
    return json.dumps(
        {
            "commit": commit,
            "elapsed_s": {"cpp": elapsed},
            "runs": [{"binding": leg_binding(stage), "tool": "mull"}],
        }
    )


def _download(legs_dir: Path, *stages: CppStage, commit: str = _SHA) -> None:
    """Lay the legs' artifacts out the way the download does: one directory per leg."""
    for stage in stages:
        leg_dir = legs_dir / f"mutation-cpp-{stage.value}" / commit
        leg_dir.mkdir(parents=True)
        _ = _write_lane_reports(leg_dir, stage.value)
        _ = (leg_dir / "summary.json").write_text(_leg_summary(commit, stage, 100.0 + len(stage)))


def _merge(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> mutation_run.MutationReport:
    """Run the merge stage over ``tmp_path / legs`` into ``tmp_path / out``."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, CppStage.MERGE.value)
    monkeypatch.setenv(CPP_LEGS_ENV, str(tmp_path / "legs"))
    out = tmp_path / "out"
    out.mkdir(exist_ok=True)
    return run_cpp(out)


def test_the_merge_of_the_legs_is_the_one_process_run(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Two legs merged read exactly what one process sweeping both trees reads."""
    _download(tmp_path / "legs", CppStage.LEAK, CppStage.PLAIN)
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
    for name in ("cpp-mull.json", "cpp-routes.json"):
        assert (tmp_path / "out" / name).read_text() == (whole / name).read_text()
    legs = json.loads((tmp_path / "out" / "cpp-legs.json").read_text())
    assert legs == {"leak": 104.0, "plain": 105.0}
    assert mutation_run.drift_for(merged, {"cpp": {"baseline": {"survivors": 1}}})["status"] == "ok"


def test_the_merge_refuses_a_missing_leg(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """One leg's reports are no verdict: the other tree may have killed what it let live."""
    _download(tmp_path / "legs", CppStage.LEAK)
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert "plain leg: 0 copies of cpp-mull-plain.json" in merged.error


def test_the_merge_refuses_a_doubled_leg(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """Two copies of one tree's report is a download that cannot be trusted."""
    _download(tmp_path / "legs", CppStage.LEAK, CppStage.PLAIN)
    _download(tmp_path / "legs" / "again", CppStage.PLAIN)
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert "2 copies of cpp-mull-plain.json" in merged.error


def test_the_merge_refuses_a_leg_of_another_commit(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A leg swept at another commit merges into a verdict about nothing."""
    _download(tmp_path / "legs", CppStage.LEAK)
    _download(tmp_path / "legs", CppStage.PLAIN, commit="othersha")
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert "is a run at othersha, this merge is at testsha" in merged.error


def test_the_merge_refuses_a_leg_without_its_summary(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The summary carries the leg's commit and wall clock; without it the leg is not one."""
    _download(tmp_path / "legs", CppStage.LEAK, CppStage.PLAIN)
    (tmp_path / "legs" / "mutation-cpp-plain" / _SHA / "summary.json").unlink()
    merged = _merge(monkeypatch, tmp_path)
    assert merged.error is not None
    assert "no summary of the plain leg" in merged.error


def test_the_merge_needs_the_legs_directory(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The merge stage without a legs directory is a misconfigured job, and says so."""
    _fake_sweeps(monkeypatch, [])
    _stage(monkeypatch, CppStage.MERGE.value)
    monkeypatch.delenv(CPP_LEGS_ENV, raising=False)
    merged = run_cpp(tmp_path)
    assert merged.error is not None
    assert CPP_LEGS_ENV in merged.error
