# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the sweep a ``tools.run_ci.Runner`` runs: its exit code, its record.

A failing step MUST make ``run()`` return 1 (never a silent green), a ``build``
failure MUST short-circuit the sweep, and serial and parallel modes must agree
on pass/fail.  A full sweep records the build sources it observed and the tree
it swept, exports the digest to its steps, and vouches for neither once they
moved under it; a sweep of a subset vouches for nothing.  Each step's command
is answered in-process by a stand-in (``_step_runs``) and the sweep's measures
are read from the scratch tree's files (``_ci_runner``): no real gates, no
timing asserts.
"""

from __future__ import annotations

import os
from dataclasses import replace
from typing import TYPE_CHECKING

from _ci_runner import EXIT_0, EXIT_1, ci_runner, exits, measured_in_process, tree_of
from _executors import DrivenExecutor
from _processes import CommandWord
from _step_runs import Answer, StepCall, ends, install, passes

from tools.check_gate_claim import SOURCES_ENV, SOURCES_LINE, SOURCES_UNRECORDED, evidence_for
from tools.run_ci import LaneName, Runner
from tools.sweep_evidence import (
    TREE_LINE,
    TREE_MOVED,
    TREE_UNRECORDED_SUBSET,
    TREE_UNRECORDED_UNTRACKED,
)
from tools.sweep_evidence import evidence_for as tree_evidence_for

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

    from tools._common import WorkerCount


def test_all_pass_returns_zero(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Every step passing ⇒ exit code 0."""
    runs = exits(monkeypatch)
    runner = ci_runner(tmp_path)
    runner.step("a", EXIT_0, lane="x")
    runner.step("b", EXIT_0, lane="y")
    assert runner.run() == 0
    assert runs.commands == [EXIT_0, EXIT_0]


def test_failure_returns_one(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A single failing step ⇒ exit code 1 (no silent green)."""
    _ = exits(monkeypatch)
    runner = ci_runner(tmp_path)
    runner.step("ok", EXIT_0, lane="x")
    runner.step("bad", EXIT_1, lane="y")
    assert runner.run() == 1


def test_build_failure_short_circuits(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A failing ``build`` aborts the sweep before any lane runs."""
    after = CommandWord("echo SHOULD_NOT_RUN; exit 0")
    measured_in_process(monkeypatch)
    runs = install(
        monkeypatch,
        {EXIT_1: ends(ExitStatus(1)), after: ends(ExitStatus(0), Prose("SHOULD_NOT_RUN\n"))},
    )
    runner = ci_runner(tmp_path)
    runner.step("build", EXIT_1, lane="agda")
    runner.step("after", after, lane="x")
    assert runner.run() == 1
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert "SHOULD_NOT_RUN" not in log  # the post-build step never executed
    assert runs.commands == [EXIT_1]


def test_parallel_mode_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Parallel mode returns 0 when every lane passes."""
    runs = exits(monkeypatch)
    runner = ci_runner(tmp_path, parallel=True)
    runner.step("a", EXIT_0, lane="x")
    runner.step("b", EXIT_0, lane="y")
    assert runner.run(executor=DrivenExecutor) == 0
    assert runs.commands == [EXIT_0, EXIT_0]


def test_parallel_mode_surfaces_failure(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Parallel mode still returns 1 when any lane fails."""
    boom = CommandWord("exit 5")
    measured_in_process(monkeypatch)
    _ = install(monkeypatch, {EXIT_0: passes, boom: ends(ExitStatus(5))})
    runner = ci_runner(tmp_path, parallel=True)
    runner.step("a", EXIT_0, lane="x")
    runner.step("boom", boom, lane="y")
    assert runner.run(executor=DrivenExecutor) == 1


def test_parallel_mode_runs_its_lanes_on_the_executor_handed_in(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Parallel lanes run on what the caller's executor factory builds, one executor a sweep."""
    built: list[DrivenExecutor] = []

    def build(workers: WorkerCount) -> DrivenExecutor:
        built.append(DrivenExecutor(workers))
        return built[-1]

    _ = exits(monkeypatch)
    runner = ci_runner(tmp_path, parallel=True)
    runner.step("a", EXIT_0, lane="x")
    runner.step("b", EXIT_0, lane="y")
    assert runner.run(executor=build) == 0
    assert len(built) == 1


def _prints_the_exported_sources(_call: StepCall) -> Answer:
    """Stand in for ``echo seen=$ALETHEIA_GATE_SOURCES``: a step inherits the sweep's export."""
    return Answer(ExitStatus(0), Prose(f"seen={os.environ.get(SOURCES_ENV, '')}\n"))


def _prints_the_exported_sources_bracketed(_call: StepCall) -> Answer:
    """Stand in for ``echo seen=[$ALETHEIA_GATE_SOURCES]``, which shows an empty value."""
    return Answer(ExitStatus(0), Prose(f"seen=[{os.environ.get(SOURCES_ENV, '')}]\n"))


def test_a_full_sweep_records_and_exports_the_sources_it_observes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The header carries the digest, every step sees it, and the export is undone.

    The gate-claim enforcer runs inside the sweep, before any log of it is
    finished, so the export is the only way it can learn which tree the sweep
    observes; the header is what it reads once the log is finished.
    """
    monkeypatch.delenv(SOURCES_ENV, raising=False)
    observe = CommandWord(f"echo seen=${SOURCES_ENV}")
    measured_in_process(monkeypatch)
    _ = install(monkeypatch, {observe: _prints_the_exported_sources})
    runner = ci_runner(tmp_path)
    runner.step("observe", observe, lane="x")
    assert runner.run() == 0
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert f"{SOURCES_LINE}{runner.ctx.sources}\n" in log
    assert f"seen={runner.ctx.sources}" in log
    assert SOURCES_ENV not in os.environ


def test_a_full_sweep_that_passed_is_read_back_as_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The log a passing sweep leaves is one the enforcer accepts for its digest.

    The writer and the reader are pinned to each other here: a summary line
    reworded on one side without the other is a sweep whose evidence nothing
    can read.
    """
    monkeypatch.delenv(SOURCES_ENV, raising=False)
    _ = exits(monkeypatch)
    runner = ci_runner(tmp_path)
    runner.step("a", EXIT_0, lane="x")
    assert runner.run() == 0
    assert evidence_for(runner.ctx.sources, log_dir=tmp_path, environ={}) is not None
    assert evidence_for("0" * 64, log_dir=tmp_path, environ={}) is None


def test_a_fast_sweep_records_no_sources_and_exports_none(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A fast-tier sweep runs a subset, so its passing log vouches for no tree."""
    monkeypatch.setenv(SOURCES_ENV, "stale-from-a-caller")
    observe = CommandWord(f"echo seen=[${SOURCES_ENV}]")
    measured_in_process(monkeypatch)
    _ = install(monkeypatch, {observe: _prints_the_exported_sources_bracketed})
    runner = ci_runner(tmp_path, fast=True)
    runner.step("observe", observe, lane="x")
    assert runner.run() == 0
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert f"{SOURCES_LINE}{SOURCES_UNRECORDED}\n" in log
    assert "seen=[]" in log
    assert os.environ[SOURCES_ENV] == "stale-from-a-caller"
    assert evidence_for(runner.ctx.sources, log_dir=tmp_path, environ={}) is None


def test_a_lane_sweep_records_no_sources_and_exports_none(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A sweep of some lanes runs a subset, so its passing log vouches for no tree."""
    monkeypatch.setenv(SOURCES_ENV, "stale-from-a-caller")
    observe = CommandWord(f"echo seen=[${SOURCES_ENV}]")
    measured_in_process(monkeypatch)
    _ = install(monkeypatch, {observe: _prints_the_exported_sources_bracketed})
    runner = ci_runner(tmp_path, only_lanes=(LaneName("x"),))
    runner.step("observe", observe, lane="x")
    assert runner.run() == 0
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert f"{SOURCES_LINE}{SOURCES_UNRECORDED}\n" in log
    assert "Lanes:    x\n" in log
    assert "seen=[]" in log
    assert evidence_for(runner.ctx.sources, log_dir=tmp_path, environ={}) is None


def test_a_sweep_whose_sources_moved_under_it_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Every step passed, but a build source changed meanwhile: no record, exit 1."""
    monkeypatch.delenv(SOURCES_ENV, raising=False)
    edit = CommandWord("mkdir -p src && echo 'module A where' > src/A.agda")

    def writes_a_module(call: StepCall) -> Answer:
        assert call.cwd == tmp_path
        module = tmp_path / "src" / "A.agda"
        module.parent.mkdir(parents=True, exist_ok=True)
        _ = module.write_text("module A where\n", encoding="utf-8")
        return Answer(ExitStatus(0))

    measured_in_process(monkeypatch)
    _ = install(monkeypatch, {edit: writes_a_module})
    runner = ci_runner(tmp_path)
    runner.step("edit", edit, cwd=tmp_path, lane="x")
    assert runner.run() == 1
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert "build sources moved during the sweep" in log
    assert evidence_for(runner.ctx.sources, log_dir=tmp_path, environ={}) is None


def _tree_runner(tmp_path: Path, *, fast: bool = False) -> Runner:
    """Build a Runner over a tree whose one tracked file is ``a.txt``, its tree named.

    The log lands beside the file and is no part of the tree ``tree_of``
    names, as an ignored file is no part of the one git writes.
    """
    _ = (tmp_path / "a.txt").write_text("one\n", encoding="utf-8")
    runner = ci_runner(tmp_path, fast=fast)
    return Runner(runner.opts, replace(runner.ctx, tree=tree_of(tmp_path)))


def test_a_full_sweep_records_the_tree_it_swept_and_reads_back_as_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The header and the summary name the tree, and the log vouches for it to a push."""
    _ = exits(monkeypatch)
    runner = _tree_runner(tmp_path)
    tree = runner.ctx.tree
    assert tree is not None
    runner.step("a", EXIT_0, lane="x")
    assert runner.run() == 0
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert log.count(f"{TREE_LINE}{tree}\n") == len(("header", "summary"))
    assert tree_evidence_for(tree, tmp_path) == tmp_path / "ci.log"


def test_a_tree_that_moved_under_the_sweep_is_recorded_as_moved(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A step that edits a tracked file leaves a summary that vouches for no tree."""
    edit = CommandWord("echo two > a.txt")

    def edits_the_tracked_file(call: StepCall) -> Answer:
        assert call.cwd == tmp_path
        _ = (tmp_path / "a.txt").write_text("two\n", encoding="utf-8")
        return Answer(ExitStatus(0))

    measured_in_process(monkeypatch)
    _ = install(monkeypatch, {edit: edits_the_tracked_file})
    runner = _tree_runner(tmp_path)
    tree = runner.ctx.tree
    assert tree is not None
    runner.step("edit", edit, cwd=tmp_path, lane="x")
    assert runner.run() == 0
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert f"{TREE_LINE}{TREE_MOVED}\n" in log
    assert tree_evidence_for(tree, tmp_path) is None


def test_an_untracked_file_or_a_subset_sweep_records_no_tree(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A file no gate lists makes the sweep vouch for no tree, and so does the fast tier."""
    _ = exits(monkeypatch)
    (tmp_path / "untracked").mkdir()
    untracked = ci_runner(tmp_path / "untracked")
    untracked.step("a", EXIT_0, lane="x")
    assert untracked.run() == 0
    log = (tmp_path / "untracked" / "ci.log").read_text(encoding="utf-8")
    assert f"{TREE_LINE}{TREE_UNRECORDED_UNTRACKED}\n" in log
    (tmp_path / "fast").mkdir()
    fast = _tree_runner(tmp_path / "fast", fast=True)
    fast.step("a", EXIT_0, lane="x")
    assert fast.run() == 0
    log = (tmp_path / "fast" / "ci.log").read_text(encoding="utf-8")
    assert f"{TREE_LINE}{TREE_UNRECORDED_SUBSET}\n" in log
