# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the sweep a ``tools.run_ci.Runner`` runs: its exit code, its record.

A failing step MUST make ``run()`` return 1 (never a silent green), a failure,
the ``build``'s included, stops only the steps that need the failed one, each
named and counted as not run, and serial and parallel modes must agree on
pass/fail.  A full sweep records the build sources it observed and the tree it
swept, exports the digest to its steps, and vouches for neither once they moved
under it; a sweep of a subset vouches for nothing.  Its log lands in the
records directory ``tools._records`` names, made when absent, and a relative
one refuses the sweep before git is asked for the branch or the commit.  Each
step's command is answered in-process by a stand-in (``_step_runs``), and the
sweep's measures are read from the scratch tree's files (``_ci_runner``) or,
where a test discovers a checkout, planted (``_plant_discovery``): no real
gates, and no clock but the suite's, which only a test moves.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
from dataclasses import replace
from typing import TYPE_CHECKING, NamedTuple

import pytest
from _ci_runner import (
    EXIT_0,
    EXIT_1,
    SourcesDigest,
    ci_runner,
    exits,
    measured_in_process,
    tree_of,
)
from _executors import DrivenExecutor
from _processes import CommandWord
from _step_runs import Answer, StepCall, ends, install, passes

from tools import run_ci
from tools._common import EnvName, EnvValue, GateName
from tools._determinism_guard import Clock, Seconds
from tools._records import records_dir
from tools._run_ci_options import LaneName, OptInOptions
from tools._scheduler import step_file
from tools._watchdog import PatternText, Progress
from tools._watchdog import Seconds as WatchSeconds
from tools.check_gate_claim import SOURCES_ENV, SOURCES_LINE, SOURCES_UNRECORDED, evidence_for
from tools.run_ci import RunContext, Runner
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

    from tools._common import WorkerCount
    from tools.commit_subjects import GitArg
    from tools.sweep_evidence import TreeId

# A step command whose output and status each test installs.
_WRITES = CommandWord("writes")

# The variable naming the records directory, spelled as the workflows set it.
_RECORDS_ENV = EnvName("ALETHEIA_CI_OUTPUT")


def test_the_header_names_where_steps_write_and_a_failure_s_tail_names_its_file(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The header names the directory steps write into; a failed step's tail names its file."""
    runner = ci_runner(tmp_path)
    live = step_file(runner.steps_dir, GateName("a"))
    _ = install(monkeypatch, {_WRITES: ends(ExitStatus(1), Prose("compiling module 3 of 9\n"))})
    runner.step("a", _WRITES, lane="x")
    assert runner.run() == 1
    printed = capsys.readouterr()
    assert f"Outputs:  {runner.steps_dir}/<step>.log, written as each step runs" in printed.out
    assert f"─── tail of failed step output (the whole of it: {live}) ───" in printed.err
    assert live.read_text(encoding="utf-8") == "compiling module 3 of 9\n"


def test_a_step_s_quarter_reports_are_shown_and_a_stall_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A report passing a new quarter of the work, short of the whole, is shown.

    A step the watchdog stopped is named so.
    """
    counted = Progress(PatternText(r"\[(?P<done>\d+)/(?P<total>\d+)\]"), WatchSeconds(600.0))

    def declared(_name: GateName) -> Progress:
        return counted

    monkeypatch.setattr(run_ci, "progress_of", declared)
    reports = Prose("".join(f"[{k}/100]\n" for k in (10, 30, 60, 100)))
    stalls = Answer(ExitStatus(0), Prose("[1/9]\n"), stalled=True)
    _ = install(monkeypatch, {_WRITES: ends(ExitStatus(0), reports), EXIT_1: lambda _c: stalls})
    runner = ci_runner(tmp_path)
    runner.step("a", _WRITES, lane="x")
    runner.step("b", EXIT_1, lane="y")
    assert runner.run() == 1
    err = capsys.readouterr().err
    assert "  ⋯ a: [30/100]\n  ⋯ a: [60/100]\n" in err
    assert "[10/100]" not in err
    assert "[100/100]" not in err
    assert "  ✗ b FAILED (stopped by the watchdog, no progress report, exit 1, 0s)" in err


def test_a_step_the_watchdog_fails_for_making_no_report_is_named_so(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    clock: Clock,
) -> None:
    """A step declaring reports that exits 0 after 11 s with none fails, its line saying why."""
    counted = Progress(PatternText(r"\[(?P<done>\d+)/(?P<total>\d+)\]"))

    def declared(_name: GateName) -> Progress:
        return counted

    def quiet(_call: StepCall) -> Answer:
        clock.advance(Seconds(11.0))
        return Answer(ExitStatus(0), Prose("compiling\n"))

    monkeypatch.setattr(run_ci, "progress_of", declared)
    _ = install(monkeypatch, {_WRITES: quiet})
    runner = ci_runner(tmp_path)
    runner.step("q", _WRITES, lane="x")
    assert runner.run() == 1
    err = capsys.readouterr().err
    assert "  ✗ q FAILED (failed by the watchdog, no progress report, exit 0, 11s)" in err


def test_what_the_watchdog_measured_of_each_step_is_recorded_beside_the_step_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, clock: Clock
) -> None:
    """``progress.json`` holds each step that ran: run time, reports, longest quiet, stalled.

    A step failing by its own exit is no stalled one.
    """
    counted = Progress(PatternText(r"\[(?P<done>\d+)/(?P<total>\d+)\]"), WatchSeconds(600.0))
    fails = CommandWord("fails")

    def declared(_name: GateName) -> Progress:
        return counted

    def reports(_call: StepCall) -> Answer:
        clock.advance(Seconds(12.34))
        return Answer(ExitStatus(0), Prose("[1/2]\n[2/2]\n"), longest_quiet=WatchSeconds(4.56))

    stalls = Answer(
        ExitStatus(0), Prose("[1/9]\n"), stalled=True, longest_quiet=WatchSeconds(600.0)
    )
    monkeypatch.setattr(run_ci, "progress_of", declared)
    measured_in_process(monkeypatch)
    _ = install(
        monkeypatch, {_WRITES: reports, EXIT_1: lambda _c: stalls, fails: ends(ExitStatus(5))}
    )
    runner = ci_runner(tmp_path)
    runner.step("a", _WRITES, lane="x")
    runner.step("b", EXIT_1, lane="y")
    runner.step("c", EXIT_0, lane="y", needs=(GateName("b"),))
    runner.step("d", fails, lane="z")
    assert runner.run() == 1
    measured = json.loads((runner.steps_dir / "progress.json").read_text(encoding="utf-8"))
    assert measured == {
        "a": {"seconds": 12.3, "reports": 2, "longest_quiet": 4.6, "stalled": False},
        "b": {"seconds": 0.0, "reports": 1, "longest_quiet": 600.0, "stalled": True},
        "d": {"seconds": 0.0, "reports": 0, "longest_quiet": 0.0, "stalled": False},
    }


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


class SweepRun(NamedTuple):
    """What a sweep answered: its exit code and what it wrote to stderr."""

    code: ExitStatus
    stderr: Prose


def _run(runner: Runner) -> SweepRun:
    """Run the sweep, returning its exit code and what it wrote to stderr."""
    captured = io.StringIO()
    with contextlib.redirect_stderr(captured):
        code = ExitStatus(runner.run())
    return SweepRun(code, Prose(captured.getvalue()))


def test_a_build_failure_leaves_the_steps_that_do_not_need_it_running(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A failing ``build`` stops no step that does not need it, in any lane."""
    lint = CommandWord("echo LINTED; exit 0")
    measured_in_process(monkeypatch)
    runs = install(
        monkeypatch, {EXIT_1: ends(ExitStatus(1)), lint: ends(ExitStatus(0), Prose("LINTED\n"))}
    )
    runner = ci_runner(tmp_path)
    runner.step("build", EXIT_1, lane="agda")
    runner.step("lint", lint, lane="x")
    assert runner.run() == 1
    assert runs.commands == [EXIT_1, lint]
    assert "LINTED" in (tmp_path / "ci.log").read_text(encoding="utf-8")


def test_a_step_needing_the_failed_build_is_reported_not_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A step needing the build that failed runs nowhere and is named, with its need, everywhere.

    The live channel and the log each carry a line for it, and the summary
    names it with the step it needed.
    """
    uses = CommandWord("uses")
    measured_in_process(monkeypatch)
    runs = install(monkeypatch, {EXIT_1: ends(ExitStatus(1)), uses: passes})
    runner = ci_runner(tmp_path)
    runner.step("build", EXIT_1, lane="agda")
    runner.step("uses", uses, lane="x", needs=(GateName("build"),))
    run = _run(runner)
    assert run.code == 1
    assert runs.commands == [EXIT_1]
    assert "  ⊘ uses not run (needs build)\n" in run.stderr
    assert "Not run:  uses (needs build)\n" in run.stderr
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert "  ⊘ uses not run: it needs build, which did not pass\n" in log


def test_the_staleness_gate_runs_alone_after_the_lanes_and_hides_none_of_them(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The gate relinks the library, so it runs after every lane; its failure stops no step.

    A step reading the build's library runs on the plain build's verdict, so a
    staleness failure leaves it running, and the summary names the one failure.
    """
    plain, stale, uses = CommandWord("plain"), CommandWord("stale"), CommandWord("uses")
    measured_in_process(monkeypatch)
    runs = install(monkeypatch, {plain: passes, stale: ends(ExitStatus(1)), uses: passes})
    runner = ci_runner(tmp_path)
    runner.step("build", plain, lane="agda")
    runner.step("build staleness", stale, lane="agda", needs=(GateName("build"),))
    runner.step("uses", uses, lane="x", needs=(GateName("build"),))
    run = _run(runner)
    assert run.code == 1
    assert runs.commands == [plain, uses, stale]
    assert "Failed:   build staleness\n" in run.stderr


def test_the_lanes_are_logged_before_the_staleness_gate_runs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An interrupt during the staleness gate's relinks loses no lane's outcome from the log."""
    plain, uses = CommandWord("plain"), CommandWord("echo USED; exit 1")

    def interrupted(_call: StepCall) -> Answer:
        raise KeyboardInterrupt

    measured_in_process(monkeypatch)
    _ = install(
        monkeypatch,
        {
            plain: passes,
            uses: ends(ExitStatus(1), Prose("USED\n")),
            CommandWord("stale"): interrupted,
        },
    )
    runner = ci_runner(tmp_path)
    runner.step("build", plain, lane="agda")
    runner.step("build staleness", CommandWord("stale"), lane="agda", needs=(GateName("build"),))
    runner.step("uses", uses, lane="x", needs=(GateName("build"),))
    with pytest.raises(KeyboardInterrupt):
        _ = _run(runner)
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert "USED\n" in log
    assert "  ✗ uses FAILED (exit 1, 0s)\n" in log


def test_the_summary_counts_every_step_by_its_outcome(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A failed sweep's summary accounts for every step: passed, failed and not run sum to all."""
    _ = exits(monkeypatch)
    runner = ci_runner(tmp_path)
    runner.step("a", EXIT_0, lane="x")
    runner.step("b", EXIT_1, lane="x")
    runner.step("c", EXIT_0, lane="x")
    runner.step("d", EXIT_0, lane="y")
    run = _run(runner)
    assert run.code == 1
    assert "═══ CI FAILED — of 4 steps, 3 passed, 1 failed, 0 not run ═══\n" in run.stderr
    assert "Failed:   b\n" in run.stderr
    assert "Not run:" not in run.stderr


def test_the_summary_names_each_step_not_run_with_its_need(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A chain of needs below a failure is counted and named link by link."""
    _ = exits(monkeypatch)
    runner = ci_runner(tmp_path)
    runner.step("a", EXIT_1, lane="x")
    runner.step("b", EXIT_0, lane="x", needs=(GateName("a"),))
    runner.step("c", EXIT_0, lane="x", needs=(GateName("b"),))
    runner.step("d", EXIT_0, lane="y")
    run = _run(runner)
    assert run.code == 1
    assert "═══ CI FAILED — of 4 steps, 1 passed, 1 failed, 2 not run ═══\n" in run.stderr
    assert "Not run:  b (needs a), c (needs b)\n" in run.stderr


def test_a_sweep_whose_need_no_step_answers_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A step needing one its lane does not run first is refused before any step runs."""
    runs = exits(monkeypatch)
    runner = ci_runner(tmp_path)
    runner.step("a", EXIT_0, lane="x", needs=(GateName("b"),))
    runner.step("b", EXIT_0, lane="x")
    run = _run(runner)
    assert run.code == 2
    assert runs.commands == []
    assert (
        "run-ci: a needs b, which is neither the build nor an earlier step of its lane\n"
        in run.stderr
    )


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


def _plant_discovery(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Answer what discovering a checkout at ``tmp_path / "repo"`` asks of git.

    Git names branch and commit ``main``, the sources digest to zeros and no
    tree is named; the checkout is returned.
    """

    def answers(_root: Path, *_args: GitArg) -> Prose:
        return Prose("main")

    def digest(_root: Path | None = None) -> SourcesDigest:
        return SourcesDigest("0" * 64)

    def no_tree(_root: Path) -> TreeId | None:
        return None

    monkeypatch.setattr(run_ci, "_git_value", answers)
    monkeypatch.setattr(run_ci, "sources_digest_of_worktree", digest)
    monkeypatch.setattr(run_ci, "worktree_tree", no_tree)
    repo = tmp_path / "repo"
    repo.mkdir()
    return repo


def test_a_sweep_s_log_lands_in_the_records_directory_made_when_absent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Unset, the log goes beside the checkout; set, where the variable says; either made."""
    repo = _plant_discovery(tmp_path, monkeypatch)
    monkeypatch.delenv(_RECORDS_ENV, raising=False)
    beside = RunContext.discover(repo).log_path.parent
    assert beside == records_dir(repo, {})
    assert beside.is_dir()
    monkeypatch.setenv(_RECORDS_ENV, str(tmp_path / "set" / "deeper"))
    pointed = RunContext.discover(repo).log_path.parent
    assert pointed == tmp_path / "set" / "deeper"
    assert pointed.is_dir()


def test_a_relative_records_directory_refuses_the_sweep_before_git_is_asked_for_the_branch(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A relative ``ALETHEIA_CI_OUTPUT`` exits 2 naming it.

    Nothing is made, and git is asked for the checkout's root alone.
    """
    repo = _plant_discovery(tmp_path, monkeypatch)

    def asked(_root: Path, *args: GitArg) -> Prose:
        ran = f"git {' '.join(args)} ran before the refusal"
        raise AssertionError(ran)

    def checkout() -> Path:
        return repo

    monkeypatch.setattr(run_ci, "_git_value", asked)
    monkeypatch.setattr(run_ci, "_git_root", checkout)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv(_RECORDS_ENV, EnvValue("records"))
    assert run_ci.main([]) == 2
    out, err = capsys.readouterr()
    assert (out, err) == (
        "",
        "run-ci: ALETHEIA_CI_OUTPUT names 'records', a relative path;"
        + " it must name an absolute one\n",
    )
    assert not any(repo.iterdir())


def test_a_sweep_run_as_the_command_leaves_its_evidence_in_the_records_directory(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``python -m tools.run_ci`` writes the log a claim rests on where the variable points."""
    repo = _plant_discovery(tmp_path, monkeypatch)

    def one_step(runner: Runner, _cabal: list[CommandWord], _opts: OptInOptions) -> None:
        runner.step("a", EXIT_0, lane="x")

    def checkout() -> Path:
        return repo

    monkeypatch.setattr(run_ci, "register_all_steps", one_step)
    monkeypatch.setattr(run_ci, "_git_root", checkout)
    _ = install(monkeypatch, {EXIT_0: passes})
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv(SOURCES_ENV, raising=False)
    monkeypatch.delenv("ALETHEIA_CI_FAST", raising=False)
    monkeypatch.setenv(_RECORDS_ENV, str(tmp_path / "records"))
    assert run_ci.main(["--no-parallel"]) == 0
    assert evidence_for("0" * 64, log_dir=tmp_path / "records", environ={}) is not None
