# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._scheduler`` — lane-parallel gate scheduling.

The logic tests answer each step's command in-process by a stand-in
(``_step_runs``), which records what the scheduler asked to run, so they hold:
the property a gate orchestrator must never get wrong — **no failure is
silently dropped** — plus lane fail-fast, cross-lane independence, a signal
death's status counted as a failure, output kept with its step, and
deterministic result ordering.  The tests that run real steps, over a stand-in
``cabal`` (``_stand_in``), hold what only processes show: once a sweep is
interrupted or killed, the steps it runs and the builds they start stop, and
the lock a build held frees.
"""

from __future__ import annotations

import os
import signal
from functools import partial
from pathlib import Path

import pytest
from _executors import DrivenExecutor, Order
from _processes import CommandWord
from _stand_in import ScriptSource, driving_a_held_build, stopped
from _step_runs import NO_OUTPUT, Answer, Descriptor, StandIn, StepCall, ends, install, passes

from tools._determinism_guard import Clock, Seconds
from tools._scheduler import Step, StepEvent, all_passed, run_lanes

from aletheia.common_types import ExitStatus, Prose

A1, A2, B1 = CommandWord("a1"), CommandWord("a2"), CommandWord("b1")
FIRST, BOOM, OOM = CommandWord("first"), CommandWord("boom"), CommandWord("oom")


def _step(command: CommandWord, *, heavy: bool = False) -> Step:
    """Build a step named by its command text, so each stand-in answers one step."""
    return Step(name=command, cmd=command, heavy=heavy)


def _table(**stand_ins: StandIn) -> dict[CommandWord, StandIn]:
    """Key each stand-in by the command text its keyword names."""
    return {CommandWord(command): stand_in for command, stand_in in stand_ins.items()}


def test_all_pass_collects_every_step(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every step of every lane is run and collected when all succeed."""
    runs = install(monkeypatch, _table(a1=passes, a2=passes, b1=passes))
    lanes = [[_step(A1), _step(A2)], [_step(B1)]]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1, executor=DrivenExecutor)
    assert all_passed(results)
    assert {r.name for r in results} == {"a1", "a2", "b1"}
    assert runs.commands == [A1, A2, B1]


def test_failure_surfaces_with_real_returncode(monkeypatch: pytest.MonkeyPatch) -> None:
    """A failing step makes the run fail and keeps its real exit code."""
    _ = install(monkeypatch, _table(ok=passes, bad=ends(ExitStatus(3))))
    lanes = [[_step(CommandWord("ok"))], [_step(CommandWord("bad"))]]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1, executor=DrivenExecutor)
    assert not all_passed(results)
    bad = next(r for r in results if r.name == "bad")
    assert bad.returncode == 3


def test_lane_fail_fast_skips_dependents(monkeypatch: pytest.MonkeyPatch) -> None:
    """Within a lane, steps after a failure are skipped (they depend on it)."""
    runs = install(monkeypatch, _table(first=passes, boom=ends(ExitStatus(1)), after=passes))
    lanes = [[_step(FIRST), _step(BOOM), _step(CommandWord("after"))]]
    results = run_lanes(lanes, max_workers=1, heavy_limit=1, executor=DrivenExecutor)
    assert [r.name for r in results] == ["first", "boom"]  # "after" skipped
    assert not all_passed(results)
    assert runs.commands == [FIRST, BOOM]  # "after" never ran


def test_one_lane_failure_does_not_abort_siblings(monkeypatch: pytest.MonkeyPatch) -> None:
    """A failing lane never drops sibling lanes — run_lanes awaits every future.

    This is the failing-step-finishes-first / no-silent-drop guarantee: the
    result set always contains every sibling step regardless of completion order.
    """
    _ = install(monkeypatch, _table(fail=ends(ExitStatus(7)), sib1=passes, sib2=passes))
    lanes = [
        [_step(CommandWord("fail"))],
        [_step(CommandWord("sib1")), _step(CommandWord("sib2"))],
    ]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1, executor=DrivenExecutor)
    assert {r.name for r in results} == {"fail", "sib1", "sib2"}
    assert not all_passed(results)


def test_signal_death_counts_as_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    """A SIGKILL's status (the OOM-killer signature) is a failure, and its lane stops there."""
    killed = ExitStatus(128 + signal.SIGKILL)  # the status the guard reports for a signal death
    runs = install(monkeypatch, _table(oom=ends(killed), next=passes))
    lanes = [[_step(OOM), _step(CommandWord("next"))]]
    results = run_lanes(lanes, max_workers=1, heavy_limit=1, executor=DrivenExecutor)
    assert not all_passed(results)
    assert results[0].returncode == killed
    assert runs.commands == [OOM]


# A sweep of two lanes run in parallel, one of them a step running the build.
_PARALLEL = ScriptSource(
    "from tools._scheduler import Step, run_lanes; "
    + "run_lanes([[Step('build', 'cabal run shake -- build')], [Step('other', 'true')]], "
    + "max_workers=2, heavy_limit=1)"
)


@pytest.mark.process(
    "an interrupt reaches a sweep through its process group, and only real processes show"
    + " the sweep stopping steps that run in groups of their own"
)
def test_an_interrupted_parallel_sweep_stops_its_steps(tmp_path: Path) -> None:
    """Ctrl-C, SIGINT to the sweep's process group, ends a parallel sweep, its steps and builds.

    Each step runs in a process group of its own, which the interrupt does
    not reach, and the build blocks until something stops it, so a sweep that
    only waited on its workers would never return.  A stop that reached the
    step's shell but not the build it waits on would leave the lock held.
    """
    with driving_a_held_build(tmp_path, _PARALLEL, own_group=True) as build:
        os.killpg(build.driver.pid, signal.SIGINT)
        assert build.driver.wait() != 0
        stopped(build.lock)


@pytest.mark.process(
    "an interrupt reaches a sweep through its process group, and only real processes show"
    + " the serial sweep's step stopping when the interrupt leaves the wait on it"
)
def test_an_interrupted_serial_sweep_stops_its_step(tmp_path: Path) -> None:
    """Ctrl-C ends a serial sweep and its build, though the serial path gives steps no stop pipe.

    The interrupt lands in the wait on the step, on the calling thread, and
    reaches the step only through its guard, whose watch pipe the sweep's
    leaving closes.
    """
    serial = ScriptSource(
        "from tools._scheduler import Step, run_lanes; "
        + "run_lanes([[Step('build', 'cabal run shake -- build')]], "
        + "max_workers=1, heavy_limit=1, executor=None)"
    )
    with driving_a_held_build(tmp_path, serial, own_group=True) as build:
        os.killpg(build.driver.pid, signal.SIGINT)
        assert build.driver.wait() != 0
        stopped(build.lock)


@pytest.mark.process(
    "SIGKILL ends the sweep without running any of its code, and only the kernel closing"
    + " its pipe ends shows the guards stopping the steps"
)
def test_a_killed_sweep_stops_its_steps(tmp_path: Path) -> None:
    """A sweep killed outright, SIGKILL included, stops the build a step runs."""
    with driving_a_held_build(tmp_path, _PARALLEL) as build:
        build.driver.kill()
        _ = build.driver.wait()
        stopped(build.lock)


@pytest.mark.process(
    "a step that runs its own build under a guard puts it in a process group of its own,"
    + " which only real processes show the killed sweep's guard reaching in turn"
)
def test_a_killed_sweep_stops_a_step_that_guards_its_own_build(tmp_path: Path) -> None:
    """A killed sweep stops a build its step guards itself, as the staleness gate's step does.

    This holds that the build stops, not by which path: were the inner guard
    never told, the outer guard's SIGKILL of the step, after its grace period,
    would close the inner guard's pipe all the same.  The guard's own tests
    hold the path an exception takes out of ``run_guarded``.
    """
    nested = ScriptSource(
        "import sys; from tools._scheduler import Step, run_lanes; "
        + "run_lanes([[Step('build', [sys.executable, '-c', "
        + "'from tools.check_build_incremental import _build; _build()'])], "
        + "[Step('other', 'true')]], max_workers=2, heavy_limit=1)"
    )
    with driving_a_held_build(tmp_path, nested) as build:
        build.driver.kill()
        _ = build.driver.wait()
        stopped(build.lock)


def test_each_step_keeps_its_own_output_whole(monkeypatch: pytest.MonkeyPatch) -> None:
    """Each step's merged output lands, whole and alone, in that step's result."""
    noisy, mixed = Prose("MARKER_42\n"), Prose("one\ntwo\nthree\n")
    _ = install(
        monkeypatch,
        _table(noisy=ends(ExitStatus(0), noisy), mixed=ends(ExitStatus(0), mixed)),
    )
    lanes = [[_step(CommandWord("noisy"))], [_step(CommandWord("mixed"))]]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1, executor=DrivenExecutor)
    assert [(r.name, r.output) for r in results] == [("noisy", noisy), ("mixed", mixed)]


def test_serial_mode_runs_every_lane(monkeypatch: pytest.MonkeyPatch) -> None:
    """The serial fallback still runs and collects every lane, with no stop descriptor."""
    runs = install(monkeypatch, _table(a=passes, b=passes))
    lanes = [[_step(CommandWord("a"))], [_step(CommandWord("b"))]]
    results = run_lanes(lanes, max_workers=4, heavy_limit=1, executor=None)
    assert all_passed(results)
    assert {r.name for r in results} == {"a", "b"}
    assert [call.stop_fd for call in runs.calls] == [None, None]


def test_results_ordered_by_lane_not_completion(monkeypatch: pytest.MonkeyPatch) -> None:
    """Results come back in lane-then-step order when the last lane finishes first."""
    runs = install(monkeypatch, _table(a1=passes, a2=passes, b1=passes))
    lanes = [[_step(A1), _step(A2)], [_step(B1)]]
    events: list[StepEvent] = []
    results = run_lanes(
        lanes,
        max_workers=2,
        heavy_limit=1,
        progress=events.append,
        executor=partial(DrivenExecutor, order=Order.LAST_SUBMITTED),
    )
    assert [e.name for e in events if e.phase == "done"] == ["b1", "a1", "a2"]
    assert [r.name for r in results] == ["a1", "a2", "b1"]
    assert runs.commands == [B1, A1, A2]


def test_heavy_steps_execute_under_the_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    """Heavy steps run and are captured (the bound is the Semaphore's contract)."""
    heavy = Prose("HEAVY\n")
    runs = install(monkeypatch, _table(h1=passes, h2=ends(ExitStatus(0), heavy)))
    lanes = [
        [_step(CommandWord("h1"), heavy=True)],
        [_step(CommandWord("h2"), heavy=True)],
    ]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1, executor=DrivenExecutor)
    assert all_passed(results)
    assert [r.output for r in results] == [NO_OUTPUT, heavy]
    assert runs.commands == ["h1", "h2"]


def test_progress_observes_start_and_done_per_step(monkeypatch: pytest.MonkeyPatch) -> None:
    """The live channel fires a start and a done event for every executed step.

    Within a lane the order is start→done per step in lane order, each step
    running between its own two events; the done event carries the step's
    real result (the fail case pins the exit code).
    """
    events: list[StepEvent] = []

    def runs_after_its_start(status: ExitStatus) -> StandIn:
        def answer(call: StepCall) -> Answer:
            assert events[-1] == StepEvent("start", call.command), events
            return Answer(status)

        return answer

    _ = install(
        monkeypatch,
        _table(first=runs_after_its_start(ExitStatus(0)), boom=runs_after_its_start(ExitStatus(4))),
    )
    lanes = [[_step(FIRST), _step(BOOM)]]
    results = run_lanes(
        lanes, max_workers=1, heavy_limit=1, progress=events.append, executor=DrivenExecutor
    )
    assert not all_passed(results)
    assert [(e.phase, e.name) for e in events] == [
        ("start", "first"),
        ("done", "first"),
        ("start", "boom"),
        ("done", "boom"),
    ]
    done_boom = events[-1]
    assert done_boom.result is not None
    assert done_boom.result.returncode == 4
    assert events[0].result is None  # a start event carries no outcome yet


def test_a_step_reports_the_time_the_clock_moved_while_it_ran(
    clock: Clock, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A step's duration is what the clock read between its start and its end, and nothing else."""

    def observe(event: StepEvent) -> None:
        if event.phase == "start":
            clock.advance(Seconds(3.0))

    _ = install(monkeypatch, _table(timed=passes))
    (result,) = run_lanes(
        [[_step(CommandWord("timed"))]],
        max_workers=1,
        heavy_limit=1,
        progress=observe,
        executor=None,
    )
    assert result.duration == 3.0


def test_progress_none_is_supported(monkeypatch: pytest.MonkeyPatch) -> None:
    """The default (no observer) runs exactly as before — the seam is optional."""
    runs = install(monkeypatch, _table(quiet=passes))
    results = run_lanes(
        [[_step(CommandWord("quiet"))]], max_workers=1, heavy_limit=1, executor=DrivenExecutor
    )
    assert all_passed(results)
    assert runs.commands == ["quiet"]


def test_a_parallel_sweep_leaves_no_descriptor_open(monkeypatch: pytest.MonkeyPatch) -> None:
    """Both ends of the parallel sweep's stop pipe are closed once it returns.

    Each step is handed the pipe's read end while it runs, which shows the
    pipe this test sees closed is the one the sweep made.
    """
    fds = Path("/proc/self/fd")
    open_while_running: list[Descriptor] = []

    def watch(call: StepCall) -> Answer:
        assert call.stop_fd is not None
        if (fds / str(call.stop_fd)).exists():
            open_while_running.append(call.stop_fd)
        return Answer(ExitStatus(0))

    runs = install(monkeypatch, _table(a=watch, b=watch))
    before = sorted(fds.iterdir())
    _ = run_lanes(
        [[_step(CommandWord("a"))], [_step(CommandWord("b"))]],
        max_workers=2,
        heavy_limit=1,
        executor=DrivenExecutor,
    )
    assert sorted(fds.iterdir()) == before
    stop_fds = [call.stop_fd for call in runs.calls]
    assert open_while_running == stop_fds
    assert len(set(stop_fds)) == 1
