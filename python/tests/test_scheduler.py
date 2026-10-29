# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._scheduler`` — lane-parallel gate scheduling.

The logic tests answer each step's command in-process by a stand-in
(``_step_runs``), which records what the scheduler asked to run, so they hold:
the property a gate orchestrator must never get wrong — **no failure is
silently dropped** — plus every step of a lane running unless a step it
needs did not pass, cross-lane independence, a signal death's status counted
as a failure, output kept with its step, and deterministic result ordering.
The tests that run real steps, over a stand-in
``cabal`` (``_stand_in``), hold what only processes show: once a sweep is
interrupted or killed, the steps it runs and the builds they start stop, and
the lock a build held frees.
"""

from __future__ import annotations

import os
import signal
from functools import partial
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _executors import DrivenExecutor, Order
from _processes import CommandWord
from _stand_in import ScriptSource, driving_a_held_build, stopped
from _step_runs import NO_OUTPUT, Answer, Descriptor, StandIn, StepCall, ends, install, passes

from tools._common import GateName
from tools._determinism_guard import Clock, Seconds
from tools._scheduler import (
    LaneContext,
    Step,
    StepEvent,
    StepNotRun,
    StepResult,
    all_passed,
    run_lane,
    run_lanes,
    unmet_needs,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Sequence

    from tools._scheduler import StepOutcome

A1, A2, B1 = CommandWord("a1"), CommandWord("a2"), CommandWord("b1")
FIRST, BOOM, OOM = CommandWord("first"), CommandWord("boom"), CommandWord("oom")
AFTER, USES, BUILD = CommandWord("after"), CommandWord("uses"), CommandWord("build")


def _step(
    command: CommandWord, *, heavy: bool = False, needs: tuple[CommandWord, ...] = ()
) -> Step:
    """Build a step named by its command text, so each stand-in answers one step."""
    return Step(name=command, cmd=command, heavy=heavy, needs=tuple(map(GateName, needs)))


def _table(**stand_ins: StandIn) -> dict[CommandWord, StandIn]:
    """Key each stand-in by the command text its keyword names."""
    return {CommandWord(command): stand_in for command, stand_in in stand_ins.items()}


def _not_run(step: CommandWord, needs: CommandWord) -> StepNotRun:
    """Return the outcome of ``step``, not run because ``needs`` did not pass."""
    return StepNotRun(GateName(step), GateName(needs))


def _ran(results: Sequence[StepOutcome]) -> list[StepResult]:
    """Return ``results`` as steps that ran, which every step of lanes needing nothing is."""
    ran = [result for result in results if isinstance(result, StepResult)]
    assert len(ran) == len(results), results
    return ran


def test_all_pass_collects_every_step(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every step of every lane is run and collected when all succeed."""
    runs = install(monkeypatch, _table(a1=passes, a2=passes, b1=passes))
    lanes = [[_step(A1), _step(A2)], [_step(B1)]]
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert all_passed(results)
    assert {r.name for r in results} == {"a1", "a2", "b1"}
    assert runs.commands == [A1, A2, B1]


def test_failure_surfaces_with_real_returncode(monkeypatch: pytest.MonkeyPatch) -> None:
    """A failing step makes the run fail and keeps its real exit code."""
    _ = install(monkeypatch, _table(ok=passes, bad=ends(ExitStatus(3))))
    lanes = [[_step(CommandWord("ok"))], [_step(CommandWord("bad"))]]
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert not all_passed(results)
    bad = next(r for r in _ran(results) if r.name == "bad")
    assert bad.returncode == 3


def test_a_failure_leaves_the_rest_of_its_lane_running(monkeypatch: pytest.MonkeyPatch) -> None:
    """A step that needs nothing runs after a failure in its lane, and its outcome is reported."""
    runs = install(monkeypatch, _table(first=passes, boom=ends(ExitStatus(1)), after=passes))
    lanes = [[_step(FIRST), _step(BOOM), _step(AFTER)]]
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert runs.commands == [FIRST, BOOM, AFTER]
    assert [(r.name, r.returncode) for r in _ran(results)] == [
        ("first", 0),
        ("boom", 1),
        ("after", 0),
    ]
    assert not all_passed(results)


def test_a_step_needing_a_failed_step_is_reported_not_run(monkeypatch: pytest.MonkeyPatch) -> None:
    """A step needing one that failed is not run and names it; a step needing nothing still runs.

    The step not run is neither a pass nor a failure: it is an outcome of its
    own, in its place in the lane's results.
    """
    runs = install(
        monkeypatch, _table(first=passes, boom=ends(ExitStatus(1)), uses=passes, after=passes)
    )
    lanes = [[_step(FIRST), _step(BOOM), _step(USES, needs=(BOOM,)), _step(AFTER)]]
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert runs.commands == [FIRST, BOOM, AFTER]
    assert [r.name for r in results] == ["first", "boom", "uses", "after"]
    assert results[2] == _not_run(USES, BOOM)
    assert not all_passed(results)


def test_a_step_needing_one_not_run_is_not_run_either(monkeypatch: pytest.MonkeyPatch) -> None:
    """Not running passes down a chain of needs, each step naming the one it needed."""
    runs = install(monkeypatch, _table(boom=ends(ExitStatus(1)), uses=passes, after=passes))
    lanes = [[_step(BOOM), _step(USES, needs=(BOOM,)), _step(AFTER, needs=(USES,))]]
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert runs.commands == [BOOM]
    assert results[1:] == [_not_run(USES, BOOM), _not_run(AFTER, USES)]


def test_a_step_needing_a_step_run_before_the_lanes_runs_only_if_it_passed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A step run before the lanes, the build, answers a need in every lane, pass or fail."""
    runs = install(monkeypatch, _table(uses=passes, after=passes))
    lanes = [[_step(USES, needs=(BUILD,))], [_step(AFTER, needs=(BUILD,))]]
    failed = StepResult(BUILD, ExitStatus(1), NO_OUTPUT, 0.0)
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor, before=[failed])
    assert runs.commands == []
    assert results == [_not_run(USES, BUILD), _not_run(AFTER, BUILD)]
    passed = StepResult(BUILD, ExitStatus(0), NO_OUTPUT, 0.0)
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor, before=[passed])
    assert runs.commands == [USES, AFTER]
    assert all_passed(results)


def test_a_need_no_earlier_step_of_its_lane_answers_is_refused(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A need names an earlier step of the same lane or one run before the lanes, or nothing runs.

    A later step of the lane has not run when the need is read, and a step of
    another lane runs beside it, so neither can answer it.
    """
    runs = install(monkeypatch, _table(a1=passes, a2=passes, b1=passes))
    lanes = [[_step(A1, needs=(A2,)), _step(A2)], [_step(B1, needs=(A1, BUILD))]]
    assert unmet_needs(lanes, frozenset({GateName(BUILD)})) == [("a1", "a2"), ("b1", "a1")]
    with pytest.raises(ValueError, match="a1 needs a2, b1 needs a1"):
        _ = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert runs.commands == []


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
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert {r.name for r in results} == {"fail", "sib1", "sib2"}
    assert not all_passed(results)


def test_a_lane_starts_no_step_once_the_sweep_is_stopping(monkeypatch: pytest.MonkeyPatch) -> None:
    """A lane raising stops the sweep: a lane not yet run starts none of its steps.

    The sweep closes its stop pipe once it reads the exception, and a step
    started after that would only be stopped again.
    """

    def raises(_call: StepCall) -> Answer:
        msg = "a lane's own fault"
        raise RuntimeError(msg)

    runs = install(monkeypatch, _table(boom=raises, a1=passes, a2=passes))
    lanes = [[_step(BOOM)], [_step(A1), _step(A2)]]
    with pytest.raises(RuntimeError, match="a lane's own fault"):
        _ = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert runs.commands == [BOOM]


def test_a_heavy_step_waiting_for_its_slot_when_the_sweep_stops_does_not_start(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The stop is read after the wait for the memory semaphore, not only before it.

    The stop arrives while the heavy step waits for its slot, as an interrupt
    reaching the sweep while another heavy step holds the slot would.
    """
    runs = install(monkeypatch, _table(heavy=passes))
    stops: list[bool] = []

    def acquire() -> bool:
        stops.append(True)
        return True

    shared = LaneContext(acquire, lambda: None, lambda: bool(stops), None, None, frozenset())
    assert not run_lane([_step(CommandWord("heavy"), heavy=True)], shared)
    assert stops == [True]
    assert runs.commands == []


def test_signal_death_counts_as_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    """A SIGKILL's status (the OOM-killer signature) is a failure: a step needing it is not run."""
    killed = ExitStatus(128 + signal.SIGKILL)  # the status the guard reports for a signal death
    runs = install(monkeypatch, _table(oom=ends(killed), uses=passes))
    lanes = [[_step(OOM), _step(USES, needs=(OOM,))]]
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert not all_passed(results)
    assert results == [StepResult(OOM, killed, NO_OUTPUT, 0.0), _not_run(USES, OOM)]
    assert runs.commands == [OOM]


# A sweep of two lanes run in parallel, one of them a step running the build.
_PARALLEL = ScriptSource(
    "from tools._scheduler import Step, run_lanes; "
    + "run_lanes([[Step('build', 'cabal run shake -- build')], [Step('other', 'true')]], "
    + "heavy_limit=1)"
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
        + "heavy_limit=1, executor=None)"
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
        + "[Step('other', 'true')]], heavy_limit=1)"
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
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert [(r.name, r.output) for r in _ran(results)] == [("noisy", noisy), ("mixed", mixed)]


def test_serial_mode_runs_every_lane(monkeypatch: pytest.MonkeyPatch) -> None:
    """The serial fallback still runs and collects every lane, with no stop descriptor."""
    runs = install(monkeypatch, _table(a=passes, b=passes))
    lanes = [[_step(CommandWord("a"))], [_step(CommandWord("b"))]]
    results = run_lanes(lanes, heavy_limit=1, executor=None)
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
    results = run_lanes(lanes, heavy_limit=1, executor=DrivenExecutor)
    assert all_passed(results)
    assert [r.output for r in _ran(results)] == [NO_OUTPUT, heavy]
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
    results = run_lanes(lanes, heavy_limit=1, progress=events.append, executor=DrivenExecutor)
    assert not all_passed(results)
    assert [(e.phase, e.name) for e in events] == [
        ("start", "first"),
        ("done", "first"),
        ("start", "boom"),
        ("done", "boom"),
    ]
    done_boom = events[-1]
    assert isinstance(done_boom.result, StepResult)
    assert done_boom.result.returncode == 4
    assert events[0].result is None  # a start event carries no outcome yet


def test_progress_observes_a_step_not_run(monkeypatch: pytest.MonkeyPatch) -> None:
    """A step not run fires one event of its own, carrying the step it needed, and no start."""
    events: list[StepEvent] = []
    _ = install(monkeypatch, _table(boom=ends(ExitStatus(1)), uses=passes))
    _ = run_lanes(
        [[_step(BOOM), _step(USES, needs=(BOOM,))]],
        heavy_limit=1,
        progress=events.append,
        executor=DrivenExecutor,
    )
    assert [(e.phase, e.name) for e in events] == [
        ("start", "boom"),
        ("done", "boom"),
        ("not run", "uses"),
    ]
    assert events[-1].result == _not_run(USES, BOOM)


def test_a_step_reports_the_time_the_clock_moved_while_it_ran(
    clock: Clock, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A step's duration is what the clock read between its start and its end, and nothing else."""

    def observe(event: StepEvent) -> None:
        if event.phase == "start":
            clock.advance(Seconds(3.0))

    _ = install(monkeypatch, _table(timed=passes))
    (result,) = _ran(
        run_lanes(
            [[_step(CommandWord("timed"))]],
            heavy_limit=1,
            progress=observe,
            executor=None,
        )
    )
    assert result.duration == 3.0


def test_progress_none_is_supported(monkeypatch: pytest.MonkeyPatch) -> None:
    """The default (no observer) runs exactly as before — the seam is optional."""
    runs = install(monkeypatch, _table(quiet=passes))
    results = run_lanes([[_step(CommandWord("quiet"))]], heavy_limit=1, executor=DrivenExecutor)
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
        heavy_limit=1,
        executor=DrivenExecutor,
    )
    assert sorted(fds.iterdir()) == before
    stop_fds = [call.stop_fd for call in runs.calls]
    assert open_while_running == stop_fds
    assert len(set(stop_fds)) == 1
