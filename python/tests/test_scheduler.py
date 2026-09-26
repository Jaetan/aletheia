# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._scheduler`` — lane-parallel gate scheduling.

Synthetic steps (``exit C`` / ``echo``) exercise the *logic* in milliseconds
without touching the real gates or hammering the host.  The focus is the
property a gate orchestrator must never get wrong — **no failure is silently
dropped** — plus lane fail-fast, cross-lane independence, signal-death handling,
output capture, and deterministic result ordering.
"""

from __future__ import annotations

import os
import signal
import subprocess
import sys
import time
from pathlib import Path

from tools import _scheduler
from tools._scheduler import Step, StepEvent, all_passed, run_lanes

REPO_ROOT = Path(_scheduler.__file__).resolve().parents[1]
BOUND_SECONDS = 5.0


def _step(name: str, sh: str, *, heavy: bool = False) -> Step:
    """Build a shell-command synthetic step."""
    return Step(name=name, cmd=sh, heavy=heavy)


def test_all_pass_collects_every_step() -> None:
    """Every step of every lane is run and collected when all succeed."""
    lanes = [[_step("a1", "exit 0"), _step("a2", "exit 0")], [_step("b1", "exit 0")]]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1)
    assert all_passed(results)
    assert {r.name for r in results} == {"a1", "a2", "b1"}


def test_failure_surfaces_with_real_returncode() -> None:
    """A failing step makes the run fail and keeps its real exit code."""
    lanes = [[_step("ok", "exit 0")], [_step("bad", "exit 3")]]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1)
    assert not all_passed(results)
    bad = next(r for r in results if r.name == "bad")
    assert bad.returncode == 3


def test_lane_fail_fast_skips_dependents() -> None:
    """Within a lane, steps after a failure are skipped (they depend on it)."""
    lanes = [[_step("first", "exit 0"), _step("boom", "exit 1"), _step("after", "exit 0")]]
    results = run_lanes(lanes, max_workers=1, heavy_limit=1)
    assert [r.name for r in results] == ["first", "boom"]  # "after" skipped
    assert not all_passed(results)


def test_one_lane_failure_does_not_abort_siblings() -> None:
    """A failing lane never drops sibling lanes — run_lanes awaits every future.

    This is the failing-step-finishes-first / no-silent-drop guarantee: the
    result set always contains every sibling step regardless of completion order.
    """
    lanes = [[_step("fail", "exit 7")], [_step("sib1", "exit 0"), _step("sib2", "exit 0")]]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1)
    assert {r.name for r in results} == {"fail", "sib1", "sib2"}
    assert not all_passed(results)


def test_signal_death_counts_as_failure() -> None:
    """A SIGKILL (the OOM-killer signature) is a failure, not a silent pass."""
    lanes = [[_step("oom", "kill -9 $$")]]
    results = run_lanes(lanes, max_workers=1, heavy_limit=1)
    assert not all_passed(results)
    assert results[0].returncode == 128 + signal.SIGKILL  # the shell's status for a signal death


def test_an_interrupted_parallel_sweep_stops_its_steps(tmp_path: Path) -> None:
    """Ctrl-C, SIGINT to the sweep's process group, ends a parallel sweep within the bound.

    Each step runs in a process group of its own, which the interrupt does
    not reach, so a sweep that only waited on its workers would run until
    the step finished on its own.
    """
    started = tmp_path / "started"
    script = (
        "from tools._scheduler import Step, run_lanes; "
        f"run_lanes([[Step('slow', 'touch \"{started}\"; exec sleep 60')], "
        "[Step('other', 'true')]], max_workers=2, heavy_limit=1)"
    )
    with subprocess.Popen(
        [sys.executable, "-c", script],
        cwd=REPO_ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        process_group=0,
    ) as sweep:
        try:
            deadline = time.monotonic() + BOUND_SECONDS
            while not started.exists():
                assert time.monotonic() < deadline, "the step never started"
                time.sleep(0.02)
            os.killpg(sweep.pid, signal.SIGINT)
            assert sweep.wait(BOUND_SECONDS) != 0
        finally:
            sweep.kill()


def test_output_is_captured() -> None:
    """Each step's combined output is captured into its result."""
    lanes = [[_step("noisy", "echo MARKER_42; exit 0")]]
    results = run_lanes(lanes, max_workers=1, heavy_limit=1)
    assert "MARKER_42" in results[0].output


def test_stderr_is_captured_in_order_with_stdout() -> None:
    """A step's stderr lands in its output, interleaved with stdout as written."""
    lanes = [[_step("mixed", "echo one; echo two >&2; echo three")]]
    results = run_lanes(lanes, max_workers=1, heavy_limit=1)
    assert results[0].output == "one\ntwo\nthree\n"


def test_serial_mode_runs_every_lane() -> None:
    """The serial fallback still runs and collects every lane."""
    lanes = [[_step("a", "exit 0")], [_step("b", "exit 0")]]
    results = run_lanes(lanes, max_workers=4, heavy_limit=1, serial=True)
    assert all_passed(results)
    assert {r.name for r in results} == {"a", "b"}


def test_results_ordered_by_lane_not_completion() -> None:
    """Results come back in lane-then-step order even when lanes run concurrently."""
    lanes = [[_step("a1", "exit 0"), _step("a2", "exit 0")], [_step("b1", "exit 0")]]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1)
    assert [r.name for r in results] == ["a1", "a2", "b1"]


def test_heavy_steps_execute_under_the_gate() -> None:
    """Heavy steps run and are captured (the bound is the Semaphore's contract)."""
    lanes = [
        [_step("h1", "exit 0", heavy=True)],
        [_step("h2", "echo HEAVY; exit 0", heavy=True)],
    ]
    results = run_lanes(lanes, max_workers=2, heavy_limit=1)
    assert all_passed(results)
    assert any("HEAVY" in r.output for r in results)


def test_progress_observes_start_and_done_per_step() -> None:
    """The live channel fires a start and a done event for every executed step.

    Within a lane the order is start→done per step in lane order; the done
    event carries the step's real result (the fail case pins the exit code).
    """
    events: list[StepEvent] = []
    lanes = [[_step("first", "exit 0"), _step("boom", "exit 4")]]
    results = run_lanes(lanes, max_workers=1, heavy_limit=1, progress=events.append)
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


def test_progress_none_is_supported() -> None:
    """The default (no observer) runs exactly as before — the seam is optional."""
    lanes = [[_step("quiet", "exit 0")]]
    results = run_lanes(lanes, max_workers=1, heavy_limit=1)
    assert all_passed(results)


def test_a_parallel_sweep_leaves_no_descriptor_open() -> None:
    """Both ends of the parallel sweep's stop pipe are closed once it returns."""
    fds = Path("/proc/self/fd")
    before = sorted(fds.iterdir())
    _ = run_lanes([[_step("a", "true")], [_step("b", "true")]], max_workers=2, heavy_limit=1)
    assert sorted(fds.iterdir()) == before
