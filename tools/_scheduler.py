# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Lane-parallel scheduler for the CI gate sweep.

The gate steps group into **lanes** by toolchain (Agda/Shake, Python, Go, C++,
Rust, GHA-meta).  Steps *within* a lane share mutable state — the Shake build
dir, ``cpp/build``, cargo's ``target`` — so they must run serially; *across*
lanes there is no shared state, so lanes run concurrently.  That is the unit of
parallelism here: lanes, never individual steps (a flat step pool would let two
``cmake`` builds clobber one ``cpp/build``).

Memory, not cores, is what kills a WSL2 host (OOM → crash-restart), so a
``heavy`` step (anything with a big RTS / sanitizer heap) takes a semaphore that
bounds how many run at once — coarse and robust, no per-step byte estimates.

Aggregation is **fail-loud**, the property a gate orchestrator must never get
wrong (a swallowed failure is a false green):

* every executed step yields a :class:`StepResult` with its real return code,
  or 1 when the watchdog fails a step that exited 0;
* a signal death is a failure like any other (``returncode != 0``): 128 plus
  the signal, e.g. ``137`` from the OOM killer's SIGKILL, or ``-9`` for a step
  the watchdog or the sweep stopped, whose guard ends with its group's SIGKILL;
* every step runs unless a step it ``needs`` did not pass, and then yields a
  :class:`StepNotRun` naming that step, so a failure hides no check that does
  not rest on it and every step of every lane has an outcome;
* a need names an earlier step of the same lane or one run before the lanes,
  which are the steps whose outcome is known when it starts, and a need
  naming anything else is refused before any step runs;
* the first exception a lane task raises, in lane order, propagates out of
  :func:`run_lanes`; a later lane's is dropped.

Every step runs under ``run_watched``, in a process group of its own whose
guard interrupts the step's command when the sweep is interrupted or dies,
SIGKILL included, and kills what is left once the command has ended or the
guard's grace has passed: no command outlives the sweep by more than that
grace, holding a lock the next run waits on.  A process a command leaves in
its group once it exits, holding the step's output, is stopped by the
watchdog's stall while the sweep runs.  An interrupt of the sweep, Ctrl-C
included, is an exceptional exit: a step a lane starts as it arrives is
interrupted as it starts, :func:`run_lanes` re-raises it, and what a step
left behind may outlive the sweep, for whoever interrupted it to clean up.

Every step's output, stderr merged into stdout, is copied into a file of its
own (:func:`step_file`) chunk by chunk as it comes, so what a step has
printed is on disk while it runs and stays there if it hangs or the sweep
dies; its result reads the file back whole.
The watchdog reads the step's progress reports as they come and stops a step
that goes longer than its allowance without one, which then fails, its output
ending with why (``tools._watchdog``).
"""

from __future__ import annotations

import os
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, replace
from typing import TYPE_CHECKING, Literal, NamedTuple

from tools._common import CommandWord, Descriptor, GateName, WorkerCount
from tools._resources import cpu_budget
from tools._watchdog import (
    NO_REPORTS_YET,
    Line,
    Progress,
    ReportCount,
    StepWatch,
    judged,
    run_watched,
)
from tools._watchdog import Seconds as WatchSeconds

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Sequence
    from pathlib import Path

    from tools._common import ExecutorFactory

_POSIX_SHELL = "/bin/sh"

# A result of a step the watchdog read no report of, and no quiet stretch.
_NO_REPORTS = ReportCount(0)
_NO_QUIET = WatchSeconds(0.0)

# How many parts each count a step reports is cut into for the reports :func:`_quarters` tells.
_QUARTERS = 4


@dataclass(frozen=True)
class Step:
    """One gate step: a name plus the command to run for it.

    ``cmd`` is an argv list (run directly) or a string (run via ``/bin/sh -c``
    for the lanes that need pipes / globs / redirection).  ``heavy`` marks a
    big-memory step (heap-capped Agda, sanitizer build, race detector) that must
    contend for the memory semaphore.  ``needs`` names the steps whose output it
    reads: it runs only once each of them passed.  ``progress`` names the lines
    of its output that report its progress and how long it may go without one
    (``tools._watchdog``).
    """

    name: str
    cmd: Sequence[str] | str
    cwd: Path | None = None
    heavy: bool = False
    lane: str = "misc"
    needs: tuple[GateName, ...] = ()
    progress: Progress = NO_REPORTS_YET


# Why the watchdog failed a step: it stopped the step, or the step exited 0 having made none of
# the reports it declares.
type WatchdogFailure = Literal["stalled", "unreported"]


@dataclass(frozen=True)
class StepResult:
    """Outcome of one executed step: its combined output and its return code.

    ``returncode`` is the guard's, as :class:`tools._watchdog.WatchedRun` has
    it, or 1 when the watchdog failed a step that exited 0; ``failure`` is why
    the watchdog failed the step, if it did: ``"stalled"`` when it stopped the
    step, ``"unreported"`` when the step exited 0 having run past
    :data:`tools._watchdog.UNREPORTED_FOR` with no report.
    """

    name: str
    returncode: int
    output: str
    duration: float
    reports: ReportCount = _NO_REPORTS
    longest_quiet: WatchSeconds = _NO_QUIET
    failure: WatchdogFailure | None = None

    @property
    def stalled(self) -> bool:
        """Answer whether the watchdog stopped the step."""
        return self.failure == "stalled"

    @property
    def unreported(self) -> bool:
        """Answer whether the watchdog failed the step, which exited 0, for making no report."""
        return self.failure == "unreported"


@dataclass(frozen=True)
class StepNotRun:
    """A step the sweep did not run, because ``needs``, a step it needs, did not pass."""

    name: GateName
    needs: GateName


# What a step of the sweep came to: it ran, or a step it needs did not pass.
type StepOutcome = StepResult | StepNotRun


@dataclass(frozen=True)
class StepEvent:
    """A live event: a step started, passed a quarter of a count, ended, or was not run.

    ``phase`` is ``"start"`` (``result`` is ``None``, ``live`` the file the
    step writes its output into as it runs), ``"done"`` (``result`` carries the
    outcome), ``"progress"`` (``report``, a report of the step's that passed
    another quarter of the count it reports) or ``"not run"`` (``result`` names
    the step it needed).  Events fire the moment they happen, from worker
    threads under ``--parallel``, so a consumer that writes them to a terminal
    must serialize its own writes; the deterministic lane-then-step ordering of
    :func:`run_lanes`'s RETURN VALUE is unaffected by observation.
    """

    phase: str
    name: str
    result: StepOutcome | None = None
    live: Path | None = None
    report: Line | None = None


def step_file(live_dir: Path, name: GateName) -> Path:
    """Return the file step ``name`` writes its output into, in ``live_dir``.

    The name, each character outside ASCII letters, digits, ``.``, ``_`` and
    ``-`` written as ``-``, with ``.log`` after it.
    """
    return live_dir / f"{re.sub(r'[^A-Za-z0-9._-]', '-', name)}.log"


def _run_one(step: Step, sweep: LaneContext) -> StepResult:
    """Execute one step, its merged output written into its file as it comes, then read back.

    The file is created afresh, so the second of two steps a sweep would write
    into one file raises ``FileExistsError``, before its ``start`` event,
    rather than mix.  The caller holds the memory semaphore for a heavy step,
    so the ``start`` event marks the step actually RUNNING (not queued behind
    the OOM guard) and the reported duration matches what the observer
    perceives.
    """
    progress = sweep.progress
    live = step_file(sweep.live_dir, GateName(step.name))
    argv: Sequence[str]
    argv = [_POSIX_SHELL, "-c", step.cmd] if isinstance(step.cmd, str) else step.cmd
    heard = _quarters(step, progress)
    with live.open("xb") as written:
        start = time.monotonic()
        if progress is not None:
            progress(StepEvent("start", step.name, live=live))
        ran = run_watched(
            [CommandWord(word) for word in argv],
            cwd=step.cwd,
            stop_fd=None if sweep.stop_fd is None else Descriptor(sweep.stop_fd),
            watch=StepWatch(written, step.progress, heard),
        )
        duration = WatchSeconds(time.monotonic() - start)
        failed = judged(step.progress, ran, duration, written)
    pumped = ran.pumped
    result = StepResult(
        step.name,
        ran.returncode if ran.returncode != 0 or not failed else 1,
        live.read_text(encoding="utf-8", errors="replace"),
        duration,
        pumped.reports,
        pumped.longest_quiet,
        "stalled" if pumped.stalled else "unreported" if failed else None,
    )
    if progress is not None:
        progress(StepEvent("done", step.name, result))
    return result


def _quarters(step: Step, progress: Callable[[StepEvent], None] | None) -> Callable[[Line], None]:
    """Answer what hears ``step``'s reports, telling ``progress`` of those that pass a new quarter.

    A report is told when it passes a quarter of the count it reports beyond
    the last one told, short of the whole: at most three per count.  A report
    at the whole tells nothing and starts the count again, so a step running
    two counts, a build's and then its tests', tells quarters of each.
    """
    passed = [0]

    def heard(report: Line) -> None:
        share = step.progress.share(report)
        if progress is None or share is None:
            return
        quarter = int(share * _QUARTERS)
        if quarter >= _QUARTERS:
            passed[0] = 0
        elif passed[0] < quarter:
            passed[0] = quarter
            progress(StepEvent("progress", step.name, report=report))

    return heard


@dataclass(frozen=True)
class Watch:
    """How a sweep is watched as it runs: where its steps write, and who hears each of their events.

    ``live_dir``, an existing directory, receives each step's file
    (:func:`step_file`), written as the step runs; ``progress``, when given,
    observes each :class:`StepEvent` the moment it happens.
    """

    live_dir: Path
    progress: Callable[[StepEvent], None] | None = None


@dataclass(frozen=True)
class LaneContext:
    """What every lane of one sweep shares.

    ``acquire`` and ``release`` take and give back a slot of the memory
    semaphore for a heavy step.  ``stopping`` answers whether the sweep is
    stopping: true once it closes its stop pipe, ``stop_fd``'s write end, on an
    interrupt or a lane's exception.  ``unavailable`` names the steps run
    before the lanes that did not pass.  ``live_dir`` holds each step's file.
    """

    acquire: Callable[[], bool]
    release: Callable[[], None]
    stopping: Callable[[], bool]
    progress: Callable[[StepEvent], None] | None
    stop_fd: int | None
    unavailable: frozenset[GateName]
    live_dir: Path


def run_lane(lane: Sequence[Step], sweep: LaneContext) -> list[StepOutcome]:
    """Run a lane's steps serially, each unless a step it needs did not pass.

    A heavy step first waits on the memory semaphore.  Once the sweep is
    stopping the lane starts no further step, a wait on the semaphore included,
    since the stop would only end it again, and its results go unread.
    """
    progress = sweep.progress
    did_not_pass = set(sweep.unavailable)
    results: list[StepOutcome] = []
    for step in lane:
        missing = next((need for need in step.needs if need in did_not_pass), None)
        outcome: StepOutcome
        if missing is None:
            if step.heavy:
                _ = sweep.acquire()
            try:
                if sweep.stopping():
                    break
                outcome = _run_one(step, sweep)
            finally:
                if step.heavy:
                    sweep.release()
            passed = outcome.returncode == 0
        else:
            outcome, passed = StepNotRun(GateName(step.name), missing), False
            if progress is not None:
                progress(StepEvent("not run", step.name, outcome))
        if not passed:
            did_not_pass.add(GateName(step.name))
        results.append(outcome)
    return results


class UnmetNeed(NamedTuple):
    """A need no step answers where its step runs: ``step`` needs ``need``."""

    step: GateName
    need: GateName


def unmet_needs(lanes: Sequence[Sequence[Step]], before: Collection[GateName]) -> list[UnmetNeed]:
    """Return each need that is neither in ``before`` nor an earlier step of its step's lane."""
    unmet: list[UnmetNeed] = []
    for lane in lanes:
        answered = set(before)
        for step in lane:
            name = GateName(step.name)
            unmet.extend(UnmetNeed(name, need) for need in step.needs if need not in answered)
            answered.add(name)
    return unmet


def _did_not_pass_before(
    lanes: Sequence[Sequence[Step]], before: Sequence[StepOutcome]
) -> frozenset[GateName]:
    """Return the steps of ``before`` that did not pass, once every need of ``lanes`` is answered.

    Raises ``ValueError`` naming each need neither ``before`` nor an earlier
    step of its lane answers.
    """
    unmet = unmet_needs(lanes, {GateName(outcome.name) for outcome in before})
    if unmet:
        msg = ", ".join(f"{unmet_need.step} needs {unmet_need.need}" for unmet_need in unmet)
        raise ValueError(msg)
    return frozenset(GateName(outcome.name) for outcome in before if not all_passed([outcome]))


def run_lanes(
    lanes: Sequence[Sequence[Step]],
    *,
    heavy_limit: int,
    watch: Watch,
    executor: ExecutorFactory | None = ThreadPoolExecutor,
    before: Sequence[StepOutcome] = (),
) -> list[StepOutcome]:
    """Run ``lanes`` concurrently, as many at once as ``cpu_budget`` allows, and collect results.

    ``executor`` builds what the lanes run on concurrently: a thread pool by
    default, and in a test an executor that runs each lane on the test's own
    thread, in the order the test picks.  ``None`` runs every lane in order on
    the calling thread — the escape hatch for debugging or a resource-starved
    host.  ``heavy_limit`` caps how
    many ``heavy`` steps run at once (the OOM guard).  Results are returned in
    lane-then-step order, deterministic regardless of completion timing, so the
    caller can tee them without interleaving.  The first exception a lane
    raises, in lane order, propagates once the other lanes have stopped; a
    later lane's is dropped.

    ``before`` holds the outcomes of the steps run before the lanes, the build,
    which every lane may need; a lane's step may need those and the steps
    before it in its lane, and a need naming any other raises ``ValueError``
    before a step runs.

    ``watch`` names the directory each step writes its file into as it runs
    and the observer of the steps' events (:class:`Watch`), which hears each
    the moment it happens (from worker threads under parallel mode): the live
    channel for a terminal spinner or per-step timing, deliberately separate
    from the deterministic result stream.  A ``None`` progress hears no event.
    """
    unavailable = _did_not_pass_before(lanes, before)
    heavy_sem = threading.Semaphore(max(1, heavy_limit))
    stopping = threading.Event()
    shared = LaneContext(
        heavy_sem.acquire,
        heavy_sem.release,
        stopping.is_set,
        watch.progress,
        None,
        unavailable,
        watch.live_dir,
    )
    if executor is None:
        return [outcome for lane in lanes for outcome in run_lane(lane, shared)]
    # An interrupt reaches this thread only, while the workers wait on steps in
    # groups of their own; closing the write end stops those steps, and every
    # step a worker starts afterwards, so leaving the executor does not wait
    # for a build to finish on its own.  An exception a lane raised, once this
    # thread reads it, stops the lanes still running the same way, and a lane
    # starts no step once ``stopping`` is set.
    stop_read, stop_write = os.pipe()
    sweep = replace(shared, stop_fd=stop_read)
    try:
        with executor(WorkerCount(cpu_budget())) as pool:
            try:
                futures = [pool.submit(run_lane, lane, sweep) for lane in lanes]
                per_lane = [future.result() for future in futures]
            finally:
                stopping.set()
                os.close(stop_write)
    finally:
        os.close(stop_read)
    return [result for lane_results in per_lane for result in lane_results]


def all_passed(results: Sequence[StepOutcome]) -> bool:
    """Return ``True`` only if every collected step ran and returned zero."""
    return all(isinstance(result, StepResult) and result.returncode == 0 for result in results)
