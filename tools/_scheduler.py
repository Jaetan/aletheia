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

* every executed step yields a :class:`StepResult` with its real return code;
* a signal death — negative ``returncode``, e.g. ``-9`` from the OOM killer —
  is a failure like any other (``returncode != 0``);
* a lane stops at its first failing step (later steps depend on it), but every
  *other* lane still runs to completion, so one run surfaces all failures;
* a lane task that raises propagates out of :func:`run_lanes` (never dropped).
"""

from __future__ import annotations

import subprocess
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Callable, Sequence
    from pathlib import Path

_POSIX_SHELL = "/bin/sh"


@dataclass(frozen=True)
class Step:
    """One gate step: a name plus the command to run for it.

    ``cmd`` is an argv list (run directly) or a string (run via ``/bin/sh -c``
    for the lanes that need pipes / globs / redirection).  ``heavy`` marks a
    big-memory step (``-M16G`` Agda, sanitizer build, race detector) that must
    contend for the memory semaphore.
    """

    name: str
    cmd: Sequence[str] | str
    cwd: Path | None = None
    heavy: bool = False
    lane: str = "misc"


@dataclass(frozen=True)
class StepResult:
    """Outcome of one executed step: combined output + real return code."""

    name: str
    returncode: int
    output: str
    duration: float


@dataclass(frozen=True)
class StepEvent:
    """A live progress event: a step started, or finished with its outcome.

    ``phase`` is ``"start"`` (``result`` is ``None``) or ``"done"`` (``result``
    carries the outcome).  Events fire the moment they happen — from worker
    threads under ``--parallel`` — so a consumer that writes them to a terminal
    must serialize its own writes; the deterministic lane-then-step ordering of
    :func:`run_lanes`'s RETURN VALUE is unaffected by observation.
    """

    phase: str
    name: str
    result: StepResult | None = None


def _run_one(
    step: Step,
    heavy_sem: threading.Semaphore,
    progress: Callable[[StepEvent], None] | None,
) -> StepResult:
    """Execute one step, capturing combined output; honour the memory semaphore.

    The ``start`` event fires after the heavy-semaphore wait, so it marks the
    step actually RUNNING (not queued behind the OOM guard) and the reported
    duration matches what the observer perceives.
    """
    if step.heavy:
        heavy_sem.acquire()
    start = time.monotonic()
    try:
        if progress is not None:
            progress(StepEvent("start", step.name))
        argv: Sequence[str]
        argv = [_POSIX_SHELL, "-c", step.cmd] if isinstance(step.cmd, str) else step.cmd
        proc = subprocess.run(
            list(argv),
            cwd=step.cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
    finally:
        if step.heavy:
            heavy_sem.release()
    result = StepResult(step.name, proc.returncode, proc.stdout, time.monotonic() - start)
    if progress is not None:
        progress(StepEvent("done", step.name, result))
    return result


def _run_lane(
    lane: Sequence[Step],
    heavy_sem: threading.Semaphore,
    progress: Callable[[StepEvent], None] | None,
) -> list[StepResult]:
    """Run a lane's steps serially, stopping at the first failure (deps follow)."""
    results: list[StepResult] = []
    for step in lane:
        result = _run_one(step, heavy_sem, progress)
        results.append(result)
        if result.returncode != 0:
            break  # later steps in THIS lane depend on the failed one; skip them
    return results


def run_lanes(
    lanes: Sequence[Sequence[Step]],
    *,
    max_workers: int,
    heavy_limit: int,
    serial: bool = False,
    progress: Callable[[StepEvent], None] | None = None,
) -> list[StepResult]:
    """Run ``lanes`` concurrently (bounded by ``max_workers``) and collect results.

    ``serial=True`` runs every lane in order on the calling thread — the escape
    hatch for debugging or a resource-starved host.  ``heavy_limit`` caps how
    many ``heavy`` steps run at once (the OOM guard).  Results are returned in
    lane-then-step order, deterministic regardless of completion timing, so the
    caller can tee them without interleaving.  Any exception inside a lane
    propagates (it is never silently dropped).

    ``progress`` observes each step's start and completion the moment they
    happen (from worker threads under parallel mode) — the live channel for a
    terminal spinner or per-step timing, deliberately separate from the
    deterministic result stream.  A ``None`` progress is zero-overhead.
    """
    heavy_sem = threading.Semaphore(max(1, heavy_limit))
    if serial:
        out: list[StepResult] = []
        for lane in lanes:
            out.extend(_run_lane(lane, heavy_sem, progress))
        return out
    with ThreadPoolExecutor(max_workers=max(1, max_workers)) as executor:
        futures = [executor.submit(_run_lane, lane, heavy_sem, progress) for lane in lanes]
        per_lane = [future.result() for future in futures]
    return [result for lane_results in per_lane for result in lane_results]


def all_passed(results: Sequence[StepResult]) -> bool:
    """Return ``True`` only if every collected step returned zero."""
    return all(result.returncode == 0 for result in results)
