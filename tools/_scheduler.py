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
    from collections.abc import Sequence
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


@dataclass(frozen=True)
class StepResult:
    """Outcome of one executed step: combined output + real return code."""

    name: str
    returncode: int
    output: str
    duration: float


def _run_one(step: Step, heavy_sem: threading.Semaphore) -> StepResult:
    """Execute one step, capturing combined output; honour the memory semaphore."""
    start = time.monotonic()
    if step.heavy:
        heavy_sem.acquire()
    try:
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
    return StepResult(step.name, proc.returncode, proc.stdout, time.monotonic() - start)


def _run_lane(lane: Sequence[Step], heavy_sem: threading.Semaphore) -> list[StepResult]:
    """Run a lane's steps serially, stopping at the first failure (deps follow)."""
    results: list[StepResult] = []
    for step in lane:
        result = _run_one(step, heavy_sem)
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
) -> list[StepResult]:
    """Run ``lanes`` concurrently (bounded by ``max_workers``) and collect results.

    ``serial=True`` runs every lane in order on the calling thread — the escape
    hatch for debugging or a resource-starved host.  ``heavy_limit`` caps how
    many ``heavy`` steps run at once (the OOM guard).  Results are returned in
    lane-then-step order, deterministic regardless of completion timing, so the
    caller can tee them without interleaving.  Any exception inside a lane
    propagates (it is never silently dropped).
    """
    heavy_sem = threading.Semaphore(max(1, heavy_limit))
    if serial:
        out: list[StepResult] = []
        for lane in lanes:
            out.extend(_run_lane(lane, heavy_sem))
        return out
    with ThreadPoolExecutor(max_workers=max(1, max_workers)) as executor:
        futures = [executor.submit(_run_lane, lane, heavy_sem) for lane in lanes]
        per_lane = [future.result() for future in futures]
    return [result for lane_results in per_lane for result in lane_results]


def all_passed(results: Sequence[StepResult]) -> bool:
    """Return ``True`` only if every collected step returned zero."""
    return all(result.returncode == 0 for result in results)
