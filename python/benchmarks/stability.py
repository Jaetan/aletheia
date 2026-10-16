# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Long-run resource-leakage stability harness (Python cat 25).

Exercises the FFI surface for ``cycles × frames`` (default 10 × 100_000 = 1M
total frames) and asserts no per-iteration drift on:

  - RSS (soft threshold):        psutil.Process().memory_info().rss
  - FD count (hard zero):        the /proc/self/fd entries naming a real resource
  - ctypes handles (hard zero):  RTSState.refcount post-final-close
  - logger handlers (hard zero): len(logging.getLogger("aletheia").handlers)

Per AGENTS.md Python cat 25 "Long-run resource leakage sub-checks": **drift on
any sub-check is a finding**.  Hard-zero gates are exact equality (no noise
tolerance allowed); soft-threshold gates carry an empirically-tuned cap that
lives next to the assertion below — change the value, the diff is visible.

Output: JSON written to stdout (and optionally
``benchmarks/stability/<commit>/python.json`` when invoked through
``tools/stability_run.py``).
"""

from __future__ import annotations

import argparse
import functools
import gc
import json
import logging
import os
import sys
import time
from pathlib import Path
from typing import TYPE_CHECKING, Literal

import psutil
from benchmarks._common import CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME, load_dbc, run_report

from aletheia import AletheiaClient
from aletheia.client._ffi import RTSState
from aletheia.common_types import ExitStatus, PositiveInt, Prose

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.types import DBCDefinition

# Soft-threshold caps (empirically established 2026-05-08, WSL2 quiet host;
# revise inline if a future reviewer runs the harness on a host that rejects
# these as too tight or too loose).
RSS_DELTA_BYTES_CAP = 50 * 1024 * 1024  # 50 MiB across 1M frames

# Warmup cycles before the measurement window opens.  The GHC RTS heap +
# MAlonzo dictionaries + lazy Agda structures need a substantial workload
# before they reach steady state — an empirical probe (2026-05-09)
# showed the heap plateaus around cycle 7 of 100k frames (≈700k frames);
# the original 10-frame warmup left 137-154 MiB of RTS warmup leaking
# into the measurement window.  7 cycles
# of WARMUP gives ≥ 30 MiB headroom over the 50 MiB threshold without
# inflating the bench beyond ~10s wall.
WARMUP_CYCLES = 7
LOGGER_NAME = "aletheia"

# The status of a run that reached no verdict, which tools/stability_run.py
# reads as an environment failure rather than as drift.
NO_VERDICT = ExitStatus(2)

# The environment variables that size the run, and the largest count each takes.
CountVariable = Literal["ALETHEIA_STABILITY_CYCLES", "ALETHEIA_STABILITY_FRAMES"]
COUNT_MAX = 2_147_483_647


class SnapshotError(Exception):
    """A resource the snapshot reads could not be read as a count."""


def _real_fd_count() -> int:
    """Count the fd entries that point to real resources.

    The entries are those of ``self/fd`` under the process filesystem psutil
    reads, ``psutil.PROCFS_PATH``; a directory that cannot be listed raises
    ``SnapshotError``.

    Excludes anon_inode targets (eventfd, eventpoll, timerfd, signalfd)
    which are runtime-infrastructure FDs the GHC RTS netpoller / Python
    asyncio loop allocate lazily based on workload.  These are not leaks —
    they are I/O multiplexer machinery — and counting them defeats hard-zero
    gating because the runtime grows them across the measurement window
    even when every Client is properly Closed.

    Per AGENTS.md cat 25 the FD sub-check is meant to catch "a forgotten
    Close somewhere on the FFI/file-loader path"; that means real resources.
    Linux-specific.
    """
    fd_dir = Path(psutil.PROCFS_PATH) / "self" / "fd"
    try:
        entries = list(fd_dir.iterdir())
    except OSError as err:
        msg = f"reading {fd_dir}: {err}"
        raise SnapshotError(msg) from err
    count = 0
    for entry in entries:
        try:
            target = entry.readlink()
        except OSError:
            # FD vanished between iterdir and readlink — common for the
            # transient FD iterdir itself opens.  Skip.
            continue
        if str(target).startswith("anon_inode:"):
            continue
        count += 1
    return count


def _proc_snapshot() -> dict[str, int]:
    """Capture per-process resource snapshot at one point in time.

    A resource that cannot be read as a count raises ``SnapshotError`` rather
    than reading as zero.
    """
    try:
        rss = psutil.Process().memory_info().rss
    except (psutil.Error, OSError, ValueError) as err:
        msg = f"reading the resident set size: {err}"
        raise SnapshotError(msg) from err
    return {
        "rss": rss,
        "num_fds": _real_fd_count(),
        "rts_refcount": RTSState.refcount,
        "logger_handlers": len(logging.getLogger(LOGGER_NAME).handlers),
    }


def _run_cycle(frames_per_cycle: int, dbc: DBCDefinition) -> None:
    """One open/load/run/close cycle.

    Loads a DBC, starts a stream, sends ``frames_per_cycle`` frames through
    the binary FFI path, ends the stream, closes.  A handle the cycle leaves
    behind stays counted in ``RTSState.refcount``, for the ``ctypes_handles``
    gate to fail at the end of the run.
    """
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.start_stream()
        for i in range(frames_per_cycle):
            client.send_frame(
                timestamp=i * 1000,
                can_id=CAN20_CAN_ID,
                dlc=CAN20_DLC,
                data=CAN20_FRAME,
            )
        client.end_stream()


def _build_sub_checks(start: dict[str, int], end: dict[str, int]) -> list[dict[str, object]]:
    """Build the four sub-check verdict dicts from start/end snapshots.

    Hard-zero gates use exact equality; soft-threshold uses |delta| ≤ cap.
    """
    rss_delta = end["rss"] - start["rss"]
    fd_delta = end["num_fds"] - start["num_fds"]
    rts_delta = end["rts_refcount"] - start["rts_refcount"]
    handler_delta = end["logger_handlers"] - start["logger_handlers"]
    return [
        {
            "name": "rss",
            "gate": "soft_threshold",
            "start": start["rss"],
            "end": end["rss"],
            "delta": rss_delta,
            "threshold": RSS_DELTA_BYTES_CAP,
            "passed": abs(rss_delta) <= RSS_DELTA_BYTES_CAP,
        },
        {
            "name": "fd_count",
            "gate": "hard_zero",
            "start": start["num_fds"],
            "end": end["num_fds"],
            "delta": fd_delta,
            "threshold": 0,
            "passed": fd_delta == 0,
        },
        {
            "name": "ctypes_handles",
            "gate": "hard_zero",
            "start": start["rts_refcount"],
            "end": end["rts_refcount"],
            "delta": rts_delta,
            "threshold": 0,
            "passed": rts_delta == 0,
        },
        {
            "name": "logger_handlers",
            "gate": "hard_zero",
            "start": start["logger_handlers"],
            "end": end["logger_handlers"],
            "delta": handler_delta,
            "threshold": 0,
            "passed": handler_delta == 0,
        },
    ]


class _StageError(Exception):
    """What a load, a warm-up or a cycle raised, held as its cause."""


def _stage[T](step: Callable[[], T]) -> T:
    """Answer ``step()``, any error it raises re-raised as a :class:`_StageError`.

    A load, a warm-up or a cycle that fails ends the run with no verdict, exit 2,
    whatever it raised: an error left to escape would exit 1, which the runner
    reads as a failed gate.
    """
    try:
        return step()
    except Exception as err:
        raise _StageError(err) from err


def env_count(name: CountVariable, default: PositiveInt) -> PositiveInt:
    """Read a count from the environment, ``default`` when unset.

    A count is ASCII digits naming a number from 1 to ``COUNT_MAX``.  Anything
    else raises ``ValueError``: a run that quietly measured the default would
    report it as the answer to what was asked.
    """
    raw = os.environ.get(name)
    if raw is None:
        return default
    # Longer than the bound once its leading zeros are dropped, a value is
    # refused unconverted: ``int`` refuses more digits than its conversion limit
    # in words of its own.
    digits = raw.lstrip("0")
    if (
        not (raw.isascii() and raw.isdigit())
        or len(digits) > len(str(COUNT_MAX))
        or not 1 <= int(digits or "0") <= COUNT_MAX
    ):
        msg = f"{name} must be a whole number from 1 to {COUNT_MAX}, got {raw!r}"
        raise ValueError(msg)
    return int(digits)


def _measure(cycles: PositiveInt, frames: PositiveInt) -> ExitStatus:
    """Drive ``cycles × frames`` exercise of the FFI surface; emit verdict JSON."""
    try:
        dbc = _stage(load_dbc)
    except _StageError as err:
        print(f"stability: loading the DBC failed: {err}", file=sys.stderr)
        return NO_VERDICT

    # Multi-cycle warmup to absorb the GHC RTS heap warmup + lazy MAlonzo /
    # Agda structure realization.  See WARMUP_CYCLES for empirical rationale.
    for warm_up in range(WARMUP_CYCLES):
        try:
            _stage(functools.partial(_run_cycle, frames_per_cycle=frames, dbc=dbc))
        except _StageError as err:
            print(
                f"stability: warm-up cycle {warm_up + 1} of {WARMUP_CYCLES} failed: {err}",
                file=sys.stderr,
            )
            return NO_VERDICT
    gc.collect()

    try:
        start = _proc_snapshot()
    except SnapshotError as err:
        print(f"stability: the opening snapshot failed: {err}", file=sys.stderr)
        return NO_VERDICT
    t0 = time.monotonic()

    for cycle in range(cycles):
        try:
            _stage(functools.partial(_run_cycle, frames_per_cycle=frames, dbc=dbc))
        except _StageError as err:
            print(f"stability: cycle {cycle + 1} of {cycles} failed: {err}", file=sys.stderr)
            return NO_VERDICT
        # Force a GC between cycles so any per-cycle Python allocations are
        # reclaimed before we measure the next snapshot — keeps the hard-zero
        # gates from being defeated by lazy GC.
        gc.collect()

    gc.collect()
    try:
        end = _proc_snapshot()
    except SnapshotError as err:
        print(f"stability: the closing snapshot failed: {err}", file=sys.stderr)
        return NO_VERDICT
    elapsed = time.monotonic() - t0

    sub_checks = _build_sub_checks(start, end)
    report = {
        "binding": "python",
        "cycles": cycles,
        "frames_per_cycle": frames,
        "total_frames": cycles * frames,
        "elapsed_seconds": elapsed,
        "sub_checks": sub_checks,
        "passed": all(c["passed"] for c in sub_checks),
    }

    json.dump(report, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return ExitStatus(0 if report["passed"] else 1)


def main() -> ExitStatus:
    """Read the run's size, then measure it, the verdict JSON on stdout.

    A report stdout refuses leaves the run without a verdict, with ``stability:
    writing the report failed: <reason>`` on stderr.
    """
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    # Before the kernel loads, so a refused run measures nothing.
    try:
        cycles = env_count("ALETHEIA_STABILITY_CYCLES", 10)
        frames = env_count("ALETHEIA_STABILITY_FRAMES", 100_000)
    except ValueError as err:
        print(f"stability: {err}", file=sys.stderr)
        return NO_VERDICT
    refusal = Prose("stability: writing the report failed")
    return run_report(functools.partial(_measure, cycles, frames), refusal, NO_VERDICT)


if __name__ == "__main__":
    sys.exit(main())
