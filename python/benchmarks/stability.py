"""Long-run resource-leakage stability harness (R18 cluster 6 / Python cat 25).

Exercises the FFI surface for ``cycles × frames`` (default 10 × 100_000 = 1M
total frames) and asserts no per-iteration drift on:

  - RSS (soft threshold)        — psutil.Process().memory_info().rss
  - FD count (hard zero)        — psutil.Process().num_fds()
  - ctypes handles (hard zero)  — RTSState.refcount post-final-close
  - logger handlers (hard zero) — len(logging.getLogger("aletheia").handlers)

Per AGENTS.md Python cat 25 "Long-run resource leakage sub-checks": **drift on
any sub-check is a finding**.  Hard-zero gates are exact equality (no noise
tolerance allowed); soft-threshold gates carry an empirically-tuned cap that
lives next to the assertion below — change the value, the diff is visible.

Output: JSON written to stdout (and optionally
``benchmarks/stability/<commit>/python.json`` when invoked through
``tools/stability_run.py``).

Forward-revert verified 2026-05-08: introducing an intentional non-Close (e.g.
deleting ``RTSState.release()``) makes the harness fail with a precise
ctypes-handle-delta diagnostic; restoring brings it back to 0 drift.
"""

from __future__ import annotations

import gc
import json
import logging
import os
import sys
import time
from pathlib import Path

import psutil

# Ensure the in-tree binding wins over any installed copy.
_REPO_PYTHON = Path(__file__).resolve().parent.parent
if str(_REPO_PYTHON) not in sys.path:
    sys.path.insert(0, str(_REPO_PYTHON))

# pylint: disable=wrong-import-position
from aletheia import AletheiaClient
from aletheia.client._ffi import RTSState
from aletheia.protocols import DBCDefinition

from ._common import CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME, load_dbc

# Soft-threshold caps (empirically established 2026-05-08, WSL2 quiet host;
# revise inline if a future reviewer runs the harness on a host that rejects
# these as too tight or too loose).
RSS_DELTA_BYTES_CAP = 50 * 1024 * 1024  # 50 MiB across 1M frames

# Warmup cycles before the measurement window opens.  The GHC RTS heap +
# MAlonzo dictionaries + lazy Agda structures need a substantial workload
# before they reach steady state — empirical probe (2026-05-09 cluster 7
# orchestrator e2e) showed the heap plateaus around cycle 7 of 100k frames
# (≈700k frames); a 10-frame warmup as cluster 6 originally shipped left
# 137-154 MiB of RTS warmup leaking into the measurement window.  7 cycles
# of WARMUP gives ≥ 30 MiB headroom over the 50 MiB threshold without
# inflating the bench beyond ~10s wall.
WARMUP_CYCLES = 7
LOGGER_NAME = "aletheia"


def _real_fd_count() -> int:
    """Count /proc/self/fd entries that point to real resources.

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
    fd_dir = Path("/proc/self/fd")
    count = 0
    for entry in fd_dir.iterdir():
        try:
            target = os.readlink(entry)
        except OSError:
            # FD vanished between iterdir and readlink — common for the
            # transient FD iterdir itself opens.  Skip.
            continue
        if target.startswith("anon_inode:"):
            continue
        count += 1
    return count


def _proc_snapshot(proc: psutil.Process) -> dict[str, int]:
    """Capture per-process resource snapshot at one point in time."""
    return {
        "rss": proc.memory_info().rss,
        "num_fds": _real_fd_count(),
        "rts_refcount": RTSState.refcount,
        "logger_handlers": len(logging.getLogger(LOGGER_NAME).handlers),
    }


def _run_cycle(frames_per_cycle: int, dbc: DBCDefinition) -> None:
    """One open/load/run/close cycle.

    Loads a DBC, starts a stream, sends ``frames_per_cycle`` frames through
    the binary FFI path, ends the stream, closes.  State leak detection
    happens inline: after ``close()`` ``client.is_closed`` must be ``True``
    (Client invariant), and the RTSState refcount must drop by exactly 1.
    """
    refcount_before = RTSState.refcount
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
        # Pre-close invariant: not yet closed (we're still inside ``with``).
        if client.is_closed:
            raise RuntimeError("state cleared inside client context")
    # Post-close invariant.
    if not client.is_closed:
        raise RuntimeError("state not cleared after Client.close()")
    if RTSState.refcount != refcount_before:
        raise RuntimeError(
            "RTSState.refcount drift mid-cycle: "
            + f"before={refcount_before} after={RTSState.refcount}"
        )


def _build_sub_checks(start: dict[str, int], end: dict[str, int]) -> list[dict[str, object]]:
    """Build the four sub-check verdict dicts from start/end snapshots.

    Hard-zero gates use exact equality; soft-threshold uses |delta| ≤ cap.
    Extracted from ``main`` to keep its local-variable count under the
    pylint cap without leaning on suppression.
    """
    rss_delta = end["rss"] - start["rss"]
    fd_delta = end["num_fds"] - start["num_fds"]
    rts_delta = end["rts_refcount"] - start["rts_refcount"]
    handler_delta = end["logger_handlers"] - start["logger_handlers"]
    return [
        {
            "name": "rss",
            "gate": "soft_threshold",
            "start": start["rss"], "end": end["rss"], "delta": rss_delta,
            "threshold": RSS_DELTA_BYTES_CAP,
            "passed": abs(rss_delta) <= RSS_DELTA_BYTES_CAP,
        },
        {
            "name": "fd_count",
            "gate": "hard_zero",
            "start": start["num_fds"], "end": end["num_fds"], "delta": fd_delta,
            "threshold": 0,
            "passed": fd_delta == 0,
        },
        {
            "name": "ctypes_handles",
            "gate": "hard_zero",
            "start": start["rts_refcount"], "end": end["rts_refcount"], "delta": rts_delta,
            "threshold": 0,
            "passed": rts_delta == 0,
        },
        {
            "name": "logger_handlers",
            "gate": "hard_zero",
            "start": start["logger_handlers"], "end": end["logger_handlers"],
            "delta": handler_delta,
            "threshold": 0,
            "passed": handler_delta == 0,
        },
    ]


def main() -> int:
    """Drive ``cycles × frames`` exercise of the FFI surface; emit verdict JSON."""
    cycles = int(os.environ.get("ALETHEIA_STABILITY_CYCLES", "10"))
    frames = int(os.environ.get("ALETHEIA_STABILITY_FRAMES", "100000"))
    proc = psutil.Process()
    dbc = load_dbc()

    # Multi-cycle warmup to absorb the GHC RTS heap warmup + lazy MAlonzo /
    # Agda structure realization.  See WARMUP_CYCLES for empirical rationale.
    for _ in range(WARMUP_CYCLES):
        _run_cycle(frames_per_cycle=frames, dbc=dbc)
    gc.collect()

    start = _proc_snapshot(proc)
    t0 = time.monotonic()

    for _cycle_idx in range(cycles):
        _run_cycle(frames_per_cycle=frames, dbc=dbc)
        # Force a GC between cycles so any per-cycle Python allocations are
        # reclaimed before we measure the next snapshot — keeps the hard-zero
        # gates from being defeated by lazy GC.
        gc.collect()

    gc.collect()
    end = _proc_snapshot(proc)
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
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
