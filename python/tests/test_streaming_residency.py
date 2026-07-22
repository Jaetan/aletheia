# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Bounded-residency regression guard for the streaming hot path.

A long-running monitor must reach a steady state: the kernel keeps O(1) state
per property and one previous frame, so streaming N frames must not cost memory
proportional to N.  This gate catches a regression where the streaming step
stops evaluating the signal cache it derives per frame — an unevaluated cache
keeps a reference to the frame it came from, so the whole trace stays reachable
and residency climbs by roughly a kibibyte per frame until the process dies on
the GHC heap cap.

Two shapes are covered because the retention has two independent routes:

* ``empty-message`` — a message with no signals.  The cache stays empty, so the
  only thing that can retain a frame is the derived cache *value* itself.  This
  shape is the discriminating one: the arms that reach it return the incoming
  cache untouched, so a fix that merely evaluates the cache somewhere along the
  *next* frame's path leaves this shape leaking.
* ``three-signals`` — a message with three signals and a property.  Exercises
  the cache's entry spine, whose per-entry tails are the second retention route.

Each case runs in a fresh interpreter (``_residency_child.py``); ``ru_maxrss``
is a process-wide high-water mark, so measuring inside pytest would let an
earlier test's peak mask a real leak.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Final

import pytest

_CHILD: Final = Path(__file__).parent / "_residency_child.py"

# Growth budget.  The regression this guards leaked ~0.9-1.2 KiB per frame, so
# the counts below grew by 85-145 MiB; a steady-state run grows by single-digit
# MiB (RTS nursery plus allocator granularity).  32 MiB sits far enough above
# the steady state not to flake and far enough below the leak to fail hard.
# Frame counts are the smallest that keep both margins while holding the case
# under a couple of seconds — this runs in the default suite, not behind a flag.
_MAX_GROWTH_KIB: Final = 32 * 1024

_CASES: Final = [
    ("empty-message", 150_000),
    ("three-signals", 100_000),
]


def _run_child(shape: str, frames: int) -> dict[str, float]:
    """Run one streaming session in a fresh interpreter; return its report."""
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join(p for p in sys.path if p)
    completed = subprocess.run(
        [sys.executable, str(_CHILD), shape, str(frames)],
        capture_output=True,
        text=True,
        check=False,
        env=env,
        timeout=600,
    )
    assert completed.returncode == 0, (
        f"residency child failed ({completed.returncode})\n"
        f"stdout: {completed.stdout}\nstderr: {completed.stderr}"
    )
    report: dict[str, float] = json.loads(completed.stdout)
    return report


@pytest.mark.parametrize(("shape", "frames"), _CASES)
def test_streaming_residency_is_bounded(shape: str, frames: int) -> None:
    """Streaming a few hundred thousand frames must not grow the heap with N."""
    report = _run_child(shape, frames)

    growth_kib = report["growth_kib"]
    per_frame_bytes = growth_kib * 1024 / frames

    assert growth_kib < _MAX_GROWTH_KIB, (
        f"streaming residency is not bounded for shape {shape!r}: "
        f"{growth_kib / 1024:.1f} MiB of peak growth over {frames:,} frames "
        f"({per_frame_bytes:.0f} B/frame), budget {_MAX_GROWTH_KIB / 1024:.0f} MiB. "
        "Residency proportional to the frame count means the streaming step is "
        "retaining every frame it accepted."
    )
