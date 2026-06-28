# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared benchmark helpers: DBC loaders, frame constants, system info, dataclasses.

Every benchmark script in this directory pulls DBC loaders, frame byte
arrays, ``get_system_info`` / ``get_rss_mb``, the canonical ``FrameSpec`` /
``BenchmarkConfig`` bundles, and the default LTL property sets from this
module so that a drift (e.g. a signal layout change for the CAN-FD frame
or a refactor of the property baseline) only has to be fixed in one place.
Keep the module-level constants ``bytes`` (not ``bytearray``) so a stray
mutation between runs cannot silently skew the numbers.

Per PY-31-1: this module is deliberately thin — each constant / function
has exactly one authoritative definition, and benchmark scripts import
what they need by name.  No re-export hoop, no star-imports; basedpyright
and pylint see a straight dependency.
"""

from __future__ import annotations

import json
import os
import platform
import resource
import time
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import TYPE_CHECKING

from aletheia import AletheiaClient, Signal
from aletheia.dbc import dbc_to_json
from aletheia.types import DBCDefinition, DLCCode, LTLFormula

if TYPE_CHECKING:
    from fractions import Fraction

# ``benchmarks/`` sits two levels below the repo root: python/benchmarks/X.py
# → ../../examples/.  Path is resolved once so re-importing this module
# is cheap; ``parents`` is immutable so no callers can mutate it.
_EXAMPLES_DIR = Path(__file__).resolve().parent.parent.parent / "examples"

# ============================================================================
# DBC loaders — single source for the demo databases used by every run.
# ============================================================================


def load_dbc() -> DBCDefinition:
    """Load the CAN 2.0B example DBC file."""
    return dbc_to_json(str(_EXAMPLES_DIR / "example.dbc"))


def load_canfd_dbc() -> DBCDefinition:
    """Load the CAN-FD example DBC file."""
    return dbc_to_json(str(_EXAMPLES_DIR / "example_canfd.dbc"))


# ============================================================================
# CAN 2.0B frame (DLC 8, 8 bytes).  Immutable ``bytes`` so an in-place
# rewrite during a benchmark cannot skew subsequent iterations.
# ============================================================================

CAN20_FRAME: bytes = bytes([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
CAN20_CAN_ID: int = 0x100
CAN20_DLC: DLCCode = DLCCode(8)
CAN20_SIGNALS: dict[str, int | Fraction] = {"EngineSpeed": 2000, "EngineTemp": 90}

# ============================================================================
# CAN-FD frame (DLC 15, 64 bytes) — sensor-fusion layout with realistic
# engineering values so the core's rational encoding path is exercised.
# ============================================================================

CANFD_FRAME: bytes = bytes(
    [0x00, 0xE1, 0xF5, 0x05]  # GPSLatitude  (raw ~100000000 → 10.0 deg)
    + [0x00, 0x6C, 0xDC, 0x02]  # GPSLongitude (raw ~48100000 → 4.81 deg)
    + [0xE8, 0x03]  # GPSAltitude  (raw 1000 → 100.0 m)
    + [0xD0, 0x07]  # GPSSpeed     (raw 2000 → 20.0 m/s)
    + [0x00, 0x00]  # YawRate      (raw 0 → 0.0 deg/s)
    + [0x00, 0x00]  # LateralAccel (raw 0)
    + [0x00, 0x00]  # LongAccel    (raw 0)
    + [0x00, 0x00]  # SteeringAngle(raw 0)
    + [0xE8, 0x03]  # WheelSpeedFL (raw 1000 → 10.0 m/s)
    + [0xE8, 0x03]  # WheelSpeedFR
    + [0xE8, 0x03]  # WheelSpeedRL
    + [0xE8, 0x03]  # WheelSpeedRR
    + [0x00] * 36  # Remaining signals + padding to 64 bytes
)
CANFD_CAN_ID: int = 0x200
CANFD_DLC: DLCCode = DLCCode(15)
CANFD_SIGNALS: dict[str, int | Fraction] = {
    "GPSSpeed": 20,
    "YawRate": 0,
    "WheelSpeedFL": 10,
    "WheelSpeedFR": 10,
}


# ============================================================================
# Frame spec — bundles the four parameters describing one CAN frame so that
# internal benchmark helpers can take a single ``spec`` argument instead of
# can_id + dlc + payload + signals.  Drops R0913 too-many-arguments on
# every per-frame helper from N+3 to N+0.  Frozen so a caller cannot
# mutate a shared spec mid-run.
# ============================================================================


@dataclass(frozen=True)
class FrameSpec:
    """Bundle of CAN frame parameters used by every per-frame benchmark.

    Frozen so a caller cannot mutate a shared spec mid-run; a stray write
    would silently skew downstream measurements.
    """

    can_id: int
    dlc: DLCCode
    payload: bytes
    signals: dict[str, int | Fraction]


CAN20_SPEC: FrameSpec = FrameSpec(
    CAN20_CAN_ID,
    CAN20_DLC,
    CAN20_FRAME,
    CAN20_SIGNALS,
)
CANFD_SPEC: FrameSpec = FrameSpec(
    CANFD_CAN_ID,
    CANFD_DLC,
    CANFD_FRAME,
    CANFD_SIGNALS,
)


# ============================================================================
# Default property bundles — the throughput / latency / scaling benchmarks
# all converged on the same baseline LTL property set per frame type.
# Duplicating them across files triggered R0801 duplicate-code.  These are
# the canonical defaults; a benchmark that needs a different shape (e.g.
# scaling.py exercising different formula counts) builds its own list.
# ============================================================================

DEFAULT_CAN20_PROPERTIES: list[LTLFormula] = [
    Signal("EngineSpeed").between(0, 8000).always().to_dict(),
    Signal("EngineTemp").between(-40, 215).always().to_dict(),
]

DEFAULT_CANFD_PROPERTIES: list[LTLFormula] = [
    Signal("GPSSpeed").between(0, 655).always().to_dict(),
    Signal("YawRate").between(-327, 327).always().to_dict(),
    Signal("WheelSpeedFL").between(0, 655).always().to_dict(),
]


# ============================================================================
# CLI config bundle — bundles common CLI knobs into one dataclass to drop
# the local-variable count of every main() entry point and keep helper
# signatures narrow.
# ============================================================================


@dataclass(frozen=True)
class BenchmarkConfig:
    """Per-run knobs used by main()-style benchmark entry points.

    Frozen so a benchmark cannot accidentally rewrite ``num_frames`` (or
    sibling) mid-run after print-prologue / pre-warmup work captured the
    initial value.  Construct once from ``argparse`` output, pass through.
    """

    num_frames: int
    num_runs: int = 5
    warmup_runs: int = 2
    json_output: bool = False


# ============================================================================
# Shared streaming-loop helpers — extracted from throughput / scaling /
# simplification (R0801 duplicate-code).  Caller owns Client lifecycle
# (parse_dbc / set_properties / start_stream / end_stream); these only
# time the inner per-frame loop.
# ============================================================================


def stream_frames(
    client: AletheiaClient,
    spec: FrameSpec,
    num_frames: int,
) -> float:
    """Time a streaming-mode ``send_frame`` loop.  Returns elapsed seconds.

    Caller is responsible for ``parse_dbc`` / ``set_properties`` /
    ``start_stream`` BEFORE this call, and ``end_stream`` AFTER.  Splitting
    timing from setup keeps each benchmark's setup-vs-measurement boundary
    visible and prevents any inadvertent inclusion of parse cost in the
    measured throughput.
    """
    start = time.perf_counter()
    for i in range(num_frames):
        client.send_frame(
            timestamp=i,
            can_id=spec.can_id,
            dlc=spec.dlc,
            data=spec.payload,
        )
    return time.perf_counter() - start


def run_streaming_benchmark(
    dbc: DBCDefinition,
    num_frames: int,
    spec: FrameSpec,
    properties: list[LTLFormula],
) -> tuple[float, float]:
    """End-to-end streaming benchmark: own a Client, parse, stream, end, close.

    Returns ``(frames_per_sec, elapsed_seconds)``.  Extracted from
    ``throughput.benchmark_streaming`` and ``scaling.benchmark_frames_per_sec``
    (R0801 duplicate-code) so the streaming-mode setup block lives in one
    place and any future change (e.g. wrapping in ``set_check_diagnostics``)
    only has to be applied here.
    """
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()
        elapsed = stream_frames(client, spec, num_frames)
        client.end_stream()
    return num_frames / elapsed, elapsed


def emit_json_report(name: str, results: object) -> None:
    """Print the canonical Aletheia benchmark JSON envelope to stdout.

    Schema (frozen by ``benchmarks/run_all.sh`` consumers and the cross-
    language baseline diff tooling): ``{benchmark, language, timestamp,
    system, results}`` — each benchmark's caller passes its own ``results``
    payload (dict or list) verbatim under the ``results`` key.
    """
    output = {
        "benchmark": name,
        "language": "python",
        "timestamp": datetime.now(UTC).isoformat(),
        "system": get_system_info(),
        "results": results,
    }
    print(json.dumps(output, indent=2))


# ============================================================================
# System info & RSS — attached to every JSON report so results can be
# cross-referenced against the hardware they were measured on.
# ============================================================================


def get_system_info() -> dict[str, object]:
    """Collect system information for benchmark metadata.

    Returned dict is JSON-safe (strings and ints) so the caller can embed
    it directly in the benchmark's stdout payload.
    """
    return {
        "cpu": platform.processor() or platform.machine(),
        "cores": os.cpu_count() or 0,
        "platform": platform.system(),
        "python": platform.python_version(),
    }


def get_rss_mb() -> float:
    """Return peak resident set size in MB (Linux ``ru_maxrss`` in KB).

    macOS reports ``ru_maxrss`` in bytes rather than kilobytes — the
    benchmarks run in Linux CI by policy (see run_all.sh) so we assume KB;
    a macOS path would need an ``if sys.platform == "darwin"`` scale of 1024.
    """
    usage = resource.getrusage(resource.RUSAGE_SELF)
    return usage.ru_maxrss / 1024.0
