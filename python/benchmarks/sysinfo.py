# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""System Info & Docker Sizing Benchmark.

Runs a short benchmark and prints resource usage, throughput, and Docker
sizing recommendations. Designed for quick execution (~5s) so it can be
run in CI or during container setup.

Usage:
    python3 sysinfo.py
"""

from __future__ import annotations

import platform
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from multiprocessing import cpu_count

# Shared vocabulary lives in ``_common``; see PY-31-1 for the dedup rationale.
from benchmarks._common import (
    CAN20_SPEC,
    FrameSpec,
    get_rss_mb,
    load_dbc,
)

# See ``throughput.py`` — benchmarks import the installed package to keep
# the wheel / setuptools shim cost inside the measurement.
from aletheia import AletheiaClient, Signal

NUM_FRAMES = 2000
WARMUP = 100


@dataclass(frozen=True)
class MemorySnapshot:
    """RSS observations at each lifecycle stage of the benchmark."""

    baseline: float
    after_init: float
    after_dbc: float
    after_streaming: float
    peak: float


@dataclass(frozen=True)
class ThroughputSnapshot:
    """Frames-per-second for the three core operations."""

    streaming_fps: float
    extraction_fps: float
    building_fps: float


def _print_system_info() -> None:
    """Print Python, OS, CPU details."""
    print(f"\nPython:    {sys.version.split()[0]}")
    print(f"Platform:  {platform.platform()}")
    print(f"CPU cores: {cpu_count()}")
    print(f"Arch:      {platform.machine()}")


def _measure_streaming(client: AletheiaClient, spec: FrameSpec) -> float:
    """Run streaming-mode warmup + measurement, return fps."""
    properties = [
        Signal("EngineSpeed").between(0, 8000).always(),
        Signal("EngineTemp").between(-40, 215).always(),
        Signal("BrakePressure").less_than(Fraction("6553.5")).always(),
    ]
    client.set_properties([p.to_dict() for p in properties])
    client.start_stream()
    for i in range(WARMUP):
        client.send_frame(timestamp=i, can_id=spec.can_id, dlc=spec.dlc, data=spec.payload)
    start = time.perf_counter()
    # R0801 false positive: this per-frame send loop IS the throughput being
    # measured; the only cross-benchmark difference is the timestamp expression.
    # Extracting a shared helper would add a call per frame and skew the
    # measurement, so the loop is kept inline in each benchmark.
    # pylint: disable=duplicate-code
    for i in range(NUM_FRAMES):
        client.send_frame(
            timestamp=WARMUP + i,
            can_id=spec.can_id,
            dlc=spec.dlc,
            data=spec.payload,
        )
    # pylint: enable=duplicate-code
    elapsed = time.perf_counter() - start
    client.end_stream()
    return NUM_FRAMES / elapsed


def _measure_extraction(client: AletheiaClient, spec: FrameSpec) -> float:
    """Run extract_signals warmup + measurement, return fps."""
    for _ in range(WARMUP):
        client.extract_signals(can_id=spec.can_id, dlc=spec.dlc, data=spec.payload)
    start = time.perf_counter()
    for _ in range(NUM_FRAMES):
        client.extract_signals(can_id=spec.can_id, dlc=spec.dlc, data=spec.payload)
    elapsed = time.perf_counter() - start
    return NUM_FRAMES / elapsed


def _measure_building(client: AletheiaClient, spec: FrameSpec) -> float:
    """Run build_frame warmup + measurement, return fps."""
    for _ in range(WARMUP):
        client.build_frame(can_id=spec.can_id, dlc=spec.dlc, signals=spec.signals)
    start = time.perf_counter()
    for _ in range(NUM_FRAMES):
        client.build_frame(can_id=spec.can_id, dlc=spec.dlc, signals=spec.signals)
    elapsed = time.perf_counter() - start
    return NUM_FRAMES / elapsed


def _run_workload(spec: FrameSpec) -> tuple[MemorySnapshot, ThroughputSnapshot]:
    """Run the full memory + throughput probe; return both snapshots."""
    baseline = get_rss_mb()
    dbc = load_dbc()
    with AletheiaClient() as client:
        after_init = get_rss_mb()
        client.parse_dbc(dbc)
        after_dbc = get_rss_mb()
        streaming_fps = _measure_streaming(client, spec)
        after_streaming = get_rss_mb()
        extraction_fps = _measure_extraction(client, spec)
        building_fps = _measure_building(client, spec)
        # Capture peak RSS while resources are still alive (before __exit__).
        peak = get_rss_mb()
    mem = MemorySnapshot(baseline, after_init, after_dbc, after_streaming, peak)
    tput = ThroughputSnapshot(streaming_fps, extraction_fps, building_fps)
    return mem, tput


def _print_memory(mem: MemorySnapshot) -> None:
    """Print the memory-stage report block."""
    print(f"\n{'Memory (max RSS)':-<60}")
    print(f"  Baseline:         {mem.baseline:6.1f} MB")
    print(f"  After hs_init:    {mem.after_init:6.1f} MB")
    print(f"  After parse_dbc:  {mem.after_dbc:6.1f} MB")
    print(f"  After streaming:  {mem.after_streaming:6.1f} MB")
    print(f"  Peak:             {mem.peak:6.1f} MB")


def _print_throughput(tput: ThroughputSnapshot) -> None:
    """Print the throughput report block."""
    print(f"\n{'Throughput (2K frames, 1 run)':-<60}")
    print(
        f"  Streaming LTL:    {tput.streaming_fps:8,.0f} fps  "
        + f"({1e6 / tput.streaming_fps:6.0f} us/frame)"
    )
    print(
        f"  Signal Extraction:{tput.extraction_fps:8,.0f} fps  "
        + f"({1e6 / tput.extraction_fps:6.0f} us/frame)"
    )
    print(
        f"  Frame Building:   {tput.building_fps:8,.0f} fps  "
        + f"({1e6 / tput.building_fps:6.0f} us/frame)"
    )


def _print_docker(mem: MemorySnapshot) -> None:
    """Print the Docker-sizing recommendation."""
    # Use peak RSS + 50% headroom for GC spikes
    recommended_mem_mb = int(mem.peak * 1.5)
    # Round up to next 32 MB boundary for clean Docker values
    recommended_mem_mb = ((recommended_mem_mb + 31) // 32) * 32
    print(f"\n{'Docker Sizing Recommendation':-<60}")
    print("  --cpus=1          (GHC RTS is single-threaded)")
    print(f"  --memory={recommended_mem_mb}m       (peak {mem.peak:.0f} MB + 50% headroom)")
    print(f"\n  docker run --cpus=1 --memory={recommended_mem_mb}m your-image")


def main() -> int:
    """CLI entry point — measure resources and print sizing recommendations."""
    print("=" * 60)
    print("Aletheia System Info & Docker Sizing")
    print("=" * 60)

    _print_system_info()
    mem, tput = _run_workload(CAN20_SPEC)
    _print_memory(mem)
    _print_throughput(tput)
    _print_docker(mem)

    print("=" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(main())
