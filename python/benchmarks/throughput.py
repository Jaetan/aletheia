#!/usr/bin/env python3
"""
Throughput Benchmark

Measures frames per second through the full Aletheia pipeline:
Python -> FFI (ctypes) -> Haskell/MAlonzo/Agda -> back

Tests both CAN 2.0B (8-byte) and CAN-FD (64-byte) frames.

Usage:
    python3 throughput.py [--frames N] [--runs N] [--warmup N]
"""

import argparse
import json
import os
import platform
import statistics
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json

EXAMPLES_DIR = Path(__file__).parent.parent.parent / "examples"


# ============================================================================
# DBC loaders
# ============================================================================

def load_dbc() -> dict:
    """Load the CAN 2.0B example DBC file."""
    return dbc_to_json(str(EXAMPLES_DIR / "example.dbc"))


def load_canfd_dbc() -> dict:
    """Load the CAN-FD example DBC file."""
    return dbc_to_json(str(EXAMPLES_DIR / "example_canfd.dbc"))


# ============================================================================
# CAN 2.0B frames (DLC 8, 8 bytes)
# ============================================================================

CAN20_FRAME = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
CAN20_CAN_ID = 0x100
CAN20_DLC = 8
CAN20_SIGNALS = {"EngineSpeed": 2000.0, "EngineTemp": 90.0}

# ============================================================================
# CAN-FD frames (DLC 15, 64 bytes)
# ============================================================================

# 64-byte sensor fusion frame with realistic values
CANFD_FRAME = bytearray(
    [0x00, 0xE1, 0xF5, 0x05]   # GPSLatitude  (raw ~100000000 → 10.0 deg)
    + [0x00, 0x6C, 0xDC, 0x02]  # GPSLongitude (raw ~48100000 → 4.81 deg)
    + [0xE8, 0x03]               # GPSAltitude  (raw 1000 → 100.0 m)
    + [0xD0, 0x07]               # GPSSpeed     (raw 2000 → 20.0 m/s)
    + [0x00, 0x00]               # YawRate      (raw 0 → 0.0 deg/s)
    + [0x00, 0x00]               # LateralAccel (raw 0)
    + [0x00, 0x00]               # LongAccel    (raw 0)
    + [0x00, 0x00]               # SteeringAngle(raw 0)
    + [0xE8, 0x03]               # WheelSpeedFL (raw 1000 → 10.0 m/s)
    + [0xE8, 0x03]               # WheelSpeedFR (raw 1000 → 10.0 m/s)
    + [0xE8, 0x03]               # WheelSpeedRL
    + [0xE8, 0x03]               # WheelSpeedRR
    + [0x00] * 36                # Remaining signals + padding to 64 bytes
)
CANFD_CAN_ID = 0x200
CANFD_DLC = 15
CANFD_SIGNALS = {
    "GPSSpeed": 20.0,
    "YawRate": 0.0,
    "WheelSpeedFL": 10.0,
    "WheelSpeedFR": 10.0,
}


# ============================================================================
# Benchmark functions
# ============================================================================

def benchmark_streaming(
    dbc: dict, num_frames: int, *,
    can_id: int, dlc: int, frame: bytearray,
    properties: list[dict],
) -> float:
    """Benchmark streaming throughput. Returns frames per second."""
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        start = time.perf_counter()
        for i in range(num_frames):
            client.send_frame(timestamp=i, can_id=can_id, dlc=dlc, data=frame)
        elapsed = time.perf_counter() - start

        client.end_stream()

    return num_frames / elapsed


def benchmark_signal_extraction(
    dbc: dict, num_frames: int, *,
    can_id: int, dlc: int, frame: bytearray,
) -> float:
    """Benchmark signal extraction throughput. Returns extractions per second."""
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        start = time.perf_counter()
        for _ in range(num_frames):
            client.extract_signals(can_id=can_id, dlc=dlc, data=frame)
        elapsed = time.perf_counter() - start

    return num_frames / elapsed


def benchmark_frame_building(
    dbc: dict, num_frames: int, *,
    can_id: int, dlc: int, signals: dict[str, float],
) -> float:
    """Benchmark frame building throughput. Returns builds per second."""
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        start = time.perf_counter()
        for _ in range(num_frames):
            client.build_frame(can_id=can_id, dlc=dlc, signals=signals)
        elapsed = time.perf_counter() - start

    return num_frames / elapsed


# ============================================================================
# Runner
# ============================================================================

def run_benchmark(
    name: str,
    func,
    num_frames: int,
    num_runs: int,
    warmup_runs: int,
) -> dict:
    """Run a benchmark multiple times and collect statistics."""
    # Warmup
    for _ in range(warmup_runs):
        func(num_frames // 10)  # Smaller warmup

    # Actual runs
    results = []
    for run in range(num_runs):
        fps = func(num_frames)
        results.append(fps)

    return {
        "name": name,
        "num_frames": num_frames,
        "num_runs": num_runs,
        "mean": statistics.mean(results),
        "stdev": statistics.stdev(results) if len(results) > 1 else 0,
        "min": min(results),
        "max": max(results),
        "results": results,
    }


def get_system_info() -> dict:
    """Collect system information for benchmark metadata."""
    return {
        "cpu": platform.processor() or platform.machine(),
        "cores": os.cpu_count() or 0,
        "platform": platform.system(),
        "python": platform.python_version(),
    }


def main():
    parser = argparse.ArgumentParser(description="Throughput benchmark")
    parser.add_argument("--frames", type=int, default=10000, help="Frames per run")
    parser.add_argument("--runs", type=int, default=5, help="Number of runs")
    parser.add_argument("--warmup", type=int, default=2, help="Warmup runs")
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    args = parser.parse_args()

    out = sys.stderr if args.json else sys.stdout

    print("=" * 70, file=out)
    print("Aletheia Throughput Benchmark", file=out)
    print("=" * 70, file=out)
    print(f"Frames per run: {args.frames:,}", file=out)
    print(f"Runs: {args.runs}", file=out)
    print(f"Warmup runs: {args.warmup}", file=out)

    dbc = load_dbc()
    canfd_dbc = load_canfd_dbc()

    # CAN 2.0B properties (on EngineStatus message)
    can20_properties = [
        Signal("EngineSpeed").between(0, 8000).always().to_dict(),
        Signal("EngineTemp").between(-40, 215).always().to_dict(),
    ]

    # CAN-FD properties (on SensorFusion message)
    canfd_properties = [
        Signal("GPSSpeed").between(0, 655).always().to_dict(),
        Signal("YawRate").between(-327, 327).always().to_dict(),
        Signal("WheelSpeedFL").between(0, 655).always().to_dict(),
    ]

    benchmarks = [
        # --- CAN 2.0B ---
        ("CAN 2.0B: Stream LTL (2 props)", lambda n: benchmark_streaming(
            dbc, n, can_id=CAN20_CAN_ID, dlc=CAN20_DLC, frame=CAN20_FRAME,
            properties=can20_properties)),
        ("CAN 2.0B: Signal Extraction", lambda n: benchmark_signal_extraction(
            dbc, n, can_id=CAN20_CAN_ID, dlc=CAN20_DLC, frame=CAN20_FRAME)),
        ("CAN 2.0B: Frame Building", lambda n: benchmark_frame_building(
            dbc, n, can_id=CAN20_CAN_ID, dlc=CAN20_DLC, signals=CAN20_SIGNALS)),

        # --- CAN-FD ---
        ("CAN-FD:   Stream LTL (3 props)", lambda n: benchmark_streaming(
            canfd_dbc, n, can_id=CANFD_CAN_ID, dlc=CANFD_DLC, frame=CANFD_FRAME,
            properties=canfd_properties)),
        ("CAN-FD:   Signal Extraction", lambda n: benchmark_signal_extraction(
            canfd_dbc, n, can_id=CANFD_CAN_ID, dlc=CANFD_DLC, frame=CANFD_FRAME)),
        ("CAN-FD:   Frame Building", lambda n: benchmark_frame_building(
            canfd_dbc, n, can_id=CANFD_CAN_ID, dlc=CANFD_DLC, signals=CANFD_SIGNALS)),
    ]

    results = []
    for name, func in benchmarks:
        print(f"\n{name}:", file=out)
        print("-" * 40, file=out)
        result = run_benchmark(name, func, args.frames, args.runs, args.warmup)
        results.append(result)
        for run_idx, fps in enumerate(result["results"]):
            print(f"  Run {run_idx + 1}/{args.runs}: {fps:,.0f} ops/sec", file=out)

    # Summary
    print("\n" + "=" * 70, file=out)
    print("Summary", file=out)
    print("=" * 70, file=out)
    print(f"{'Benchmark':<35} {'Mean':>12} {'Stdev':>10} {'Min':>10} {'Max':>10}", file=out)
    print("-" * 80, file=out)
    for r in results:
        print(
            f"{r['name']:<35} {r['mean']:>10,.0f}/s "
            f"{r['stdev']:>9,.0f} {r['min']:>9,.0f} {r['max']:>9,.0f}",
            file=out,
        )
    print("=" * 70, file=out)

    if args.json:
        json_results = []
        for r in results:
            json_results.append({
                "name": r["name"],
                "frames": r["num_frames"],
                "runs": r["num_runs"],
                "fps_mean": round(r["mean"], 1),
                "fps_stdev": round(r["stdev"], 1),
                "fps_min": round(r["min"], 1),
                "fps_max": round(r["max"], 1),
                "us_per_frame": round(1_000_000 / r["mean"], 1) if r["mean"] > 0 else 0,
            })
        output = {
            "benchmark": "throughput",
            "language": "python",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "system": get_system_info(),
            "results": json_results,
        }
        print(json.dumps(output, indent=2))

    return 0


if __name__ == "__main__":
    sys.exit(main())
