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
import statistics
import sys
import time
from datetime import datetime, timezone

# Benchmarks import the *installed* package (``pip install -e .[dev]``) so
# that any wheel/setuptools shim overhead shows up in the numbers — matches
# how end users measure Aletheia in production.  Do not reintroduce
# ``sys.path.insert`` here; it hid the install-path cost from earlier runs.
from aletheia import AletheiaClient, Signal
# Shared benchmark vocabulary — DBC loaders, frame constants, system info.
# Consolidating these in ``_common.py`` keeps the five benchmark scripts
# from drifting apart; see PY-31-1.
from ._common import (
    CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME, CAN20_SIGNALS,
    CANFD_CAN_ID, CANFD_DLC, CANFD_FRAME, CANFD_SIGNALS,
    get_system_info, load_canfd_dbc, load_dbc,
)


# ============================================================================
# Benchmark functions
# ============================================================================

def benchmark_streaming(
    dbc: dict, num_frames: int, *,
    can_id: int, dlc: int, frame: bytes,
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
    can_id: int, dlc: int, frame: bytes,
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
    for _ in range(num_runs):
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
