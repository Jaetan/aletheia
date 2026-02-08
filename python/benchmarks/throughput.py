#!/usr/bin/env python3
"""
Throughput Benchmark

Measures frames per second through the full Aletheia pipeline:
Python -> FFI (ctypes) -> Haskell/MAlonzo/Agda -> back

Usage:
    python3 throughput.py [--frames N] [--runs N] [--warmup N]
"""

import argparse
import statistics
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json


def load_dbc() -> dict:
    """Load the example DBC file."""
    dbc_path = Path(__file__).parent.parent.parent / "examples" / "example.dbc"
    return dbc_to_json(str(dbc_path))


def benchmark_streaming(dbc: dict, num_frames: int, num_properties: int = 3) -> float:
    """
    Benchmark streaming throughput.

    Returns frames per second.
    """
    # Define properties based on count requested
    all_properties = [
        Signal("EngineSpeed").between(0, 8000).always(),
        Signal("EngineTemp").between(-40, 215).always(),
        Signal("BrakePressure").less_than(6553.5).always(),
    ]
    properties = [p.to_dict() for p in all_properties[:num_properties]]

    # Test frame: EngineSpeed=2000rpm, EngineTemp=90C
    frame = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])

    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        start = time.perf_counter()
        for i in range(num_frames):
            client.send_frame(timestamp=i, can_id=0x100, data=frame)
        elapsed = time.perf_counter() - start

        client.end_stream()

    return num_frames / elapsed


def benchmark_signal_extraction(dbc: dict, num_frames: int) -> float:
    """
    Benchmark signal extraction throughput (no streaming).

    Returns extractions per second.
    """
    frame = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        start = time.perf_counter()
        for _ in range(num_frames):
            client.extract_signals(can_id=0x100, data=frame)
        elapsed = time.perf_counter() - start

    return num_frames / elapsed


def benchmark_frame_building(dbc: dict, num_frames: int) -> float:
    """
    Benchmark frame building throughput.

    Returns builds per second.
    """
    signals = {"EngineSpeed": 2000.0, "EngineTemp": 90.0}

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        start = time.perf_counter()
        for _ in range(num_frames):
            client.build_frame(can_id=0x100, signals=signals)
        elapsed = time.perf_counter() - start

    return num_frames / elapsed


def run_benchmark(
    name: str,
    func,
    dbc: dict,
    num_frames: int,
    num_runs: int,
    warmup_runs: int,
) -> dict:
    """Run a benchmark multiple times and collect statistics."""
    # Warmup
    for _ in range(warmup_runs):
        func(dbc, num_frames // 10)  # Smaller warmup

    # Actual runs
    results = []
    for run in range(num_runs):
        fps = func(dbc, num_frames)
        results.append(fps)
        print(f"  Run {run + 1}/{num_runs}: {fps:,.0f} ops/sec")

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
    args = parser.parse_args()

    print("=" * 70)
    print("Aletheia Throughput Benchmark")
    print("=" * 70)
    print(f"Frames per run: {args.frames:,}")
    print(f"Runs: {args.runs}")
    print(f"Warmup runs: {args.warmup}")
    print()

    dbc = load_dbc()

    benchmarks = [
        ("Streaming LTL (3 properties)", benchmark_streaming),
        ("Signal Extraction", benchmark_signal_extraction),
        ("Frame Building", benchmark_frame_building),
    ]

    results = []
    for name, func in benchmarks:
        print(f"\n{name}:")
        print("-" * 40)
        result = run_benchmark(name, func, dbc, args.frames, args.runs, args.warmup)
        results.append(result)

    # Summary
    print("\n" + "=" * 70)
    print("Summary")
    print("=" * 70)
    print(f"{'Benchmark':<35} {'Mean':>12} {'Stdev':>10} {'Min':>10} {'Max':>10}")
    print("-" * 70)
    for r in results:
        print(f"{r['name']:<35} {r['mean']:>10,.0f}/s {r['stdev']:>9,.0f} {r['min']:>9,.0f} {r['max']:>9,.0f}")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
