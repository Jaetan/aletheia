#!/usr/bin/env python3
"""
Latency Benchmark

Measures per-operation latency distribution through the Aletheia pipeline.
Reports percentiles (p50, p90, p99, p99.9) to understand tail latency.

Usage:
    python3 latency.py [--ops N] [--warmup N]
"""

import argparse
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


def percentile(data: list[float], p: float) -> float:
    """Calculate percentile of sorted data."""
    if not data:
        return 0.0
    k = (len(data) - 1) * p / 100
    f = int(k)
    c = f + 1 if f + 1 < len(data) else f
    return data[f] + (k - f) * (data[c] - data[f])


def measure_latencies(
    client: AletheiaClient,
    operation: str,
    num_ops: int,
    frame: bytearray,
    signals: dict[str, float] = {},
) -> list[float]:
    """Measure latency for each operation."""
    latencies = []

    for i in range(num_ops):
        if operation == "stream":
            start = time.perf_counter()
            client.send_frame(timestamp=i, can_id=0x100, data=frame)
            latencies.append(time.perf_counter() - start)
        elif operation == "extract":
            start = time.perf_counter()
            client.extract_signals(can_id=0x100, data=frame)
            latencies.append(time.perf_counter() - start)
        elif operation == "build":
            start = time.perf_counter()
            client.build_frame(can_id=0x100, signals=signals)
            latencies.append(time.perf_counter() - start)

    return latencies


def analyze_latencies(latencies: list[float]) -> dict:
    """Analyze latency distribution."""
    sorted_lat = sorted(latencies)
    return {
        "count": len(latencies),
        "mean_us": sum(latencies) / len(latencies) * 1_000_000,
        "min_us": min(latencies) * 1_000_000,
        "max_us": max(latencies) * 1_000_000,
        "p50_us": percentile(sorted_lat, 50) * 1_000_000,
        "p90_us": percentile(sorted_lat, 90) * 1_000_000,
        "p99_us": percentile(sorted_lat, 99) * 1_000_000,
        "p999_us": percentile(sorted_lat, 99.9) * 1_000_000,
    }


def print_latency_stats(name: str, stats: dict):
    """Print latency statistics."""
    print(f"\n{name}:")
    print("-" * 50)
    print(f"  Count:    {stats['count']:,} operations")
    print(f"  Mean:     {stats['mean_us']:,.1f} us")
    print(f"  Min:      {stats['min_us']:,.1f} us")
    print(f"  Max:      {stats['max_us']:,.1f} us")
    print(f"  p50:      {stats['p50_us']:,.1f} us")
    print(f"  p90:      {stats['p90_us']:,.1f} us")
    print(f"  p99:      {stats['p99_us']:,.1f} us")
    print(f"  p99.9:    {stats['p999_us']:,.1f} us")
    print(f"  Implied:  {1_000_000 / stats['mean_us']:,.0f} ops/sec (from mean)")


def main():
    parser = argparse.ArgumentParser(description="Latency benchmark")
    parser.add_argument("--ops", type=int, default=5000, help="Operations to measure")
    parser.add_argument("--warmup", type=int, default=500, help="Warmup operations")
    args = parser.parse_args()

    print("=" * 70)
    print("Aletheia Latency Benchmark")
    print("=" * 70)
    print(f"Operations: {args.ops:,}")
    print(f"Warmup: {args.warmup:,}")

    dbc = load_dbc()
    frame = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
    signals = {"EngineSpeed": 2000.0, "EngineTemp": 90.0}

    properties = [
        Signal("EngineSpeed").between(0, 8000).always().to_dict(),
        Signal("EngineTemp").between(-40, 215).always().to_dict(),
        Signal("BrakePressure").less_than(6553.5).always().to_dict(),
    ]

    # Streaming latency
    print("\nBenchmarking streaming...")
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        # Warmup
        for i in range(args.warmup):
            client.send_frame(timestamp=i, can_id=0x100, data=frame)

        # Measure
        latencies = measure_latencies(client, "stream", args.ops, frame)
        client.end_stream()

    stream_stats = analyze_latencies(latencies)
    print_latency_stats("Streaming LTL (3 properties)", stream_stats)

    # Extraction latency
    print("\nBenchmarking signal extraction...")
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Warmup
        for _ in range(args.warmup):
            client.extract_signals(can_id=0x100, data=frame)

        # Measure
        latencies = measure_latencies(client, "extract", args.ops, frame)

    extract_stats = analyze_latencies(latencies)
    print_latency_stats("Signal Extraction", extract_stats)

    # Frame building latency
    print("\nBenchmarking frame building...")
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Warmup
        for _ in range(args.warmup):
            client.build_frame(can_id=0x100, signals=signals)

        # Measure
        latencies = measure_latencies(client, "build", args.ops, frame, signals)

    build_stats = analyze_latencies(latencies)
    print_latency_stats("Frame Building", build_stats)

    # Summary table
    print("\n" + "=" * 70)
    print("Summary (all times in microseconds)")
    print("=" * 70)
    print(f"{'Operation':<25} {'Mean':>10} {'p50':>10} {'p99':>10} {'p99.9':>10}")
    print("-" * 70)
    for name, stats in [
        ("Streaming LTL", stream_stats),
        ("Signal Extraction", extract_stats),
        ("Frame Building", build_stats),
    ]:
        print(
            f"{name:<25} {stats['mean_us']:>10.1f} {stats['p50_us']:>10.1f} "
            f"{stats['p99_us']:>10.1f} {stats['p999_us']:>10.1f}"
        )
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
