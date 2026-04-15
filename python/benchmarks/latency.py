#!/usr/bin/env python3
"""
Latency Benchmark

Measures per-operation latency distribution through the Aletheia pipeline.
Reports percentiles (p50, p90, p99, p99.9) to understand tail latency.

Tests both CAN 2.0B (8-byte) and CAN-FD (64-byte) frames.

Usage:
    python3 latency.py [--ops N] [--warmup N]
"""

import argparse
import json
import sys
import time
from datetime import datetime, timezone

# See ``throughput.py`` — benchmarks import the installed package to keep
# the wheel / setuptools shim cost inside the measurement.
from aletheia import AletheiaClient, Signal
# Shared vocabulary lives in ``_common``; see PY-31-1 for the dedup rationale.
from ._common import (
    CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME, CAN20_SIGNALS,
    CANFD_CAN_ID, CANFD_DLC, CANFD_FRAME, CANFD_SIGNALS,
    get_system_info, load_canfd_dbc, load_dbc,
)


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
    can_id: int,
    dlc: int,
    frame: bytes,
    signals: dict[str, float],
) -> list[float]:
    """Measure latency for each operation."""
    latencies = []

    for i in range(num_ops):
        if operation == "stream":
            start = time.perf_counter()
            client.send_frame(timestamp=i, can_id=can_id, dlc=dlc, data=frame)
            latencies.append(time.perf_counter() - start)
        elif operation == "extract":
            start = time.perf_counter()
            client.extract_signals(can_id=can_id, dlc=dlc, data=frame)
            latencies.append(time.perf_counter() - start)
        elif operation == "build":
            start = time.perf_counter()
            client.build_frame(can_id=can_id, dlc=dlc, signals=signals)
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


def print_latency_stats(name: str, stats: dict, file=None):
    """Print latency statistics."""
    out = file or sys.stdout
    print(f"\n{name}:", file=out)
    print("-" * 50, file=out)
    print(f"  Count:    {stats['count']:,} operations", file=out)
    print(f"  Mean:     {stats['mean_us']:,.1f} us", file=out)
    print(f"  Min:      {stats['min_us']:,.1f} us", file=out)
    print(f"  Max:      {stats['max_us']:,.1f} us", file=out)
    print(f"  p50:      {stats['p50_us']:,.1f} us", file=out)
    print(f"  p90:      {stats['p90_us']:,.1f} us", file=out)
    print(f"  p99:      {stats['p99_us']:,.1f} us", file=out)
    print(f"  p99.9:    {stats['p999_us']:,.1f} us", file=out)
    print(f"  Implied:  {1_000_000 / stats['mean_us']:,.0f} ops/sec (from mean)", file=out)


def run_latency_suite(
    label: str,
    dbc: dict,
    can_id: int,
    dlc: int,
    frame: bytes,
    signals: dict[str, float],
    properties: list[dict],
    num_ops: int,
    warmup: int,
    file=None,
) -> list[tuple[str, dict]]:
    """Run streaming, extraction, and build latency for one frame type."""
    out = file or sys.stdout
    all_stats = []

    # Streaming latency
    print(f"\nBenchmarking {label} streaming...", file=out)
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        for i in range(warmup):
            client.send_frame(timestamp=i, can_id=can_id, dlc=dlc, data=frame)

        latencies = measure_latencies(client, "stream", num_ops, can_id, dlc, frame, signals)
        client.end_stream()

    stats = analyze_latencies(latencies)
    print_latency_stats(f"{label} Streaming LTL", stats, file=out)
    all_stats.append((f"{label} Streaming LTL", stats))

    # Extraction latency
    print(f"\nBenchmarking {label} signal extraction...", file=out)
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        for _ in range(warmup):
            client.extract_signals(can_id=can_id, dlc=dlc, data=frame)

        latencies = measure_latencies(client, "extract", num_ops, can_id, dlc, frame, signals)

    stats = analyze_latencies(latencies)
    print_latency_stats(f"{label} Signal Extraction", stats, file=out)
    all_stats.append((f"{label} Signal Extraction", stats))

    # Frame building latency
    print(f"\nBenchmarking {label} frame building...", file=out)
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        for _ in range(warmup):
            client.build_frame(can_id=can_id, dlc=dlc, signals=signals)

        latencies = measure_latencies(client, "build", num_ops, can_id, dlc, frame, signals)

    stats = analyze_latencies(latencies)
    print_latency_stats(f"{label} Frame Building", stats, file=out)
    all_stats.append((f"{label} Frame Building", stats))

    return all_stats


def main():
    parser = argparse.ArgumentParser(description="Latency benchmark")
    parser.add_argument("--ops", type=int, default=5000, help="Operations to measure")
    parser.add_argument("--warmup", type=int, default=500, help="Warmup operations")
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    args = parser.parse_args()

    out = sys.stderr if args.json else sys.stdout

    print("=" * 70, file=out)
    print("Aletheia Latency Benchmark", file=out)
    print("=" * 70, file=out)
    print(f"Operations: {args.ops:,}", file=out)
    print(f"Warmup: {args.warmup:,}", file=out)

    dbc = load_dbc()
    canfd_dbc = load_canfd_dbc()

    can20_properties = [
        Signal("EngineSpeed").between(0, 8000).always().to_dict(),
        Signal("EngineTemp").between(-40, 215).always().to_dict(),
    ]

    canfd_properties = [
        Signal("GPSSpeed").between(0, 655).always().to_dict(),
        Signal("YawRate").between(-327, 327).always().to_dict(),
        Signal("WheelSpeedFL").between(0, 655).always().to_dict(),
    ]

    # CAN 2.0B suite
    all_stats = run_latency_suite(
        "CAN 2.0B", dbc,
        CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME, CAN20_SIGNALS,
        can20_properties, args.ops, args.warmup, file=out,
    )

    # CAN-FD suite
    all_stats += run_latency_suite(
        "CAN-FD", canfd_dbc,
        CANFD_CAN_ID, CANFD_DLC, CANFD_FRAME, CANFD_SIGNALS,
        canfd_properties, args.ops, args.warmup, file=out,
    )

    # Summary table
    print("\n" + "=" * 70, file=out)
    print("Summary (all times in microseconds)", file=out)
    print("=" * 70, file=out)
    print(f"{'Operation':<30} {'Mean':>10} {'p50':>10} {'p99':>10} {'p99.9':>10}", file=out)
    print("-" * 70, file=out)
    for name, stats in all_stats:
        print(
            f"{name:<30} {stats['mean_us']:>10.1f} {stats['p50_us']:>10.1f} "
            + f"{stats['p99_us']:>10.1f} {stats['p999_us']:>10.1f}",
            file=out,
        )
    print("=" * 70, file=out)

    if args.json:
        json_results = []
        for name, stats in all_stats:
            json_results.append({
                "name": name,
                "count": stats["count"],
                "mean_us": round(stats["mean_us"], 1),
                "min_us": round(stats["min_us"], 1),
                "max_us": round(stats["max_us"], 1),
                "p50_us": round(stats["p50_us"], 1),
                "p90_us": round(stats["p90_us"], 1),
                "p99_us": round(stats["p99_us"], 1),
                "p999_us": round(stats["p999_us"], 1),
            })
        output = {
            "benchmark": "latency",
            "language": "python",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "system": get_system_info(),
            "results": json_results,
        }
        print(json.dumps(output, indent=2))

    return 0


if __name__ == "__main__":
    sys.exit(main())
