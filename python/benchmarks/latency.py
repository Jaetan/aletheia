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
import sys
import time
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
# Frame definitions
# ============================================================================

CAN20_FRAME = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
CAN20_CAN_ID = 0x100
CAN20_DLC = 8
CAN20_SIGNALS = {"EngineSpeed": 2000.0, "EngineTemp": 90.0}

CANFD_FRAME = bytearray(
    [0x00, 0xE1, 0xF5, 0x05]
    + [0x00, 0x6C, 0xDC, 0x02]
    + [0xE8, 0x03]
    + [0xD0, 0x07]
    + [0x00, 0x00]
    + [0x00, 0x00]
    + [0x00, 0x00]
    + [0x00, 0x00]
    + [0xE8, 0x03]
    + [0xE8, 0x03]
    + [0xE8, 0x03]
    + [0xE8, 0x03]
    + [0x00] * 36
)
CANFD_CAN_ID = 0x200
CANFD_DLC = 15
CANFD_SIGNALS = {"GPSSpeed": 20.0, "YawRate": 0.0, "WheelSpeedFL": 10.0, "WheelSpeedFR": 10.0}


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
    frame: bytearray,
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
            client.build_frame(can_id=can_id, signals=signals, dlc=dlc)
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


def run_latency_suite(
    label: str,
    dbc: dict,
    can_id: int,
    dlc: int,
    frame: bytearray,
    signals: dict[str, float],
    properties: list[dict],
    num_ops: int,
    warmup: int,
) -> list[tuple[str, dict]]:
    """Run streaming, extraction, and build latency for one frame type."""
    all_stats = []

    # Streaming latency
    print(f"\nBenchmarking {label} streaming...")
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        for i in range(warmup):
            client.send_frame(timestamp=i, can_id=can_id, dlc=dlc, data=frame)

        latencies = measure_latencies(client, "stream", num_ops, can_id, dlc, frame, signals)
        client.end_stream()

    stats = analyze_latencies(latencies)
    print_latency_stats(f"{label} Streaming LTL", stats)
    all_stats.append((f"{label} Streaming LTL", stats))

    # Extraction latency
    print(f"\nBenchmarking {label} signal extraction...")
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        for _ in range(warmup):
            client.extract_signals(can_id=can_id, dlc=dlc, data=frame)

        latencies = measure_latencies(client, "extract", num_ops, can_id, dlc, frame, signals)

    stats = analyze_latencies(latencies)
    print_latency_stats(f"{label} Signal Extraction", stats)
    all_stats.append((f"{label} Signal Extraction", stats))

    # Frame building latency
    print(f"\nBenchmarking {label} frame building...")
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        for _ in range(warmup):
            client.build_frame(can_id=can_id, signals=signals, dlc=dlc)

        latencies = measure_latencies(client, "build", num_ops, can_id, dlc, frame, signals)

    stats = analyze_latencies(latencies)
    print_latency_stats(f"{label} Frame Building", stats)
    all_stats.append((f"{label} Frame Building", stats))

    return all_stats


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
        can20_properties, args.ops, args.warmup,
    )

    # CAN-FD suite
    all_stats += run_latency_suite(
        "CAN-FD", canfd_dbc,
        CANFD_CAN_ID, CANFD_DLC, CANFD_FRAME, CANFD_SIGNALS,
        canfd_properties, args.ops, args.warmup,
    )

    # Summary table
    print("\n" + "=" * 70)
    print("Summary (all times in microseconds)")
    print("=" * 70)
    print(f"{'Operation':<30} {'Mean':>10} {'p50':>10} {'p99':>10} {'p99.9':>10}")
    print("-" * 70)
    for name, stats in all_stats:
        print(
            f"{name:<30} {stats['mean_us']:>10.1f} {stats['p50_us']:>10.1f} "
            f"{stats['p99_us']:>10.1f} {stats['p999_us']:>10.1f}"
        )
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
