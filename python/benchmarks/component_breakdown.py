#!/usr/bin/env python3
"""
Component Breakdown Benchmark

Measures time spent in each component of the pipeline:
1. Python JSON serialization (json.dumps)
2. Python JSON deserialization (json.loads)
3. IPC round-trip (echo command baseline)
4. Full streaming operation (for comparison)

This provides factual data to identify the actual bottleneck.

Usage:
    python3 component_breakdown.py [--ops N]
"""

import argparse
import json
import subprocess
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


def measure_json_dumps(num_ops: int) -> dict:
    """Measure json.dumps performance."""
    # Typical frame command
    command = {
        "command": "frame",
        "timestamp": 12345,
        "canId": 256,
        "data": [0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00],
    }

    start = time.perf_counter()
    for _ in range(num_ops):
        json.dumps(command)
    elapsed = time.perf_counter() - start

    return {
        "name": "json.dumps (frame command)",
        "total_us": elapsed * 1_000_000,
        "per_op_us": elapsed * 1_000_000 / num_ops,
        "ops_per_sec": num_ops / elapsed,
    }


def measure_json_loads(num_ops: int) -> dict:
    """Measure json.loads performance."""
    # Typical ack response
    response_str = '{"status":"ack","timestamp":12345}'

    start = time.perf_counter()
    for _ in range(num_ops):
        json.loads(response_str)
    elapsed = time.perf_counter() - start

    return {
        "name": "json.loads (ack response)",
        "total_us": elapsed * 1_000_000,
        "per_op_us": elapsed * 1_000_000 / num_ops,
        "ops_per_sec": num_ops / elapsed,
    }


def measure_json_roundtrip(num_ops: int) -> dict:
    """Measure combined json.dumps + json.loads."""
    command = {
        "command": "frame",
        "timestamp": 12345,
        "canId": 256,
        "data": [0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00],
    }
    response_str = '{"status":"ack","timestamp":12345}'

    start = time.perf_counter()
    for _ in range(num_ops):
        json.dumps(command)
        json.loads(response_str)
    elapsed = time.perf_counter() - start

    return {
        "name": "JSON roundtrip (dumps + loads)",
        "total_us": elapsed * 1_000_000,
        "per_op_us": elapsed * 1_000_000 / num_ops,
        "ops_per_sec": num_ops / elapsed,
    }


def measure_echo_roundtrip(num_ops: int) -> dict:
    """Measure IPC round-trip using echo command (minimal processing)."""
    dbc = load_dbc()

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Warmup
        for _ in range(100):
            client._send_command({"command": "echo", "message": "ping"})

        start = time.perf_counter()
        for _ in range(num_ops):
            client._send_command({"command": "echo", "message": "ping"})
        elapsed = time.perf_counter() - start

    return {
        "name": "Echo roundtrip (IPC baseline)",
        "total_us": elapsed * 1_000_000,
        "per_op_us": elapsed * 1_000_000 / num_ops,
        "ops_per_sec": num_ops / elapsed,
    }


def measure_streaming_frame(num_ops: int) -> dict:
    """Measure full streaming frame operation."""
    dbc = load_dbc()
    frame = [0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00]
    properties = [
        Signal("EngineSpeed").between(0, 8000).always().to_dict(),
        Signal("EngineTemp").between(-40, 215).always().to_dict(),
        Signal("BrakePressure").less_than(6553.5).always().to_dict(),
    ]

    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        # Warmup
        for i in range(100):
            client.send_frame(timestamp=i, can_id=0x100, data=frame)

        start = time.perf_counter()
        for i in range(num_ops):
            client.send_frame(timestamp=i, can_id=0x100, data=frame)
        elapsed = time.perf_counter() - start

        client.end_stream()

    return {
        "name": "Streaming frame (full pipeline)",
        "total_us": elapsed * 1_000_000,
        "per_op_us": elapsed * 1_000_000 / num_ops,
        "ops_per_sec": num_ops / elapsed,
    }


def measure_extract_signals(num_ops: int) -> dict:
    """Measure signal extraction operation."""
    dbc = load_dbc()
    frame = [0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00]

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Warmup
        for _ in range(100):
            client.extract_signals(can_id=0x100, data=frame)

        start = time.perf_counter()
        for _ in range(num_ops):
            client.extract_signals(can_id=0x100, data=frame)
        elapsed = time.perf_counter() - start

    return {
        "name": "Signal extraction (full pipeline)",
        "total_us": elapsed * 1_000_000,
        "per_op_us": elapsed * 1_000_000 / num_ops,
        "ops_per_sec": num_ops / elapsed,
    }


def print_result(result: dict):
    """Print a single benchmark result."""
    print(f"  {result['name']}")
    print(f"    Per-op: {result['per_op_us']:.1f} us")
    print(f"    Throughput: {result['ops_per_sec']:,.0f} ops/sec")
    print()


def main():
    parser = argparse.ArgumentParser(description="Component breakdown benchmark")
    parser.add_argument("--ops", type=int, default=5000, help="Operations per benchmark")
    args = parser.parse_args()

    print("=" * 70)
    print("Component Breakdown Benchmark")
    print("=" * 70)
    print(f"Operations per test: {args.ops:,}")
    print()

    results = []

    # 1. JSON serialization (Python-only)
    print("1. Measuring Python JSON serialization...")
    results.append(measure_json_dumps(args.ops))
    print_result(results[-1])

    # 2. JSON deserialization (Python-only)
    print("2. Measuring Python JSON deserialization...")
    results.append(measure_json_loads(args.ops))
    print_result(results[-1])

    # 3. JSON roundtrip (Python-only)
    print("3. Measuring Python JSON roundtrip...")
    results.append(measure_json_roundtrip(args.ops))
    print_result(results[-1])

    # 4. Echo roundtrip (IPC + minimal processing)
    print("4. Measuring echo roundtrip (IPC baseline)...")
    results.append(measure_echo_roundtrip(args.ops))
    print_result(results[-1])

    # 5. Full streaming frame
    print("5. Measuring streaming frame (full pipeline)...")
    results.append(measure_streaming_frame(args.ops))
    print_result(results[-1])

    # 6. Signal extraction
    print("6. Measuring signal extraction (full pipeline)...")
    results.append(measure_extract_signals(args.ops))
    print_result(results[-1])

    # Summary and breakdown
    print("=" * 70)
    print("Summary")
    print("=" * 70)
    print(f"{'Component':<40} {'Per-op (us)':>12} {'Throughput':>15}")
    print("-" * 70)
    for r in results:
        print(f"{r['name']:<40} {r['per_op_us']:>12.1f} {r['ops_per_sec']:>12,.0f}/s")

    # Calculate breakdown
    print()
    print("=" * 70)
    print("Breakdown Analysis")
    print("=" * 70)

    json_rt = next(r for r in results if "roundtrip" in r["name"] and "JSON" in r["name"])
    echo_rt = next(r for r in results if "Echo" in r["name"])
    stream_rt = next(r for r in results if "Streaming" in r["name"])

    json_us = json_rt["per_op_us"]
    echo_us = echo_rt["per_op_us"]
    stream_us = stream_rt["per_op_us"]

    # IPC overhead = echo - json (echo includes json + IPC)
    ipc_overhead = echo_us - json_us
    # Agda processing = stream - echo (stream includes echo + Agda logic)
    agda_processing = stream_us - echo_us

    print(f"Total streaming frame time:     {stream_us:>8.1f} us (100%)")
    print(f"  - JSON serialization:         {json_us:>8.1f} us ({json_us/stream_us*100:>5.1f}%)")
    print(f"  - IPC overhead (echo - JSON): {ipc_overhead:>8.1f} us ({ipc_overhead/stream_us*100:>5.1f}%)")
    print(f"  - Agda processing:            {agda_processing:>8.1f} us ({agda_processing/stream_us*100:>5.1f}%)")
    print()

    if ipc_overhead > agda_processing:
        print("CONCLUSION: IPC is the primary bottleneck")
    elif agda_processing > ipc_overhead:
        print("CONCLUSION: Agda processing is the primary bottleneck")
    else:
        print("CONCLUSION: IPC and Agda processing are roughly equal")

    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
