#!/usr/bin/env python3
"""
Scaling Benchmark

Measures how Aletheia performance scales with:
- Trace size (1K to 100K frames)
- Property count (1 to 10 properties)
- Property complexity (simple vs nested temporal operators)

Tests both CAN 2.0B and CAN-FD frames for trace size scaling.

Usage:
    python3 scaling.py [--quick]
"""

import argparse
import json
import os
import platform
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json

EXAMPLES_DIR = Path(__file__).parent.parent.parent / "examples"


def load_dbc() -> dict:
    """Load the CAN 2.0B example DBC file."""
    return dbc_to_json(str(EXAMPLES_DIR / "example.dbc"))


def load_canfd_dbc() -> dict:
    """Load the CAN-FD example DBC file."""
    return dbc_to_json(str(EXAMPLES_DIR / "example_canfd.dbc"))


CAN20_FRAME = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
CAN20_CAN_ID = 0x100
CAN20_DLC = 8

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


def benchmark_frames_per_sec(
    dbc: dict,
    num_frames: int,
    properties: list[dict],
    can_id: int,
    dlc: int,
    frame: bytearray,
) -> tuple[float, float]:
    """Benchmark streaming throughput. Returns (frames_per_sec, total_time)."""
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        start = time.perf_counter()
        for i in range(num_frames):
            client.send_frame(timestamp=i, can_id=can_id, dlc=dlc, data=frame)
        elapsed = time.perf_counter() - start

        client.end_stream()

    return num_frames / elapsed, elapsed


def test_trace_size_scaling(dbc: dict, quick: bool = False, file=None) -> list[dict]:
    """Test how throughput scales with trace size (CAN 2.0B)."""
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("1. Trace Size Scaling (CAN 2.0B)", file=out)
    print("=" * 70, file=out)
    print("Testing throughput as trace size increases...", file=out)
    print("(Verifies O(1) memory and constant throughput)", file=out)
    print(file=out)

    properties = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]
    sizes = [1000, 5000, 10000, 50000] if quick else [1000, 5000, 10000, 50000, 100000]

    print(f"{'Frames':>10} {'Time (s)':>10} {'Frames/sec':>12} {'Relative':>10}", file=out)
    print("-" * 45, file=out)

    baseline_fps = None
    results = []
    for size in sizes:
        fps, elapsed = benchmark_frames_per_sec(
            dbc, size, properties, CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME,
        )
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{size:>10,} {elapsed:>10.2f} {fps:>12,.0f} {relative:>10.2f}x", file=out)
        results.append({"frames": size, "fps": round(fps, 1), "relative": round(relative, 3)})

    print(file=out)
    print("Expected: Relative throughput should stay near 1.0x (O(1) per frame)", file=out)
    return results


def test_trace_size_scaling_canfd(canfd_dbc: dict, quick: bool = False, file=None) -> list[dict]:
    """Test how throughput scales with trace size (CAN-FD)."""
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("2. Trace Size Scaling (CAN-FD, 64 bytes)", file=out)
    print("=" * 70, file=out)
    print("Testing CAN-FD throughput as trace size increases...", file=out)
    print(file=out)

    properties = [Signal("GPSSpeed").between(0, 655).always().to_dict()]
    sizes = [1000, 5000, 10000, 50000] if quick else [1000, 5000, 10000, 50000, 100000]

    print(f"{'Frames':>10} {'Time (s)':>10} {'Frames/sec':>12} {'Relative':>10}", file=out)
    print("-" * 45, file=out)

    baseline_fps = None
    results = []
    for size in sizes:
        fps, elapsed = benchmark_frames_per_sec(
            canfd_dbc, size, properties, CANFD_CAN_ID, CANFD_DLC, CANFD_FRAME,
        )
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{size:>10,} {elapsed:>10.2f} {fps:>12,.0f} {relative:>10.2f}x", file=out)
        results.append({"frames": size, "fps": round(fps, 1), "relative": round(relative, 3)})

    print(file=out)
    print("Expected: Relative throughput should stay near 1.0x (O(1) per frame)", file=out)
    return results


def test_property_count_scaling(dbc: dict, quick: bool = False, file=None) -> list[dict]:
    """Test how throughput scales with number of properties."""
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("3. Property Count Scaling", file=out)
    print("=" * 70, file=out)
    print("Testing throughput as property count increases...", file=out)
    print(file=out)

    num_frames = 5000 if quick else 10000

    def make_properties(count: int) -> list[dict]:
        props = []
        templates = [
            lambda: Signal("EngineSpeed").between(0, 8000).always(),
            lambda: Signal("EngineTemp").between(-40, 215).always(),
            lambda: Signal("BrakePressure").less_than(6553.5).always(),
            lambda: Signal("EngineSpeed").less_than(7000).always(),
            lambda: Signal("EngineTemp").less_than(200).always(),
            lambda: Signal("BrakePressure").less_than(5000).always(),
            lambda: Signal("EngineSpeed").between(500, 7500).always(),
            lambda: Signal("EngineTemp").between(-20, 180).always(),
            lambda: Signal("BrakePressure").between(0, 4000).always(),
            lambda: Signal("EngineSpeed").less_than(6000).always(),
        ]
        for i in range(count):
            props.append(templates[i % len(templates)]().to_dict())
        return props

    counts = [1, 2, 3, 5, 7, 10]

    print(f"{'Properties':>10} {'Frames/sec':>12} {'us/frame':>10} {'Relative':>10}", file=out)
    print("-" * 45, file=out)

    baseline_fps = None
    results = []
    for count in counts:
        properties = make_properties(count)
        fps, _ = benchmark_frames_per_sec(
            dbc, num_frames, properties, CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME,
        )
        us_per_frame = 1_000_000 / fps
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{count:>10} {fps:>12,.0f} {us_per_frame:>10.1f} {relative:>10.2f}x", file=out)
        results.append({
            "properties": count, "fps": round(fps, 1),
            "us_per_frame": round(us_per_frame, 1), "relative": round(relative, 3),
        })

    print(file=out)
    print("Expected: Some degradation, but should be sub-linear", file=out)
    return results


def test_property_complexity_scaling(dbc: dict, quick: bool = False, file=None) -> list[dict]:
    """Test how throughput scales with property complexity."""
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("4. Property Complexity Scaling", file=out)
    print("=" * 70, file=out)
    print("Testing throughput with different property complexities...", file=out)
    print(file=out)

    num_frames = 5000 if quick else 10000

    complexity_levels = [
        (
            "Simple predicate",
            [Signal("EngineSpeed").less_than(8000).always().to_dict()],
        ),
        (
            "Range predicate",
            [Signal("EngineSpeed").between(0, 8000).always().to_dict()],
        ),
        (
            "Two predicates (AND)",
            [
                Signal("EngineSpeed").between(0, 8000).always().to_dict(),
                Signal("EngineTemp").between(-40, 215).always().to_dict(),
            ],
        ),
        (
            "Three predicates",
            [
                Signal("EngineSpeed").between(0, 8000).always().to_dict(),
                Signal("EngineTemp").between(-40, 215).always().to_dict(),
                Signal("BrakePressure").less_than(6553.5).always().to_dict(),
            ],
        ),
        (
            "Implication",
            [Signal("EngineSpeed").less_than(1000).implies(
                Signal("EngineTemp").less_than(100)
            ).always().to_dict()],
        ),
    ]

    print(f"{'Complexity':<25} {'Frames/sec':>12} {'us/frame':>10} {'Relative':>10}", file=out)
    print("-" * 60, file=out)

    baseline_fps = None
    results = []
    for name, properties in complexity_levels:
        fps, _ = benchmark_frames_per_sec(
            dbc, num_frames, properties, CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME,
        )
        us_per_frame = 1_000_000 / fps
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{name:<25} {fps:>12,.0f} {us_per_frame:>10.1f} {relative:>10.2f}x", file=out)
        results.append({
            "complexity": name, "fps": round(fps, 1),
            "us_per_frame": round(us_per_frame, 1), "relative": round(relative, 3),
        })

    print(file=out)
    print("Expected: More complex properties should be slower", file=out)
    return results


def get_system_info() -> dict:
    """Collect system information for benchmark metadata."""
    return {
        "cpu": platform.processor() or platform.machine(),
        "cores": os.cpu_count() or 0,
        "platform": platform.system(),
        "python": platform.python_version(),
    }


def main():
    parser = argparse.ArgumentParser(description="Scaling benchmark")
    parser.add_argument("--quick", action="store_true", help="Run faster with fewer iterations")
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    args = parser.parse_args()

    out = sys.stderr if args.json else sys.stdout

    print("=" * 70, file=out)
    print("Aletheia Scaling Benchmark", file=out)
    print("=" * 70, file=out)
    if args.quick:
        print("(Quick mode - reduced iterations)", file=out)

    dbc = load_dbc()
    canfd_dbc = load_canfd_dbc()

    # Warmup
    print("\nWarming up...", file=out)
    props = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]
    benchmark_frames_per_sec(dbc, 1000, props, CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME)
    print("Done.", file=out)

    trace_can20 = test_trace_size_scaling(dbc, args.quick, file=out)
    trace_canfd = test_trace_size_scaling_canfd(canfd_dbc, args.quick, file=out)
    prop_count = test_property_count_scaling(dbc, args.quick, file=out)
    prop_complexity = test_property_complexity_scaling(dbc, args.quick, file=out)

    print("\n" + "=" * 70, file=out)
    print("Scaling benchmark complete", file=out)
    print("=" * 70, file=out)

    if args.json:
        output = {
            "benchmark": "scaling",
            "language": "python",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "system": get_system_info(),
            "results": {
                "trace_size_can20": trace_can20,
                "trace_size_canfd": trace_canfd,
                "property_count": prop_count,
                "property_complexity": prop_complexity,
            },
        }
        print(json.dumps(output, indent=2))

    return 0


if __name__ == "__main__":
    sys.exit(main())
