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
import sys
import time
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


def test_trace_size_scaling(dbc: dict, quick: bool = False):
    """Test how throughput scales with trace size (CAN 2.0B)."""
    print("\n" + "=" * 70)
    print("1. Trace Size Scaling (CAN 2.0B)")
    print("=" * 70)
    print("Testing throughput as trace size increases...")
    print("(Verifies O(1) memory and constant throughput)")
    print()

    properties = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]
    sizes = [1000, 5000, 10000, 50000] if quick else [1000, 5000, 10000, 50000, 100000]

    print(f"{'Frames':>10} {'Time (s)':>10} {'Frames/sec':>12} {'Relative':>10}")
    print("-" * 45)

    baseline_fps = None
    for size in sizes:
        fps, elapsed = benchmark_frames_per_sec(
            dbc, size, properties, CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME,
        )
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{size:>10,} {elapsed:>10.2f} {fps:>12,.0f} {relative:>10.2f}x")

    print()
    print("Expected: Relative throughput should stay near 1.0x (O(1) per frame)")


def test_trace_size_scaling_canfd(canfd_dbc: dict, quick: bool = False):
    """Test how throughput scales with trace size (CAN-FD)."""
    print("\n" + "=" * 70)
    print("2. Trace Size Scaling (CAN-FD, 64 bytes)")
    print("=" * 70)
    print("Testing CAN-FD throughput as trace size increases...")
    print()

    properties = [Signal("GPSSpeed").between(0, 655).always().to_dict()]
    sizes = [1000, 5000, 10000, 50000] if quick else [1000, 5000, 10000, 50000, 100000]

    print(f"{'Frames':>10} {'Time (s)':>10} {'Frames/sec':>12} {'Relative':>10}")
    print("-" * 45)

    baseline_fps = None
    for size in sizes:
        fps, elapsed = benchmark_frames_per_sec(
            canfd_dbc, size, properties, CANFD_CAN_ID, CANFD_DLC, CANFD_FRAME,
        )
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{size:>10,} {elapsed:>10.2f} {fps:>12,.0f} {relative:>10.2f}x")

    print()
    print("Expected: Relative throughput should stay near 1.0x (O(1) per frame)")


def test_property_count_scaling(dbc: dict, quick: bool = False):
    """Test how throughput scales with number of properties."""
    print("\n" + "=" * 70)
    print("3. Property Count Scaling")
    print("=" * 70)
    print("Testing throughput as property count increases...")
    print()

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

    print(f"{'Properties':>10} {'Frames/sec':>12} {'us/frame':>10} {'Relative':>10}")
    print("-" * 45)

    baseline_fps = None
    for count in counts:
        properties = make_properties(count)
        fps, _ = benchmark_frames_per_sec(
            dbc, num_frames, properties, CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME,
        )
        us_per_frame = 1_000_000 / fps
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{count:>10} {fps:>12,.0f} {us_per_frame:>10.1f} {relative:>10.2f}x")

    print()
    print("Expected: Some degradation, but should be sub-linear")


def test_property_complexity_scaling(dbc: dict, quick: bool = False):
    """Test how throughput scales with property complexity."""
    print("\n" + "=" * 70)
    print("4. Property Complexity Scaling")
    print("=" * 70)
    print("Testing throughput with different property complexities...")
    print()

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

    print(f"{'Complexity':<25} {'Frames/sec':>12} {'us/frame':>10} {'Relative':>10}")
    print("-" * 60)

    baseline_fps = None
    for name, properties in complexity_levels:
        fps, _ = benchmark_frames_per_sec(
            dbc, num_frames, properties, CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME,
        )
        us_per_frame = 1_000_000 / fps
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{name:<25} {fps:>12,.0f} {us_per_frame:>10.1f} {relative:>10.2f}x")

    print()
    print("Expected: More complex properties should be slower")


def main():
    parser = argparse.ArgumentParser(description="Scaling benchmark")
    parser.add_argument("--quick", action="store_true", help="Run faster with fewer iterations")
    args = parser.parse_args()

    print("=" * 70)
    print("Aletheia Scaling Benchmark")
    print("=" * 70)
    if args.quick:
        print("(Quick mode - reduced iterations)")

    dbc = load_dbc()
    canfd_dbc = load_canfd_dbc()

    # Warmup
    print("\nWarming up...")
    props = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]
    benchmark_frames_per_sec(dbc, 1000, props, CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME)
    print("Done.")

    test_trace_size_scaling(dbc, args.quick)
    test_trace_size_scaling_canfd(canfd_dbc, args.quick)
    test_property_count_scaling(dbc, args.quick)
    test_property_complexity_scaling(dbc, args.quick)

    print("\n" + "=" * 70)
    print("Scaling benchmark complete")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
