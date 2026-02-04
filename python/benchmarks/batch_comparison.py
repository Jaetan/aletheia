#!/usr/bin/env python3
"""
Batch Processing Benchmark

Compares single-frame vs batch-frame throughput to measure the
impact of IPC overhead amortization.

Usage:
    python3 batch_comparison.py [--frames N] [--batch-size N]
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


def benchmark_single_frame(dbc: dict, num_frames: int) -> tuple[float, float]:
    """Benchmark single-frame sending."""
    frame = [0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00]
    properties = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]

    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        start = time.perf_counter()
        for i in range(num_frames):
            client.send_frame(timestamp=i, can_id=0x100, data=frame)
        elapsed = time.perf_counter() - start

        client.end_stream()

    return num_frames / elapsed, elapsed


def benchmark_batch_frames(dbc: dict, num_frames: int, batch_size: int) -> tuple[float, float]:
    """Benchmark batch-frame sending."""
    frame = [0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00]
    properties = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]

    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        # Prepare all frames
        frames = [(i, 0x100, frame) for i in range(num_frames)]

        start = time.perf_counter()
        # Send in batches
        for batch_start in range(0, num_frames, batch_size):
            batch = frames[batch_start:batch_start + batch_size]
            client.send_frames_batch(batch)
        elapsed = time.perf_counter() - start

        client.end_stream()

    return num_frames / elapsed, elapsed


def main():
    parser = argparse.ArgumentParser(description="Batch processing benchmark")
    parser.add_argument("--frames", type=int, default=10000, help="Total frames to process")
    parser.add_argument("--batch-size", type=int, default=100, help="Frames per batch")
    args = parser.parse_args()

    print("=" * 70)
    print("Batch Processing Benchmark")
    print("=" * 70)
    print(f"Total frames: {args.frames:,}")
    print(f"Batch size: {args.batch_size}")
    print()

    dbc = load_dbc()

    # Warmup
    print("Warming up...")
    benchmark_single_frame(dbc, 1000)
    benchmark_batch_frames(dbc, 1000, 100)
    print()

    # Single-frame benchmark
    print("Benchmarking single-frame mode...")
    single_fps, single_time = benchmark_single_frame(dbc, args.frames)
    print(f"  Throughput: {single_fps:,.0f} frames/sec")
    print(f"  Time: {single_time:.2f}s")
    print()

    # Batch benchmark with different batch sizes
    batch_sizes = [10, 50, 100, 500, 1000]
    print("Benchmarking batch mode...")
    print()
    print(f"{'Batch Size':>12} {'Throughput':>15} {'Time':>10} {'Speedup':>10}")
    print("-" * 50)

    for batch_size in batch_sizes:
        if batch_size > args.frames:
            continue
        batch_fps, batch_time = benchmark_batch_frames(dbc, args.frames, batch_size)
        speedup = batch_fps / single_fps
        print(f"{batch_size:>12} {batch_fps:>12,.0f}/s {batch_time:>10.2f}s {speedup:>9.2f}x")

    print()
    print("=" * 70)
    print("Summary")
    print("=" * 70)
    print(f"Single-frame baseline: {single_fps:,.0f} frames/sec")
    print()
    print("Batch processing amortizes IPC overhead over multiple frames,")
    print("reducing the per-frame cost of subprocess communication.")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
