#!/usr/bin/env python3
"""
Violation Enrichment Benchmark

Measures the overhead of violation diagnostics (extract_signals calls)
under different violation rates, at both the AletheiaClient and CLI layers.

The AletheiaClient benchmarks test the raw send_frame() path with
set_check_diagnostics() enabled.  The CLI benchmarks test the full
_run_checks() pipeline (file I/O, ASC parsing, enrichment, result building).

Scenarios:
    1. All violations, identical frames (cache hit rate: 100%)
    2. All violations, unique frames   (cache hit rate: 0%, bounded at 256)
    3. Mixed: 10% violations, 90% passing
    4. No violations (baseline)

Usage:
    python3 violations.py [--frames N] [--runs N]
"""

import argparse
import os
import statistics
import sys
import tempfile
import time
from pathlib import Path

import can

sys.path.insert(0, str(Path(__file__).parent.parent))

from aletheia import AletheiaClient, Signal
from aletheia.checks import Check, CheckResult
from aletheia.cli import _run_checks
from aletheia.dbc_converter import dbc_to_json

_TARGET_FPS = 8000
_DBC_PATH = Path(__file__).parent.parent.parent / "examples" / "demo" / "vehicle.dbc"


# ============================================================================
# ASC file generators
# ============================================================================

def _write_asc(path: str, messages: list[can.Message]) -> None:
    writer = can.ASCWriter(path)
    for msg in messages:
        writer.on_message_received(msg)
    writer.stop()


def _make_frame(speed_raw: int, ts: float) -> can.Message:
    """CAN frame with given raw VehicleSpeed (factor=0.01, CAN ID 0x100)."""
    lo = speed_raw & 0xFF
    hi = (speed_raw >> 8) & 0xFF
    return can.Message(
        timestamp=ts,
        arbitration_id=0x100,
        data=bytearray([lo, hi, 0, 0, 0, 0, 0, 0]),
        is_extended_id=False,
    )


def _raw_data(speed_raw: int) -> bytearray:
    """8-byte bytearray for a given raw VehicleSpeed."""
    lo = speed_raw & 0xFF
    hi = (speed_raw >> 8) & 0xFF
    return bytearray([lo, hi, 0, 0, 0, 0, 0, 0])


def gen_all_identical(tmpdir: str, n: int) -> str:
    path = os.path.join(tmpdir, "all_identical.asc")
    _write_asc(path, [_make_frame(10000, i * 0.001) for i in range(n)])
    return path


def gen_all_unique(tmpdir: str, n: int) -> str:
    path = os.path.join(tmpdir, "all_unique.asc")
    _write_asc(path, [_make_frame(5100 + i, i * 0.001) for i in range(n)])
    return path


def gen_mixed(tmpdir: str, n: int) -> str:
    path = os.path.join(tmpdir, "mixed.asc")
    msgs = []
    for i in range(n):
        raw = 10000 if i % 10 == 0 else 2000
        msgs.append(_make_frame(raw, i * 0.001))
    _write_asc(path, msgs)
    return path


def gen_no_violations(tmpdir: str, n: int) -> str:
    path = os.path.join(tmpdir, "no_violations.asc")
    _write_asc(path, [_make_frame(2000, i * 0.001) for i in range(n)])
    return path


# ============================================================================
# Client-level benchmark
# ============================================================================

def bench_client(
    dbc: dict,
    checks: list[CheckResult],
    num_frames: int,
    frame_gen: str,
) -> float:
    """Benchmark AletheiaClient.send_frame() with enrichment.

    Returns frames per second.
    """
    properties = [c.to_dict() for c in checks]

    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.set_check_diagnostics(checks)
        client.start_stream()

        if frame_gen == "identical":
            data = _raw_data(10000)
            start = time.perf_counter()
            for i in range(num_frames):
                client.send_frame(timestamp=i, can_id=0x100, data=data)
            elapsed = time.perf_counter() - start
        elif frame_gen == "unique":
            frames = [_raw_data(5100 + i) for i in range(num_frames)]
            start = time.perf_counter()
            for i, data in enumerate(frames):
                client.send_frame(timestamp=i, can_id=0x100, data=data)
            elapsed = time.perf_counter() - start
        elif frame_gen == "mixed":
            start = time.perf_counter()
            for i in range(num_frames):
                raw = 10000 if i % 10 == 0 else 2000
                client.send_frame(timestamp=i, can_id=0x100, data=_raw_data(raw))
            elapsed = time.perf_counter() - start
        else:  # no_violations
            data = _raw_data(2000)
            start = time.perf_counter()
            for i in range(num_frames):
                client.send_frame(timestamp=i, can_id=0x100, data=data)
            elapsed = time.perf_counter() - start

        client.end_stream()

    return num_frames / elapsed


# ============================================================================
# CLI-level benchmark
# ============================================================================

def bench_cli(
    dbc: dict,
    checks: list[CheckResult],
    asc_path: str,
) -> tuple[float, int]:
    """Benchmark _run_checks() (CLI pipeline).

    Returns (fps, violation_count).
    """
    start = time.perf_counter()
    violations, total = _run_checks(dbc, checks, asc_path)
    elapsed = time.perf_counter() - start
    return total / elapsed, len(violations)


# ============================================================================
# Runner
# ============================================================================

def run_multi(
    name: str, func, num_runs: int,
) -> dict:
    """Run a benchmark function multiple times and collect stats."""
    results = []
    for run in range(num_runs):
        fps = func()
        results.append(fps)
        print(f"  Run {run + 1}/{num_runs}: {fps:,.0f} fps")

    return {
        "name": name,
        "mean_fps": statistics.mean(results),
        "stdev_fps": statistics.stdev(results) if len(results) > 1 else 0,
        "min_fps": min(results),
        "max_fps": max(results),
        "mean_us": 1_000_000 / statistics.mean(results),
    }


def print_summary(title: str, results: list[dict]) -> None:
    print(f"\n{'=' * 70}")
    print(title)
    print("=" * 70)
    print(f"{'Scenario':<30} {'Mean FPS':>10} {'us/frame':>10} {'Stdev':>8} {'Status':>8}")
    print("-" * 70)
    for r in results:
        status = "OK" if r["mean_fps"] >= _TARGET_FPS else "SLOW"
        print(
            f"{r['name']:<30} {r['mean_fps']:>10,.0f} {r['mean_us']:>10.0f} "
            f"{r['stdev_fps']:>8,.0f} {status:>8}"
        )
    print("-" * 70)
    print(f"Target: {_TARGET_FPS:,} FPS ({1_000_000 / _TARGET_FPS:.0f} us/frame)")
    print("=" * 70)


def main() -> int:
    parser = argparse.ArgumentParser(description="Violation enrichment benchmark")
    parser.add_argument("--frames", type=int, default=10000, help="Frames per run")
    parser.add_argument("--runs", type=int, default=5, help="Number of runs")
    args = parser.parse_args()

    print("=" * 70)
    print("Aletheia Violation Enrichment Benchmark")
    print("=" * 70)
    print(f"Frames per run: {args.frames:,}")
    print(f"Runs: {args.runs}")

    dbc = dbc_to_json(str(_DBC_PATH))
    checks = [
        Check.signal("VehicleSpeed").never_exceeds(50.0)
            .named("Speed limit").severity("critical"),
    ]

    # -- Client-level benchmarks ---------------------------------------------
    client_scenarios = [
        ("identical (cached)", "identical"),
        ("unique (bounded)", "unique"),
        ("mixed 10%", "mixed"),
        ("no violations", "no_violations"),
    ]

    print("\n--- AletheiaClient.send_frame() ---")
    client_results = []
    for label, gen in client_scenarios:
        print(f"\n{label}:")
        r = run_multi(
            label,
            lambda g=gen: bench_client(dbc, checks, args.frames, g),
            args.runs,
        )
        client_results.append(r)

    print_summary("Client-level Summary", client_results)

    # -- CLI-level benchmarks ------------------------------------------------
    tmpdir = tempfile.mkdtemp()
    cli_scenarios = [
        ("identical (cached)", gen_all_identical(tmpdir, args.frames)),
        ("unique (bounded)", gen_all_unique(tmpdir, args.frames)),
        ("mixed 10%", gen_mixed(tmpdir, args.frames)),
        ("no violations", gen_no_violations(tmpdir, args.frames)),
    ]

    print("\n--- CLI _run_checks() ---")
    cli_results = []
    for label, asc_path in cli_scenarios:
        print(f"\n{label}:")
        r = run_multi(
            label,
            lambda p=asc_path: bench_cli(dbc, checks, p)[0],
            args.runs,
        )
        cli_results.append(r)

    print_summary("CLI-level Summary", cli_results)

    # Cleanup
    for _, path in cli_scenarios:
        os.unlink(path)
    os.rmdir(tmpdir)

    return 0


if __name__ == "__main__":
    sys.exit(main())
