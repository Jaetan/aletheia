#!/usr/bin/env python3
"""Violation Enrichment Benchmark.

Measures the overhead of violation diagnostics (extract_signals calls)
under different violation rates, at both the AletheiaClient and CLI layers.

The AletheiaClient benchmarks test the raw send_frame() path with
set_check_diagnostics() enabled.  The CLI benchmarks test the full
``run_checks`` pipeline (file I/O, ASC parsing, enrichment, result building).

Scenarios:
    1. All violations, identical frames (cache hit rate: 100%)
    2. All violations, unique frames   (cache hit rate: 0%, bounded at 256)
    3. Mixed: 10% violations, 90% passing
    4. No violations (baseline)

Usage:
    python3 violations.py [--frames N] [--runs N]
"""

from __future__ import annotations

import argparse
import os
import statistics
import sys
import tempfile
import time
from pathlib import Path
from typing import Callable, TypedDict

import can

# See ``throughput.py`` — benchmarks import the installed package to keep
# the wheel / setuptools shim cost inside the measurement.
from aletheia import AletheiaClient
from aletheia.checks import CheckResult, signal
from aletheia.dbc_converter import dbc_to_json
from aletheia.protocols import DBCDefinition, DLCCode
from aletheia.testing import run_checks

_TARGET_FPS = 8000
_DBC_PATH = Path(__file__).parent.parent.parent / "examples" / "demo" / "vehicle.dbc"


class _BenchResult(TypedDict):
    """Stats record for one scenario × N runs.  Frozen-shape consumer schema."""

    name: str
    mean_fps: float
    stdev_fps: float
    min_fps: float
    max_fps: float
    mean_us: float


# ============================================================================
# ASC file generators
# ============================================================================

def _write_asc(path: str, messages: list[can.Message]) -> None:
    """Write the given CAN messages to an ASC log at ``path``."""
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
    """Generate ASC log of N copies of the same violating frame."""
    path = os.path.join(tmpdir, "all_identical.asc")
    _write_asc(path, [_make_frame(10000, i * 0.001) for i in range(n)])
    return path


def gen_all_unique(tmpdir: str, n: int) -> str:
    """Generate ASC log of N unique violating frames (forces cache miss)."""
    path = os.path.join(tmpdir, "all_unique.asc")
    _write_asc(path, [_make_frame(5100 + i, i * 0.001) for i in range(n)])
    return path


def gen_mixed(tmpdir: str, n: int) -> str:
    """Generate ASC log with 10% violations + 90% passing."""
    path = os.path.join(tmpdir, "mixed.asc")
    msgs: list[can.Message] = []
    for i in range(n):
        raw = 10000 if i % 10 == 0 else 2000
        msgs.append(_make_frame(raw, i * 0.001))
    _write_asc(path, msgs)
    return path


def gen_no_violations(tmpdir: str, n: int) -> str:
    """Generate ASC log of N copies of a passing frame."""
    path = os.path.join(tmpdir, "no_violations.asc")
    _write_asc(path, [_make_frame(2000, i * 0.001) for i in range(n)])
    return path


# ============================================================================
# Client-level benchmark
# ============================================================================

def _stream_identical(client: AletheiaClient, num_frames: int) -> float:
    """Stream identical violating frames; return elapsed seconds."""
    data = _raw_data(10000)
    start = time.perf_counter()
    for i in range(num_frames):
        client.send_frame(timestamp=i, can_id=0x100, dlc=DLCCode(8), data=data)
    return time.perf_counter() - start


def _stream_unique(client: AletheiaClient, num_frames: int) -> float:
    """Stream unique violating frames; return elapsed seconds."""
    frames = [_raw_data(5100 + i) for i in range(num_frames)]
    start = time.perf_counter()
    for i, data in enumerate(frames):
        client.send_frame(timestamp=i, can_id=0x100, dlc=DLCCode(8), data=data)
    return time.perf_counter() - start


def _stream_mixed(client: AletheiaClient, num_frames: int) -> float:
    """Stream 10% violating / 90% passing frames; return elapsed seconds."""
    start = time.perf_counter()
    for i in range(num_frames):
        raw = 10000 if i % 10 == 0 else 2000
        client.send_frame(timestamp=i, can_id=0x100, dlc=DLCCode(8), data=_raw_data(raw))
    return time.perf_counter() - start


def _stream_no_violations(client: AletheiaClient, num_frames: int) -> float:
    """Stream identical passing frames; return elapsed seconds."""
    data = _raw_data(2000)
    start = time.perf_counter()
    for i in range(num_frames):
        client.send_frame(timestamp=i, can_id=0x100, dlc=DLCCode(8), data=data)
    return time.perf_counter() - start


_FRAME_GENS: dict[str, Callable[[AletheiaClient, int], float]] = {
    "identical": _stream_identical,
    "unique": _stream_unique,
    "mixed": _stream_mixed,
    "no_violations": _stream_no_violations,
}


def bench_client(
    dbc: DBCDefinition, checks: list[CheckResult], num_frames: int, frame_gen: str,
) -> float:
    """Benchmark AletheiaClient.send_frame() with enrichment.

    Returns frames per second.
    """
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.add_checks(checks)
        client.start_stream()
        elapsed = _FRAME_GENS[frame_gen](client, num_frames)
        client.end_stream()
    return num_frames / elapsed


# ============================================================================
# CLI-level benchmark
# ============================================================================

def bench_cli(
    dbc: DBCDefinition, checks: list[CheckResult], asc_path: str,
) -> tuple[float, int]:
    """Benchmark ``run_checks`` (CLI pipeline).

    Returns (fps, violation_count).
    """
    start = time.perf_counter()
    result = run_checks(dbc, checks, asc_path)
    elapsed = time.perf_counter() - start
    return result.total_frames / elapsed, len(result.violations)


# ============================================================================
# Runner
# ============================================================================

def run_multi(name: str, func: Callable[[], float], num_runs: int) -> _BenchResult:
    """Run a benchmark function multiple times and collect stats."""
    results: list[float] = []
    for run in range(num_runs):
        fps = func()
        results.append(fps)
        print(f"  Run {run + 1}/{num_runs}: {fps:,.0f} fps")

    return {
        "name": name,
        "mean_fps": statistics.mean(results),
        "stdev_fps": statistics.stdev(results) if len(results) > 1 else 0.0,
        "min_fps": min(results),
        "max_fps": max(results),
        "mean_us": 1_000_000 / statistics.mean(results),
    }


def print_summary(title: str, results: list[_BenchResult]) -> None:
    """Print a formatted summary table for one benchmark layer."""
    print(f"\n{'=' * 70}")
    print(title)
    print("=" * 70)
    print(
        f"{'Scenario':<30} {'Mean FPS':>10} {'us/frame':>10} {'Stdev':>8} {'Status':>8}"
    )
    print("-" * 70)
    for r in results:
        status = "OK" if r["mean_fps"] >= _TARGET_FPS else "SLOW"
        print(
            f"{r['name']:<30} {r['mean_fps']:>10,.0f} {r['mean_us']:>10.0f} "
            + f"{r['stdev_fps']:>8,.0f} {status:>8}"
        )
    print("-" * 70)
    print(f"Target: {_TARGET_FPS:,} FPS ({1_000_000 / _TARGET_FPS:.0f} us/frame)")
    print("=" * 70)


def _run_client_layer(
    dbc: DBCDefinition, checks: list[CheckResult], num_frames: int, num_runs: int,
) -> list[_BenchResult]:
    """Run + summarize the AletheiaClient.send_frame() benchmark layer."""
    scenarios = [
        ("identical (cached)", "identical"),
        ("unique (bounded)", "unique"),
        ("mixed 10%", "mixed"),
        ("no violations", "no_violations"),
    ]
    print("\n--- AletheiaClient.send_frame() ---")
    results: list[_BenchResult] = []
    for label, gen in scenarios:
        print(f"\n{label}:")
        results.append(run_multi(
            label,
            lambda g=gen: bench_client(dbc, checks, num_frames, g),
            num_runs,
        ))
    print_summary("Client-level Summary", results)
    return results


def _run_cli_layer(
    dbc: DBCDefinition, checks: list[CheckResult], num_frames: int, num_runs: int,
) -> tuple[list[_BenchResult], list[str]]:
    """Run + summarize the ``run_checks`` CLI benchmark layer.

    Returns (results, asc_paths).  Caller is responsible for cleaning up
    each path in ``asc_paths`` plus the parent tempdir.
    """
    tmpdir = tempfile.mkdtemp()
    scenarios = [
        ("identical (cached)", gen_all_identical(tmpdir, num_frames)),
        ("unique (bounded)", gen_all_unique(tmpdir, num_frames)),
        ("mixed 10%", gen_mixed(tmpdir, num_frames)),
        ("no violations", gen_no_violations(tmpdir, num_frames)),
    ]
    print("\n--- CLI run_checks() ---")
    results: list[_BenchResult] = []
    paths: list[str] = []
    for label, asc_path in scenarios:
        print(f"\n{label}:")
        results.append(run_multi(
            label,
            lambda p=asc_path: bench_cli(dbc, checks, p)[0],
            num_runs,
        ))
        paths.append(asc_path)
    print_summary("CLI-level Summary", results)
    paths.append(tmpdir)
    return results, paths


def main() -> int:
    """CLI entry point — run client + CLI violation benchmark layers."""
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
        signal("VehicleSpeed").never_exceeds(50.0)
            .named("Speed limit").severity("critical"),
    ]

    _run_client_layer(dbc, checks, args.frames, args.runs)
    _, paths = _run_cli_layer(dbc, checks, args.frames, args.runs)

    # Cleanup: paths is [asc1, asc2, asc3, asc4, tmpdir] — last entry is the dir.
    *files, tmpdir = paths
    for path in files:
        os.unlink(path)
    os.rmdir(tmpdir)

    return 0


if __name__ == "__main__":
    sys.exit(main())
