#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Throughput Benchmark.

Measures frames per second through the full Aletheia pipeline:
Python -> FFI (ctypes) -> Haskell/MAlonzo/Agda -> back.

Tests both CAN 2.0B (8-byte) and CAN-FD (64-byte) frames.

Usage:
    python3 throughput.py [--frames N] [--runs N] [--warmup N]
"""

from __future__ import annotations

import argparse
import statistics
import sys
import time
from typing import TYPE_CHECKING, TextIO, TypedDict

# Shared benchmark vocabulary — frame specs, default property bundles, JSON
# envelope, system info.  Consolidated in ``_common.py`` to keep the suite
# files thin; see PY-31-1.
from benchmarks._common import (
    CAN20_SPEC,
    CANFD_SPEC,
    DEFAULT_CAN20_PROPERTIES,
    DEFAULT_CANFD_PROPERTIES,
    BenchmarkConfig,
    FrameSpec,
    emit_json_report,
    load_canfd_dbc,
    load_dbc,
    run_streaming_benchmark,
)

# Benchmarks import the *installed* package (``pip install -e .[dev]``) so
# that any wheel/setuptools shim overhead shows up in the numbers — matches
# how end users measure Aletheia in production.  Do not reintroduce
# ``sys.path.insert`` here; it hid the install-path cost from earlier runs.
from aletheia import AletheiaClient

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.protocols import DBCDefinition, LTLFormula


class _BenchResult(TypedDict):
    """Stats record for one benchmark scenario × N runs."""

    name: str
    num_frames: int
    num_runs: int
    mean: float
    stdev: float
    min: float
    max: float
    results: list[float]


class _JsonPayload(TypedDict):
    """JSON-report-shaped projection of a ``_BenchResult`` row."""

    name: str
    frames: int
    runs: int
    fps_mean: float
    fps_stdev: float
    fps_min: float
    fps_max: float
    us_per_frame: float


# ============================================================================
# Per-mode benchmark functions — each takes a FrameSpec to keep the
# parameter list narrow (was 4-5 args; now 3).
# ============================================================================


def benchmark_streaming(
    dbc: DBCDefinition,
    num_frames: int,
    spec: FrameSpec,
    properties: list[LTLFormula],
) -> float:
    """Benchmark streaming throughput. Returns frames per second."""
    fps, _elapsed = run_streaming_benchmark(dbc, num_frames, spec, properties)
    return fps


def benchmark_signal_extraction(
    dbc: DBCDefinition,
    num_frames: int,
    spec: FrameSpec,
) -> float:
    """Benchmark signal extraction throughput. Returns extractions per second."""
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        start = time.perf_counter()
        for _ in range(num_frames):
            client.extract_signals(can_id=spec.can_id, dlc=spec.dlc, data=spec.payload)
        elapsed = time.perf_counter() - start
    return num_frames / elapsed


def benchmark_frame_building(
    dbc: DBCDefinition,
    num_frames: int,
    spec: FrameSpec,
) -> float:
    """Benchmark frame building throughput. Returns builds per second."""
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        start = time.perf_counter()
        for _ in range(num_frames):
            client.build_frame(can_id=spec.can_id, dlc=spec.dlc, signals=spec.signals)
        elapsed = time.perf_counter() - start
    return num_frames / elapsed


# ============================================================================
# Runner
# ============================================================================


def run_benchmark(
    name: str,
    func: Callable[[int], float],
    cfg: BenchmarkConfig,
) -> _BenchResult:
    """Run a benchmark multiple times and collect statistics."""
    for _ in range(cfg.warmup_runs):
        func(cfg.num_frames // 10)  # Smaller warmup
    results = [func(cfg.num_frames) for _ in range(cfg.num_runs)]
    return {
        "name": name,
        "num_frames": cfg.num_frames,
        "num_runs": cfg.num_runs,
        "mean": statistics.mean(results),
        "stdev": statistics.stdev(results) if len(results) > 1 else 0.0,
        "min": min(results),
        "max": max(results),
        "results": results,
    }


def _build_benchmarks(
    dbc: DBCDefinition,
    canfd_dbc: DBCDefinition,
) -> list[tuple[str, Callable[[int], float]]]:
    """Build the (name, partial_fn) list driving the benchmark loop.

    Extracted from ``main`` so its local-variable count stays under the
    pylint ``too-many-locals`` cap; also makes the benchmark inventory
    easy to spot independently of the run loop.
    """
    return [
        # --- CAN 2.0B ---
        (
            "CAN 2.0B: Stream LTL (2 props)",
            lambda n: benchmark_streaming(dbc, n, CAN20_SPEC, DEFAULT_CAN20_PROPERTIES),
        ),
        ("CAN 2.0B: Signal Extraction", lambda n: benchmark_signal_extraction(dbc, n, CAN20_SPEC)),
        ("CAN 2.0B: Frame Building", lambda n: benchmark_frame_building(dbc, n, CAN20_SPEC)),
        # --- CAN-FD ---
        (
            "CAN-FD:   Stream LTL (3 props)",
            lambda n: benchmark_streaming(canfd_dbc, n, CANFD_SPEC, DEFAULT_CANFD_PROPERTIES),
        ),
        (
            "CAN-FD:   Signal Extraction",
            lambda n: benchmark_signal_extraction(canfd_dbc, n, CANFD_SPEC),
        ),
        ("CAN-FD:   Frame Building", lambda n: benchmark_frame_building(canfd_dbc, n, CANFD_SPEC)),
    ]


def _print_summary(results: list[_BenchResult], file: TextIO) -> None:
    """Print the formatted summary table to the given stream."""
    print("\n" + "=" * 70, file=file)
    print("Summary", file=file)
    print("=" * 70, file=file)
    print(
        f"{'Benchmark':<35} {'Mean':>12} {'Stdev':>10} {'Min':>10} {'Max':>10}",
        file=file,
    )
    print("-" * 80, file=file)
    for r in results:
        print(
            f"{r['name']:<35} {r['mean']:>10,.0f}/s "
            + f"{r['stdev']:>9,.0f} {r['min']:>9,.0f} {r['max']:>9,.0f}",
            file=file,
        )
    print("=" * 70, file=file)


def _to_json_payload(r: _BenchResult) -> _JsonPayload:
    """Project one ``run_benchmark`` result dict into the JSON-report shape."""
    return {
        "name": r["name"],
        "frames": r["num_frames"],
        "runs": r["num_runs"],
        "fps_mean": round(r["mean"], 1),
        "fps_stdev": round(r["stdev"], 1),
        "fps_min": round(r["min"], 1),
        "fps_max": round(r["max"], 1),
        "us_per_frame": round(1_000_000 / r["mean"], 1) if r["mean"] > 0 else 0,
    }


def main() -> int:
    """CLI entry point — parse args, run the benchmark suite, emit summary."""
    parser = argparse.ArgumentParser(description="Throughput benchmark")
    parser.add_argument("--frames", type=int, default=10000, help="Frames per run")
    parser.add_argument("--runs", type=int, default=5, help="Number of runs")
    parser.add_argument("--warmup", type=int, default=2, help="Warmup runs")
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    args = parser.parse_args()

    cfg = BenchmarkConfig(
        num_frames=args.frames,
        num_runs=args.runs,
        warmup_runs=args.warmup,
        json_output=args.json,
    )
    out = sys.stderr if cfg.json_output else sys.stdout

    print("=" * 70, file=out)
    print("Aletheia Throughput Benchmark", file=out)
    print("=" * 70, file=out)
    print(f"Frames per run: {cfg.num_frames:,}", file=out)
    print(f"Runs: {cfg.num_runs}", file=out)
    print(f"Warmup runs: {cfg.warmup_runs}", file=out)

    benchmarks = _build_benchmarks(load_dbc(), load_canfd_dbc())

    results: list[_BenchResult] = []
    for name, func in benchmarks:
        print(f"\n{name}:", file=out)
        print("-" * 40, file=out)
        result = run_benchmark(name, func, cfg)
        results.append(result)
        for run_idx, fps in enumerate(result["results"]):
            print(f"  Run {run_idx + 1}/{cfg.num_runs}: {fps:,.0f} ops/sec", file=out)

    _print_summary(results, out)

    if cfg.json_output:
        emit_json_report("throughput", [_to_json_payload(r) for r in results])

    return 0


if __name__ == "__main__":
    sys.exit(main())
