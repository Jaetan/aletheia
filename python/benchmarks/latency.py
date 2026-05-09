#!/usr/bin/env python3
"""Latency Benchmark.

Measures per-operation latency distribution through the Aletheia pipeline.
Reports percentiles (p50, p90, p99, p99.9) to understand tail latency.

Tests both CAN 2.0B (8-byte) and CAN-FD (64-byte) frames.

Usage:
    python3 latency.py [--ops N] [--warmup N]
"""

from __future__ import annotations

import argparse
import sys
import time
from dataclasses import dataclass
from typing import IO, TypedDict

# See ``throughput.py`` — benchmarks import the installed package to keep
# the wheel / setuptools shim cost inside the measurement.
from aletheia import AletheiaClient
from aletheia.protocols import DBCDefinition, LTLFormula

# Shared vocabulary lives in ``_common``; see PY-31-1 for the dedup rationale.
from ._common import (
    CAN20_SPEC, CANFD_SPEC,
    DEFAULT_CAN20_PROPERTIES, DEFAULT_CANFD_PROPERTIES,
    FrameSpec,
    emit_json_report, load_canfd_dbc, load_dbc,
)


class _LatencyStats(TypedDict):
    """Per-operation latency distribution stats (microseconds)."""

    count: int
    mean_us: float
    min_us: float
    max_us: float
    p50_us: float
    p90_us: float
    p99_us: float
    p999_us: float


class _JsonStatsRow(TypedDict):
    """JSON-report-shaped projection of one (name, stats) row."""

    name: str
    count: int
    mean_us: float
    min_us: float
    max_us: float
    p50_us: float
    p90_us: float
    p99_us: float
    p999_us: float


@dataclass(frozen=True)
class LatencyContext:
    """Per-suite context bundle: keeps internal helper signatures narrow.

    The four internal lane helpers (``_bench_stream_lane``,
    ``_bench_extract_lane``, ``_bench_build_lane``, ``run_latency_suite``)
    all need the same set of parameters; passing them inside one frozen
    bundle drops them from N+5 args to 1 and stops pylint R0913 from
    firing without forcing the helpers to read globals.
    """

    label: str
    dbc: DBCDefinition
    spec: FrameSpec
    properties: list[LTLFormula]
    num_ops: int
    warmup: int
    file: IO[str]


def percentile(data: list[float], p: float) -> float:
    """Calculate percentile of sorted data."""
    if not data:
        return 0.0
    k = (len(data) - 1) * p / 100
    f = int(k)
    c = f + 1 if f + 1 < len(data) else f
    return data[f] + (k - f) * (data[c] - data[f])


def _measure_stream(client: AletheiaClient, spec: FrameSpec, num_ops: int) -> list[float]:
    """Per-op stream latencies."""
    latencies: list[float] = []
    for i in range(num_ops):
        start = time.perf_counter()
        client.send_frame(timestamp=i, can_id=spec.can_id, dlc=spec.dlc, data=spec.payload)
        latencies.append(time.perf_counter() - start)
    return latencies


def _measure_extract(client: AletheiaClient, spec: FrameSpec, num_ops: int) -> list[float]:
    """Per-op extract_signals latencies."""
    latencies: list[float] = []
    for _ in range(num_ops):
        start = time.perf_counter()
        client.extract_signals(can_id=spec.can_id, dlc=spec.dlc, data=spec.payload)
        latencies.append(time.perf_counter() - start)
    return latencies


def _measure_build(client: AletheiaClient, spec: FrameSpec, num_ops: int) -> list[float]:
    """Per-op build_frame latencies."""
    latencies: list[float] = []
    for _ in range(num_ops):
        start = time.perf_counter()
        client.build_frame(can_id=spec.can_id, dlc=spec.dlc, signals=spec.signals)
        latencies.append(time.perf_counter() - start)
    return latencies


def analyze_latencies(latencies: list[float]) -> _LatencyStats:
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


def print_latency_stats(name: str, stats: _LatencyStats, file: IO[str] | None = None) -> None:
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


def _bench_stream_lane(ctx: LatencyContext) -> tuple[str, _LatencyStats]:
    """Run streaming-mode latency for one frame type and return (name, stats)."""
    print(f"\nBenchmarking {ctx.label} streaming...", file=ctx.file)
    spec = ctx.spec
    with AletheiaClient() as client:
        client.parse_dbc(ctx.dbc)
        client.set_properties(ctx.properties)
        client.start_stream()
        for i in range(ctx.warmup):
            client.send_frame(timestamp=i, can_id=spec.can_id, dlc=spec.dlc, data=spec.payload)
        latencies = _measure_stream(client, spec, ctx.num_ops)
        client.end_stream()
    stats = analyze_latencies(latencies)
    name = f"{ctx.label} Streaming LTL"
    print_latency_stats(name, stats, file=ctx.file)
    return name, stats


def _bench_extract_lane(ctx: LatencyContext) -> tuple[str, _LatencyStats]:
    """Run extract-signals latency for one frame type and return (name, stats)."""
    print(f"\nBenchmarking {ctx.label} signal extraction...", file=ctx.file)
    spec = ctx.spec
    with AletheiaClient() as client:
        client.parse_dbc(ctx.dbc)
        for _ in range(ctx.warmup):
            client.extract_signals(can_id=spec.can_id, dlc=spec.dlc, data=spec.payload)
        latencies = _measure_extract(client, spec, ctx.num_ops)
    stats = analyze_latencies(latencies)
    name = f"{ctx.label} Signal Extraction"
    print_latency_stats(name, stats, file=ctx.file)
    return name, stats


def _bench_build_lane(ctx: LatencyContext) -> tuple[str, _LatencyStats]:
    """Run frame-build latency for one frame type and return (name, stats)."""
    print(f"\nBenchmarking {ctx.label} frame building...", file=ctx.file)
    spec = ctx.spec
    with AletheiaClient() as client:
        client.parse_dbc(ctx.dbc)
        for _ in range(ctx.warmup):
            client.build_frame(can_id=spec.can_id, dlc=spec.dlc, signals=spec.signals)
        latencies = _measure_build(client, spec, ctx.num_ops)
    stats = analyze_latencies(latencies)
    name = f"{ctx.label} Frame Building"
    print_latency_stats(name, stats, file=ctx.file)
    return name, stats


def run_latency_suite(ctx: LatencyContext) -> list[tuple[str, _LatencyStats]]:
    """Run streaming, extraction, and build latency for one frame type."""
    return [
        _bench_stream_lane(ctx),
        _bench_extract_lane(ctx),
        _bench_build_lane(ctx),
    ]


def _print_summary(all_stats: list[tuple[str, _LatencyStats]], file: IO[str]) -> None:
    """Print the formatted summary table to the given stream."""
    print("\n" + "=" * 70, file=file)
    print("Summary (all times in microseconds)", file=file)
    print("=" * 70, file=file)
    print(
        f"{'Operation':<30} {'Mean':>10} {'p50':>10} {'p99':>10} {'p99.9':>10}",
        file=file,
    )
    print("-" * 70, file=file)
    for name, stats in all_stats:
        print(
            f"{name:<30} {stats['mean_us']:>10.1f} {stats['p50_us']:>10.1f} "
            + f"{stats['p99_us']:>10.1f} {stats['p999_us']:>10.1f}",
            file=file,
        )
    print("=" * 70, file=file)


def _to_json_payload(name: str, stats: _LatencyStats) -> _JsonStatsRow:
    """Project (name, stats) into the JSON-report shape."""
    return {
        "name": name,
        "count": stats["count"],
        "mean_us": round(stats["mean_us"], 1),
        "min_us": round(stats["min_us"], 1),
        "max_us": round(stats["max_us"], 1),
        "p50_us": round(stats["p50_us"], 1),
        "p90_us": round(stats["p90_us"], 1),
        "p99_us": round(stats["p99_us"], 1),
        "p999_us": round(stats["p999_us"], 1),
    }


def main() -> int:
    """CLI entry point — parse args, run latency suites, emit summary."""
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

    all_stats = run_latency_suite(LatencyContext(
        label="CAN 2.0B", dbc=load_dbc(), spec=CAN20_SPEC,
        properties=DEFAULT_CAN20_PROPERTIES,
        num_ops=args.ops, warmup=args.warmup, file=out,
    ))
    all_stats += run_latency_suite(LatencyContext(
        label="CAN-FD", dbc=load_canfd_dbc(), spec=CANFD_SPEC,
        properties=DEFAULT_CANFD_PROPERTIES,
        num_ops=args.ops, warmup=args.warmup, file=out,
    ))

    _print_summary(all_stats, out)

    if args.json:
        emit_json_report("latency", [_to_json_payload(n, s) for n, s in all_stats])

    return 0


if __name__ == "__main__":
    sys.exit(main())
