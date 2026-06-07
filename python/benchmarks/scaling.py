#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Scaling Benchmark.

Measures how Aletheia performance scales with:

- Trace size (1K to 100K frames)
- Property count (1 to 10 properties)
- Property complexity (simple vs nested temporal operators)

Tests both CAN 2.0B and CAN-FD frames for trace size scaling.

Usage:
    python3 scaling.py [--quick]
"""

from __future__ import annotations

import argparse
import sys
from typing import IO, TYPE_CHECKING, NamedTuple, TypedDict

# Shared vocabulary lives in ``_common``; see PY-31-1 for the dedup rationale.
from benchmarks._common import (
    CAN20_SPEC,
    CANFD_SPEC,
    FrameSpec,
    emit_json_report,
    load_canfd_dbc,
    load_dbc,
    run_streaming_benchmark,
)

# See ``throughput.py`` — benchmarks import the installed package to keep
# the wheel / setuptools shim cost inside the measurement.
from aletheia import Signal

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.dsl import Property
    from aletheia.types import DBCDefinition, LTLFormula


class _TraceSizeRow(TypedDict):
    """One row from the trace-size scaling sweep."""

    frames: int
    fps: float
    relative: float


class _PropertyCountRow(TypedDict):
    """One row from the property-count scaling sweep."""

    properties: int
    fps: float
    us_per_frame: float
    relative: float


class _PropertyComplexityRow(TypedDict):
    """One row from the property-complexity scaling sweep."""

    complexity: str
    fps: float
    us_per_frame: float
    relative: float


class _ScalingResults(TypedDict):
    """All four sweep rows aggregated into one JSON-report payload."""

    trace_size_can20: list[_TraceSizeRow]
    trace_size_canfd: list[_TraceSizeRow]
    property_count: list[_PropertyCountRow]
    property_complexity: list[_PropertyComplexityRow]


def benchmark_frames_per_sec(
    dbc: DBCDefinition,
    num_frames: int,
    properties: list[LTLFormula],
    spec: FrameSpec,
) -> tuple[float, float]:
    """Benchmark streaming throughput. Returns (frames_per_sec, total_time)."""
    return run_streaming_benchmark(dbc, num_frames, spec, properties)


def _trace_sizes(*, quick: bool) -> list[int]:
    """Return the trace-size sweep (smaller in --quick mode)."""
    return [1000, 5000, 10000, 50000] if quick else [1000, 5000, 10000, 50000, 100000]


def _scan_trace_sizes(
    dbc: DBCDefinition,
    spec: FrameSpec,
    properties: list[LTLFormula],
    sizes: list[int],
    file: IO[str],
) -> list[_TraceSizeRow]:
    """Sweep trace sizes for one frame type and return per-size result rows."""
    print(f"{'Frames':>10} {'Time (s)':>10} {'Frames/sec':>12} {'Relative':>10}", file=file)
    print("-" * 45, file=file)
    baseline_fps: float | None = None
    results: list[_TraceSizeRow] = []
    for size in sizes:
        fps, elapsed = benchmark_frames_per_sec(dbc, size, properties, spec)
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{size:>10,} {elapsed:>10.2f} {fps:>12,.0f} {relative:>10.2f}x", file=file)
        results.append({"frames": size, "fps": round(fps, 1), "relative": round(relative, 3)})
    print(file=file)
    print("Expected: Relative throughput should stay near 1.0x (O(1) per frame)", file=file)
    return results


def benchmark_trace_size_scaling(
    dbc: DBCDefinition,
    *,
    quick: bool = False,
    file: IO[str] | None = None,
) -> list[_TraceSizeRow]:
    """Test how throughput scales with trace size (CAN 2.0B)."""
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("1. Trace Size Scaling (CAN 2.0B)", file=out)
    print("=" * 70, file=out)
    print("Testing throughput as trace size increases...", file=out)
    print("(Verifies O(1) memory and constant throughput)", file=out)
    print(file=out)
    properties = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]
    return _scan_trace_sizes(dbc, CAN20_SPEC, properties, _trace_sizes(quick=quick), out)


def benchmark_trace_size_scaling_canfd(
    canfd_dbc: DBCDefinition,
    *,
    quick: bool = False,
    file: IO[str] | None = None,
) -> list[_TraceSizeRow]:
    """Test how throughput scales with trace size (CAN-FD)."""
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("2. Trace Size Scaling (CAN-FD, 64 bytes)", file=out)
    print("=" * 70, file=out)
    print("Testing CAN-FD throughput as trace size increases...", file=out)
    print(file=out)
    properties = [Signal("GPSSpeed").between(0, 655).always().to_dict()]
    return _scan_trace_sizes(canfd_dbc, CANFD_SPEC, properties, _trace_sizes(quick=quick), out)


def _property_templates() -> list[Callable[[], Property]]:
    """Templates used by the property-count sweep."""
    return [
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


def benchmark_property_count_scaling(
    dbc: DBCDefinition,
    *,
    quick: bool = False,
    file: IO[str] | None = None,
) -> list[_PropertyCountRow]:
    """Test how throughput scales with number of properties."""
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("3. Property Count Scaling", file=out)
    print("=" * 70, file=out)
    print("Testing throughput as property count increases...", file=out)
    print(file=out)

    num_frames = 5000 if quick else 10000
    templates = _property_templates()
    counts = [1, 2, 3, 5, 7, 10]

    print(f"{'Properties':>10} {'Frames/sec':>12} {'us/frame':>10} {'Relative':>10}", file=out)
    print("-" * 45, file=out)

    baseline_fps: float | None = None
    results: list[_PropertyCountRow] = []
    for count in counts:
        properties = [templates[i % len(templates)]().to_dict() for i in range(count)]
        fps, _ = benchmark_frames_per_sec(dbc, num_frames, properties, CAN20_SPEC)
        us_per_frame = 1_000_000 / fps
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{count:>10} {fps:>12,.0f} {us_per_frame:>10.1f} {relative:>10.2f}x", file=out)
        results.append(
            {
                "properties": count,
                "fps": round(fps, 1),
                "us_per_frame": round(us_per_frame, 1),
                "relative": round(relative, 3),
            }
        )

    print(file=out)
    print("Expected: Some degradation, but should be sub-linear", file=out)
    return results


class ComplexityLevel(NamedTuple):
    """A labelled property bundle for the complexity-scaling sweep."""

    label: str
    properties: list[LTLFormula]


def _complexity_levels() -> list[ComplexityLevel]:
    """Property bundles used by the complexity-scaling sweep."""
    raw = [
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
            [
                Signal("EngineSpeed")
                .less_than(1000)
                .implies(Signal("EngineTemp").less_than(100))
                .always()
                .to_dict()
            ],
        ),
    ]
    return [ComplexityLevel(*_entry) for _entry in raw]


def benchmark_property_complexity_scaling(
    dbc: DBCDefinition,
    *,
    quick: bool = False,
    file: IO[str] | None = None,
) -> list[_PropertyComplexityRow]:
    """Test how throughput scales with property complexity."""
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("4. Property Complexity Scaling", file=out)
    print("=" * 70, file=out)
    print("Testing throughput with different property complexities...", file=out)
    print(file=out)

    num_frames = 5000 if quick else 10000

    print(f"{'Complexity':<25} {'Frames/sec':>12} {'us/frame':>10} {'Relative':>10}", file=out)
    print("-" * 60, file=out)

    baseline_fps: float | None = None
    results: list[_PropertyComplexityRow] = []
    for name, properties in _complexity_levels():
        fps, _ = benchmark_frames_per_sec(dbc, num_frames, properties, CAN20_SPEC)
        us_per_frame = 1_000_000 / fps
        if baseline_fps is None:
            baseline_fps = fps
        relative = fps / baseline_fps
        print(f"{name:<25} {fps:>12,.0f} {us_per_frame:>10.1f} {relative:>10.2f}x", file=out)
        results.append(
            {
                "complexity": name,
                "fps": round(fps, 1),
                "us_per_frame": round(us_per_frame, 1),
                "relative": round(relative, 3),
            }
        )

    print(file=out)
    print("Expected: More complex properties should be slower", file=out)
    return results


def main() -> int:
    """CLI entry point — parse args, run all scaling sweeps, emit summary."""
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

    print("\nWarming up...", file=out)
    props = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]
    benchmark_frames_per_sec(dbc, 1000, props, CAN20_SPEC)
    print("Done.", file=out)

    results: _ScalingResults = {
        "trace_size_can20": benchmark_trace_size_scaling(dbc, quick=args.quick, file=out),
        "trace_size_canfd": benchmark_trace_size_scaling_canfd(
            canfd_dbc, quick=args.quick, file=out
        ),
        "property_count": benchmark_property_count_scaling(dbc, quick=args.quick, file=out),
        "property_complexity": benchmark_property_complexity_scaling(
            dbc, quick=args.quick, file=out
        ),
    }

    print("\n" + "=" * 70, file=out)
    print("Scaling benchmark complete", file=out)
    print("=" * 70, file=out)

    if args.json:
        emit_json_report("scaling", results)

    return 0


if __name__ == "__main__":
    sys.exit(main())
