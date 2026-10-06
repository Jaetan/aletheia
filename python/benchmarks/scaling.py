# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Scaling Benchmark.

Measures how Aletheia performance scales with:

- Trace size (1K to 100K frames)
- Property count (1 to 10 properties)
- Property complexity (simple vs nested temporal operators)
- DBC size (load time for 1,250 to 10,000 messages)

Tests both CAN 2.0B and CAN-FD frames for trace size scaling.

Usage:
    python3 scaling.py [--quick]
"""

from __future__ import annotations

import argparse
import sys
import time
from fractions import Fraction
from statistics import fmean
from typing import IO, TYPE_CHECKING, NamedTuple, NewType, TextIO, TypedDict

# Shared vocabulary lives in ``_common``; see PY-31-1 for the dedup rationale.
from benchmarks._common import (
    CAN20_SPEC,
    CANFD_SPEC,
    FrameSpec,
    RunCount,
    ScalingParameters,
    emit_json_report,
    load_canfd_dbc,
    load_dbc,
    run_streaming_benchmark,
)

# See ``throughput.py`` — benchmarks import the installed package to keep
# the wheel / setuptools shim cost inside the measurement.
from aletheia import AletheiaClient, Signal
from aletheia._dbc_types import BitLength, SignalName, raw_unsigned_signal
from aletheia.types import DLCByteCount

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.dsl import Property
    from aletheia.types import DBCDefinition, LTLFormula

# A DBC's number of messages, a load's wall-clock duration, messages loaded per
# second, and a rate over the sweep's first rate.
MessageCount = NewType("MessageCount", int)
Seconds = NewType("Seconds", float)
MessageRate = NewType("MessageRate", float)
RelativeRate = NewType("RelativeRate", float)


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


class _DbcSizeRow(TypedDict):
    """One row from the DBC-size scaling sweep."""

    messages: MessageCount
    seconds: Seconds
    messages_per_sec: MessageRate
    relative: RelativeRate


class _ScalingResults(TypedDict):
    """Every sweep's rows aggregated into one JSON-report payload."""

    trace_size_can20: list[_TraceSizeRow]
    trace_size_canfd: list[_TraceSizeRow]
    property_count: list[_PropertyCountRow]
    property_complexity: list[_PropertyComplexityRow]
    dbc_size: list[_DbcSizeRow]


def benchmark_frames_per_sec(
    dbc: DBCDefinition,
    num_frames: int,
    properties: list[LTLFormula],
    spec: FrameSpec,
) -> tuple[float, float]:
    """Benchmark streaming throughput. Returns (frames_per_sec, total_time)."""
    return run_streaming_benchmark(dbc, num_frames, spec, properties)


def mean_fps(
    dbc: DBCDefinition,
    num_frames: int,
    properties: list[LTLFormula],
    spec: FrameSpec,
    runs: int,
) -> tuple[float, float]:
    """Mean fps + total elapsed over ``runs`` streaming passes.

    Every streaming point is averaged over ``runs`` passes (default 5): the sweep
    reports ``relative = fps / baseline_fps``, so noise on an un-averaged
    baseline row would multiply into every ratio. Matches the run-averaging the
    C++/Go/Rust harnesses use — the robust methodology, kept identical across
    all four bindings.
    """
    samples = [benchmark_frames_per_sec(dbc, num_frames, properties, spec) for _ in range(runs)]
    fps_values = [s[0] for s in samples]
    total_elapsed = sum(s[1] for s in samples)
    return fmean(fps_values), total_elapsed


def _trace_sizes(*, quick: bool) -> list[int]:
    """Return the trace-size sweep (smaller in --quick mode)."""
    return [1000, 5000, 10000, 50000] if quick else [1000, 5000, 10000, 50000, 100000]


class _TraceTarget(NamedTuple):
    """A trace-size sweep's fixed inputs: which DBC, frame spec, and properties."""

    dbc: DBCDefinition
    spec: FrameSpec
    properties: list[LTLFormula]


def _scan_trace_sizes(
    target: _TraceTarget,
    sizes: list[int],
    runs: int,
    file: IO[str],
) -> list[_TraceSizeRow]:
    """Sweep trace sizes for one frame type and return per-size result rows."""
    print(f"{'Frames':>10} {'Time (s)':>10} {'Frames/sec':>12} {'Relative':>10}", file=file)
    print("-" * 45, file=file)
    baseline_fps: float | None = None
    results: list[_TraceSizeRow] = []
    for size in sizes:
        fps, elapsed = mean_fps(target.dbc, size, target.properties, target.spec, runs)
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
    runs: int = 5,
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
    target = _TraceTarget(dbc, CAN20_SPEC, properties)
    return _scan_trace_sizes(target, _trace_sizes(quick=quick), runs, out)


def benchmark_trace_size_scaling_canfd(
    canfd_dbc: DBCDefinition,
    *,
    quick: bool = False,
    runs: int = 5,
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
    target = _TraceTarget(canfd_dbc, CANFD_SPEC, properties)
    return _scan_trace_sizes(target, _trace_sizes(quick=quick), runs, out)


def _property_templates() -> list[Callable[[], Property]]:
    """Templates used by the property-count sweep."""
    return [
        lambda: Signal("EngineSpeed").between(0, 8000).always(),
        lambda: Signal("EngineTemp").between(-40, 215).always(),
        lambda: Signal("BrakePressure").less_than(Fraction("6553.5")).always(),
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
    runs: int = 5,
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
        fps, _ = mean_fps(dbc, num_frames, properties, CAN20_SPEC, runs)
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
                Signal("BrakePressure").less_than(Fraction("6553.5")).always().to_dict(),
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
    runs: int = 5,
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
        fps, _ = mean_fps(dbc, num_frames, properties, CAN20_SPEC, runs)
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


def _dbc_sizes(*, quick: bool) -> list[MessageCount]:
    """Return the DBC-size sweep in messages, each double the last (--quick drops the smallest)."""
    sizes = [2500, 5000, 10000] if quick else [1250, 2500, 5000, 10000]
    return [MessageCount(size) for size in sizes]


def _sized_dbc(messages: MessageCount) -> DBCDefinition:
    """Build a DBC of ``messages`` extended-ID messages, every kind of reference growing with them.

    Message ``i`` is ``M{i}`` at CAN ID ``0x100000 + i``, sent by node ``N{i}``
    and by one more sender, the next node round the ring
    (``N{(i + 1) % messages}``); its one 8-bit signal ``S{i}`` is received by
    ``N{i}``, and one comment targets it.  The nodes are ``N0`` to
    ``N{messages - 1}``.  So the nodes, senders, receivers and comments grow in
    proportion to the messages and double with them, every name resolves, and
    no two messages share an ID or a name: the load succeeds.
    """
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x100000 + i,
                "name": f"M{i}",
                "dlc": DLCByteCount(8),
                "sender": f"N{i}",
                "senders": [f"N{(i + 1) % messages}"],
                "extended": True,
                "signals": [
                    {
                        **raw_unsigned_signal(SignalName(f"S{i}"), BitLength(8)),
                        "receivers": [f"N{i}"],
                    }
                ],
            }
            for i in range(messages)
        ],
        "signalGroups": [],
        "environmentVars": [],
        "valueTables": [],
        "nodes": [{"name": f"N{i}"} for i in range(messages)],
        "comments": [
            {"target": {"kind": "message", "id": 0x100000 + i, "extended": True}, "text": "c"}
            for i in range(messages)
        ],
        "attributes": [],
        "unresolvedValueDescs": [],
    }


def _load_seconds(dbc: DBCDefinition) -> Seconds:
    """Time one ``parse_dbc`` on a fresh client, closed after it.

    Raises ``RuntimeError`` when the load is refused, or the client's
    ``InputBoundExceededError`` when a bound refuses it, so a refusal is never
    recorded as a time.
    """
    with AletheiaClient() as client:
        start = time.perf_counter()
        result = client.parse_dbc(dbc)
        elapsed = Seconds(time.perf_counter() - start)
    if result["status"] != "success":
        msg = (
            f"parse_dbc refused a {len(dbc['messages'])}-message DBC: "
            + f"{result['code']}: {result['message']}"
        )
        raise RuntimeError(msg)
    return elapsed


def benchmark_dbc_size_scaling(
    *,
    runs: RunCount,
    quick: bool = False,
    file: TextIO | None = None,
) -> list[_DbcSizeRow]:
    """Test how DBC load time scales with the number of messages.

    Each point is the minimum over ``runs`` loads: the sweep compares sizes'
    times, and the minimum is the least noisy estimate of the work.
    """
    out = file or sys.stdout
    print("\n" + "=" * 70, file=out)
    print("5. DBC Size Scaling", file=out)
    print("=" * 70, file=out)
    print("Testing DBC load time as the message count increases...", file=out)
    print(file=out)

    _load_seconds(_sized_dbc(MessageCount(500)))  # warm-up; its time is discarded

    print(f"{'Messages':>10} {'Time (s)':>10} {'Messages/sec':>12} {'Relative':>10}", file=out)
    print("-" * 45, file=out)

    baseline_rate: MessageRate | None = None
    results: list[_DbcSizeRow] = []
    for size in _dbc_sizes(quick=quick):
        dbc = _sized_dbc(size)
        seconds = min(_load_seconds(dbc) for _ in range(runs))
        rate = MessageRate(size / seconds)
        if baseline_rate is None:
            baseline_rate = rate
        relative = RelativeRate(rate / baseline_rate)
        print(f"{size:>10,} {seconds:>10.4f} {rate:>12,.0f} {relative:>10.2f}x", file=out)
        results.append(
            {
                "messages": size,
                "seconds": Seconds(round(seconds, 4)),
                "messages_per_sec": MessageRate(round(rate, 1)),
                "relative": RelativeRate(round(relative, 3)),
            }
        )

    print(file=out)
    print(
        "Expected: Relative stays near 1.0x (load time linear in the number of messages)",
        file=out,
    )
    return results


def main() -> int:
    """CLI entry point — parse args, run all scaling sweeps, emit summary."""
    parser = argparse.ArgumentParser(description="Scaling benchmark")
    parser.add_argument("--quick", action="store_true", help="Run faster with fewer iterations")
    parser.add_argument(
        "--runs",
        type=int,
        default=5,
        help="Passes per sweep point: streaming averaged, DBC loads minimum",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    args = parser.parse_args()

    out = sys.stderr if args.json else sys.stdout

    print("=" * 70, file=out)
    print("Aletheia Scaling Benchmark", file=out)
    print("=" * 70, file=out)
    print(f"Runs per point: {args.runs}", file=out)
    if args.quick:
        print("(Quick mode - reduced iterations)", file=out)

    dbc = load_dbc()
    canfd_dbc = load_canfd_dbc()

    print("\nWarming up...", file=out)
    props = [Signal("EngineSpeed").between(0, 8000).always().to_dict()]
    benchmark_frames_per_sec(dbc, 1000, props, CAN20_SPEC)
    print("Done.", file=out)

    results: _ScalingResults = {
        "trace_size_can20": benchmark_trace_size_scaling(
            dbc, quick=args.quick, runs=args.runs, file=out
        ),
        "trace_size_canfd": benchmark_trace_size_scaling_canfd(
            canfd_dbc, quick=args.quick, runs=args.runs, file=out
        ),
        "property_count": benchmark_property_count_scaling(
            dbc, quick=args.quick, runs=args.runs, file=out
        ),
        "property_complexity": benchmark_property_complexity_scaling(
            dbc, quick=args.quick, runs=args.runs, file=out
        ),
        "dbc_size": benchmark_dbc_size_scaling(
            quick=args.quick, runs=RunCount(args.runs), file=out
        ),
    }

    print("\n" + "=" * 70, file=out)
    print("Scaling benchmark complete", file=out)
    print("=" * 70, file=out)

    if args.json:
        parameters: ScalingParameters = {"runs": RunCount(args.runs), "quick": args.quick}
        emit_json_report("scaling", parameters, results)

    return 0


if __name__ == "__main__":
    sys.exit(main())
