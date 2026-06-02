#!/usr/bin/env python3
"""Cross-Language Benchmark Comparison.

Reads JSON benchmark results from Python, C++, and Go benchmarks,
and produces a side-by-side comparison table.

Usage:
    python3 benchmarks/compare.py results/python.json results/cpp.json results/go.json
    python3 benchmarks/compare.py results/*.json
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Literal, NotRequired, TypedDict, cast


class _ThroughputRow(TypedDict):
    """One throughput result row."""

    name: str
    fps_mean: float


class _LatencyRow(TypedDict):
    """One latency result row (percentiles in microseconds)."""

    name: str
    p50_us: float
    p99_us: float


class _ScalingPropRow(TypedDict):
    """One property-count scaling row."""

    properties: int
    fps: float


class _ScalingResults(TypedDict):
    """Scaling result payload (a dict of sweeps, not a flat list)."""

    property_count: list[_ScalingPropRow]


class _ThroughputFile(TypedDict):
    """A throughput benchmark result file."""

    language: NotRequired[str]
    benchmark: Literal["throughput"]
    results: list[_ThroughputRow]


class _LatencyFile(TypedDict):
    """A latency benchmark result file."""

    language: NotRequired[str]
    benchmark: Literal["latency"]
    results: list[_LatencyRow]


class _ScalingFile(TypedDict):
    """A scaling benchmark result file."""

    language: NotRequired[str]
    benchmark: Literal["scaling"]
    results: _ScalingResults


# Discriminated on the ``benchmark`` tag.
_ResultFile = _ThroughputFile | _LatencyFile | _ScalingFile

# argv needs the script name plus at least one result-file path.
_MIN_ARGV = 2


def load_results(paths: list[str]) -> dict[str, _ResultFile]:
    """Load JSON results keyed by language.  Skips corrupt/unreadable files."""
    by_language: dict[str, _ResultFile] = {}
    for path in paths:
        try:
            with Path(path).open(encoding="utf-8") as f:
                data = cast("_ResultFile", json.load(f))
        except (OSError, json.JSONDecodeError) as e:
            print(f"WARNING: skipping {path}: {e}", file=sys.stderr)
            continue
        lang = data.get("language", Path(path).stem)
        by_language[lang] = data
    return by_language


def compare_throughput(by_language: dict[str, _ThroughputFile]) -> None:
    """Compare throughput results across languages."""
    languages = sorted(by_language.keys())
    col_width = 12

    all_names: list[str] = []
    for data in by_language.values():
        for r in data["results"]:
            if r["name"] not in all_names:
                all_names.append(r["name"])

    if not all_names:
        return

    print("=" * 70)
    print("Throughput Comparison (frames/sec)")
    print("=" * 70)

    header = f"{'Benchmark':<35}"
    for lang in languages:
        header += f"{lang:>{col_width}}"
    print(header)
    print("-" * (35 + col_width * len(languages)))

    for name in all_names:
        row = f"{name:<35}"
        for lang in languages:
            match = next((r for r in by_language[lang]["results"] if r["name"] == name), None)
            row += f"{match['fps_mean']:>{col_width},.0f}" if match else f"{'—':>{col_width}}"
        print(row)
    print()


def compare_latency(by_language: dict[str, _LatencyFile]) -> None:
    """Compare latency results across languages."""
    languages = sorted(by_language.keys())
    col_width = 12

    all_names: list[str] = []
    for data in by_language.values():
        for r in data["results"]:
            if r["name"] not in all_names:
                all_names.append(r["name"])

    if not all_names:
        return

    print("=" * 70)
    print("Latency Comparison (p50 / p99 in microseconds)")
    print("=" * 70)

    header = f"{'Benchmark':<30}"
    for lang in languages:
        header += f"{'p50 ' + lang:>{col_width}}" + f"{'p99 ' + lang:>{col_width}}"
    print(header)
    print("-" * (30 + col_width * 2 * len(languages)))

    for name in all_names:
        row = f"{name:<30}"
        for lang in languages:
            match = next((r for r in by_language[lang]["results"] if r["name"] == name), None)
            if match:
                row += f"{match['p50_us']:>{col_width},.1f}"
                row += f"{match['p99_us']:>{col_width},.1f}"
            else:
                row += f"{'—':>{col_width}}" * 2
        print(row)
    print()


def compare_scaling(by_language: dict[str, _ScalingFile]) -> None:
    """Compare scaling results across languages."""
    languages = sorted(by_language.keys())
    col_width = 12

    print("=" * 70)
    print("Property Count Scaling Comparison (fps)")
    print("=" * 70)

    header = f"{'Properties':>10}"
    for lang in languages:
        header += f"{lang:>{col_width}}"
    print(header)
    print("-" * (10 + col_width * len(languages)))

    # Use the first language's property counts as reference.
    ref_counts: list[int] = []
    for data in by_language.values():
        prop_count = data["results"]["property_count"]
        if prop_count:
            ref_counts = [r["properties"] for r in prop_count]
            break

    for count in ref_counts:
        row = f"{count:>10}"
        for lang in languages:
            prop_count = by_language[lang]["results"]["property_count"]
            match = next((r for r in prop_count if r["properties"] == count), None)
            row += f"{match['fps']:>{col_width},.0f}" if match else f"{'—':>{col_width}}"
        print(row)
    print()


def main() -> int:
    """CLI entry point — load result files and print the comparison tables."""
    if len(sys.argv) < _MIN_ARGV:
        print("Usage: compare.py <result1.json> [result2.json] ...", file=sys.stderr)
        return 1

    by_language = load_results(sys.argv[1:])

    if not by_language:
        print("No results loaded.", file=sys.stderr)
        return 1

    # Group by benchmark type, narrowing the discriminated union on the tag.
    throughput_data: dict[str, _ThroughputFile] = {}
    latency_data: dict[str, _LatencyFile] = {}
    scaling_data: dict[str, _ScalingFile] = {}

    for lang, data in by_language.items():
        if data["benchmark"] == "throughput":
            throughput_data[lang] = data
        elif data["benchmark"] == "latency":
            latency_data[lang] = data
        elif data["benchmark"] == "scaling":
            scaling_data[lang] = data

    print()
    print("Aletheia Cross-Language Benchmark Comparison")
    print(f"Files: {', '.join(sys.argv[1:])}")
    print()

    if throughput_data:
        compare_throughput(throughput_data)
    if latency_data:
        compare_latency(latency_data)
    if scaling_data:
        compare_scaling(scaling_data)

    return 0


if __name__ == "__main__":
    sys.exit(main())
