#!/usr/bin/env python3
"""
Cross-Language Benchmark Comparison

Reads JSON benchmark results from Python, C++, and Go benchmarks,
and produces a side-by-side comparison table.

Usage:
    python3 benchmarks/compare.py results/python.json results/cpp.json results/go.json
    python3 benchmarks/compare.py results/*.json
"""

import json
import sys
from pathlib import Path


def load_results(paths: list[str]) -> dict[str, dict]:
    """Load JSON results keyed by language."""
    by_language: dict[str, dict] = {}
    for path in paths:
        with open(path) as f:
            data = json.load(f)
        lang = data.get("language", Path(path).stem)
        by_language[lang] = data
    return by_language


def compare_throughput(by_language: dict[str, dict]):
    """Compare throughput results across languages."""
    languages = sorted(by_language.keys())
    col_width = 12

    # Collect all benchmark names
    all_names: list[str] = []
    for data in by_language.values():
        if data.get("benchmark") != "throughput":
            continue
        for r in data.get("results", []):
            name = r["name"]
            if name not in all_names:
                all_names.append(name)

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
            data = by_language[lang]
            if data.get("benchmark") != "throughput":
                row += f"{'—':>{col_width}}"
                continue
            found = False
            for r in data.get("results", []):
                if r["name"] == name:
                    row += f"{r['fps_mean']:>{col_width},.0f}"
                    found = True
                    break
            if not found:
                row += f"{'—':>{col_width}}"
        print(row)
    print()


def compare_latency(by_language: dict[str, dict]):
    """Compare latency results across languages."""
    languages = sorted(by_language.keys())
    col_width = 12

    all_names: list[str] = []
    for data in by_language.values():
        if data.get("benchmark") != "latency":
            continue
        for r in data.get("results", []):
            name = r["name"]
            if name not in all_names:
                all_names.append(name)

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
            data = by_language[lang]
            if data.get("benchmark") != "latency":
                row += f"{'—':>{col_width}}" * 2
                continue
            found = False
            for r in data.get("results", []):
                if r["name"] == name:
                    row += f"{r['p50_us']:>{col_width},.1f}"
                    row += f"{r['p99_us']:>{col_width},.1f}"
                    found = True
                    break
            if not found:
                row += f"{'—':>{col_width}}" * 2
        print(row)
    print()


def compare_scaling(by_language: dict[str, dict]):
    """Compare scaling results across languages."""
    languages = sorted(by_language.keys())
    col_width = 12

    has_scaling = False
    for data in by_language.values():
        if data.get("benchmark") == "scaling":
            has_scaling = True
            break

    if not has_scaling:
        return

    print("=" * 70)
    print("Property Count Scaling Comparison (fps)")
    print("=" * 70)

    header = f"{'Properties':>10}"
    for lang in languages:
        header += f"{lang:>{col_width}}"
    print(header)
    print("-" * (10 + col_width * len(languages)))

    # Use first language's property counts as reference
    ref_counts = []
    for data in by_language.values():
        if data.get("benchmark") != "scaling":
            continue
        results = data.get("results", {})
        prop_count = results.get("property_count", [])
        if prop_count:
            ref_counts = [r["properties"] for r in prop_count]
            break

    for count in ref_counts:
        row = f"{count:>10}"
        for lang in languages:
            data = by_language[lang]
            if data.get("benchmark") != "scaling":
                row += f"{'—':>{col_width}}"
                continue
            results = data.get("results", {})
            prop_count = results.get("property_count", [])
            found = False
            for r in prop_count:
                if r["properties"] == count:
                    row += f"{r['fps']:>{col_width},.0f}"
                    found = True
                    break
            if not found:
                row += f"{'—':>{col_width}}"
        print(row)
    print()


def main():
    if len(sys.argv) < 2:
        print("Usage: compare.py <result1.json> [result2.json] ...", file=sys.stderr)
        return 1

    by_language = load_results(sys.argv[1:])

    if not by_language:
        print("No results loaded.", file=sys.stderr)
        return 1

    # Group by benchmark type
    throughput_data: dict[str, dict] = {}
    latency_data: dict[str, dict] = {}
    scaling_data: dict[str, dict] = {}

    for lang, data in by_language.items():
        bench_type = data.get("benchmark", "")
        if bench_type == "throughput":
            throughput_data[lang] = data
        elif bench_type == "latency":
            latency_data[lang] = data
        elif bench_type == "scaling":
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
