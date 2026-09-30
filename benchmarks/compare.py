#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Cross-Language Benchmark Comparison.

Reads the JSON result files the Python, C++, Go and Rust benchmarks write and
prints one side-by-side table per mode given. A file is a column, named by its
binding plus whatever its name adds beyond ``<binding>_<mode>``, so a fresh
run and its committed baseline print as ``cpp`` and ``cpp baseline``, and a
binding given with both prints a second table per lane: the current mean, the
baseline mean, the delta and the current standard deviation.

Usage:
    python3 benchmarks/compare.py benchmarks/results/*_throughput.json
    python3 benchmarks/compare.py benchmarks/results/cpp_throughput*.json
    python3 benchmarks/compare.py benchmarks/results/*_throughput_baseline.json
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NotRequired, TypedDict, cast

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable


class _ThroughputRow(TypedDict):
    """One throughput result row."""

    name: str
    fps_mean: float
    fps_stdev: float


class _LatencyRow(TypedDict):
    """One latency result row (percentiles in microseconds)."""

    name: str
    p50_us: float
    p99_us: float


class _ScalingRow(TypedDict):
    """One scaling row: an identifying column (frames/properties/complexity) + fps."""

    fps: float


class _ScalingResults(TypedDict):
    """Scaling result payload: a dict of four sweeps (see benchmarks/SCHEMA.yaml)."""

    trace_size_can20: list[_ScalingRow]
    trace_size_canfd: list[_ScalingRow]
    property_count: list[_ScalingRow]
    property_complexity: list[_ScalingRow]


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
# The tag a committed baseline's name adds beyond ``<binding>_<mode>``.
_BASELINE = "baseline"
# A column is at least this wide; a longer label widens every column of its table.
_MIN_COL = 12
_RULE = "=" * 70


def _column(path: str, data: _ResultFile) -> tuple[str, str]:
    """Return (language, column label) for a file.

    The label is the language, plus whatever the file's stem carries beyond
    ``<language>_<mode>``: a committed ``cpp_throughput_baseline.json`` prints
    as ``cpp baseline`` beside a fresh ``cpp_throughput.json`` printing as ``cpp``.
    """
    stem = Path(path).stem
    lang = data.get("language", stem)
    prefix = f"{lang}_{data['benchmark']}"
    extra = stem.removeprefix(prefix).strip("_") if stem.startswith(prefix) else ""
    return lang, f"{lang} {extra}".strip()


def load_results(paths: list[str]) -> dict[str, dict[str, tuple[str, _ResultFile]]]:
    """Load JSON results as ``mode -> column label -> (path, data)``.

    Skips a corrupt or unreadable file with a warning. Two files that would
    share a column of one table are refused, both named, rather than the
    later one replacing the earlier without a word.
    """
    by_mode: dict[str, dict[str, tuple[str, _ResultFile]]] = {}
    for path in paths:
        try:
            with Path(path).open(encoding="utf-8") as f:
                data = cast("_ResultFile", json.load(f))
        except (OSError, json.JSONDecodeError) as e:
            print(f"WARNING: skipping {path}: {e}", file=sys.stderr)
            continue
        _, label = _column(path, data)
        columns = by_mode.setdefault(data["benchmark"], {})
        if label in columns:
            first = columns[label][0]
            table = f"the {label!r} column of the {data['benchmark']} table"
            print(f"ERROR: {path} and {first} would both print as {table}", file=sys.stderr)
            sys.exit(1)
        columns[label] = (path, data)
    return by_mode


def _width(labels: Iterable[str]) -> int:
    """Column width: the floor, or the longest label plus a gutter."""
    return max([_MIN_COL, *(len(label) + 2 for label in labels)])


def _delta(current: float, baseline: float) -> str:
    """Percentage change from baseline to current, signed, or a dash at zero."""
    if baseline == 0:
        return "n/a"
    return f"{100 * (current - baseline) / baseline:+.1f}%"


def _lane_names(files: Iterable[_ThroughputFile | _LatencyFile]) -> list[str]:
    """Every lane name across the files, first appearance first."""
    names: list[str] = []
    for data in files:
        for r in data["results"]:
            if r["name"] not in names:
                names.append(r["name"])
    return names


def _lane[R: (_ThroughputRow, _LatencyRow)](rows: list[R], name: str) -> R | None:
    """Return the row of a lane in a file, if the file carries it."""
    return next((r for r in rows if r["name"] == name), None)


def compare_throughput(columns: dict[str, _ThroughputFile]) -> None:
    """Print throughput means side by side, one column per file."""
    labels = sorted(columns)
    names = _lane_names(columns.values())
    if not names:
        return
    col = _width(labels)
    print(_RULE)
    print("Throughput Comparison (frames/sec)")
    print(_RULE)
    print(f"{'Benchmark':<35}" + "".join(f"{label:>{col}}" for label in labels))
    print("-" * (35 + col * len(labels)))
    for name in names:
        row = f"{name:<35}"
        for label in labels:
            match = _lane(columns[label]["results"], name)
            row += f"{match['fps_mean']:>{col},.0f}" if match else f"{'n/a':>{col}}"
        print(row)
    print()


def compare_latency(columns: dict[str, _LatencyFile]) -> None:
    """Print p50 and p99 latencies side by side, two columns per file."""
    labels = sorted(columns)
    names = _lane_names(columns.values())
    if not names:
        return
    col = _width(f"p50 {label}" for label in labels)
    print(_RULE)
    print("Latency Comparison (p50 / p99 in microseconds)")
    print(_RULE)
    head = "".join(f"{'p50 ' + label:>{col}}{'p99 ' + label:>{col}}" for label in labels)
    print(f"{'Benchmark':<30}{head}")
    print("-" * (30 + col * 2 * len(labels)))
    for name in names:
        row = f"{name:<30}"
        for label in labels:
            match = _lane(columns[label]["results"], name)
            if match:
                row += f"{match['p50_us']:>{col},.1f}{match['p99_us']:>{col},.1f}"
            else:
                row += f"{'n/a':>{col}}" * 2
        print(row)
    print()


# (sweep key in the results dict, identifying column, human title). Mirrors the
# four sub-benchmarks pinned in benchmarks/SCHEMA.yaml.
_SCALING_SWEEPS: list[tuple[str, str, str]] = [
    ("trace_size_can20", "frames", "Trace Size (CAN 2.0B)"),
    ("trace_size_canfd", "frames", "Trace Size (CAN-FD)"),
    ("property_count", "properties", "Property Count"),
    ("property_complexity", "complexity", "Property Complexity"),
]


def _sweep_rows(data: _ScalingFile, sweep_key: str) -> list[dict[str, object]]:
    """One sweep's rows, or none when the file lacks the sweep."""
    return cast("list[dict[str, object]]", data["results"].get(sweep_key, []))


def _sweep_ids(files: Iterable[_ScalingFile], sweep_key: str, id_col: str) -> list[object]:
    """Return the identifying values of a sweep, from the first file that carries it."""
    for data in files:
        rows = _sweep_rows(data, sweep_key)
        if rows:
            return [r[id_col] for r in rows]
    return []


def _id_label(idv: object, width: int) -> str:
    """Return an identifying value right-aligned: thousands-grouped for a count."""
    return f"{idv:>{width},}" if isinstance(idv, int) else f"{idv!s:>{width}}"


def _sweep_fps(data: _ScalingFile, sweep_key: str, id_col: str, idv: object) -> float | None:
    """Return the fps a file reports at one identifying value of a sweep, if any."""
    match = next((r for r in _sweep_rows(data, sweep_key) if r.get(id_col) == idv), None)
    return float(cast("float", match["fps"])) if match else None


def _compare_one_sweep(
    columns: dict[str, _ScalingFile], sweep_key: str, id_col: str, title: str
) -> None:
    """Print one sweep's fps table, one column per file, keyed on its id column."""
    labels = sorted(columns)
    col = _width(labels)
    ids = _sweep_ids(columns.values(), sweep_key, id_col)
    idw = _width(str(idv) for idv in ids)
    print(_RULE)
    print(f"{title} Scaling Comparison (fps)")
    print(_RULE)
    print(f"{id_col:>{idw}}" + "".join(f"{label:>{col}}" for label in labels))
    print("-" * (idw + col * len(labels)))
    for idv in ids:
        row = _id_label(idv, idw)
        for label in labels:
            fps = _sweep_fps(columns[label], sweep_key, id_col, idv)
            row += f"{fps:>{col},.0f}" if fps is not None else f"{'n/a':>{col}}"
        print(row)
    print()


def compare_scaling(columns: dict[str, _ScalingFile]) -> None:
    """Compare all four scaling sweeps across the files."""
    for sweep_key, id_col, title in _SCALING_SWEEPS:
        _compare_one_sweep(columns, sweep_key, id_col, title)


def _pairs[F](columns: dict[str, tuple[str, F]]) -> list[tuple[str, F, F]]:
    """(language, current, baseline) for every language given with both."""
    pairs: list[tuple[str, F, F]] = []
    for label, (_, current) in columns.items():
        baseline = columns.get(f"{label} {_BASELINE}")
        if " " not in label and baseline is not None:
            pairs.append((label, current, baseline[1]))
    return pairs


def against_baseline_throughput(
    lang: str, current: _ThroughputFile, baseline: _ThroughputFile
) -> None:
    """Per lane: the current mean, the baseline mean, the delta, the current stdev."""
    print(_RULE)
    print(f"{lang} throughput against its baseline (frames/sec)")
    print(_RULE)
    print(f"{'Benchmark':<35}{'current':>12}{'baseline':>12}{'delta':>9}{'stdev':>12}")
    print("-" * 80)
    for name in _lane_names([current]):
        cur, base = _lane(current["results"], name), _lane(baseline["results"], name)
        row = f"{name:<35}"
        if cur and base:
            row += f"{cur['fps_mean']:>12,.0f}{base['fps_mean']:>12,.0f}"
            row += f"{_delta(cur['fps_mean'], base['fps_mean']):>9}{cur['fps_stdev']:>12,.0f}"
        else:
            row += f"{'n/a':>12}{'n/a':>12}{'n/a':>9}{'n/a':>12}"
        print(row)
    print()


def against_baseline_latency(lang: str, current: _LatencyFile, baseline: _LatencyFile) -> None:
    """Per lane: current and baseline p50 and p99 with the delta of each."""
    print(_RULE)
    print(f"{lang} latency against its baseline (microseconds, lower is better)")
    print(_RULE)
    head = "".join(f"{p:>10}{'base':>10}{'delta':>9}" for p in ("p50", "p99"))
    print(f"{'Benchmark':<30}{head}")
    print("-" * 88)
    for name in _lane_names([current]):
        cur, base = _lane(current["results"], name), _lane(baseline["results"], name)
        row = f"{name:<30}"
        if cur and base:
            for key in ("p50_us", "p99_us"):
                row += f"{cur[key]:>10,.1f}{base[key]:>10,.1f}{_delta(cur[key], base[key]):>9}"
        else:
            row += f"{'n/a':>10}{'n/a':>10}{'n/a':>9}" * 2
        print(row)
    print()


def against_baseline_scaling(lang: str, current: _ScalingFile, baseline: _ScalingFile) -> None:
    """Per sweep and identifying value: current fps, baseline fps, the delta."""
    for sweep_key, id_col, title in _SCALING_SWEEPS:
        ids = _sweep_ids([current], sweep_key, id_col)
        idw = _width(str(idv) for idv in ids)
        print(_RULE)
        print(f"{lang} {title} scaling against its baseline (fps)")
        print(_RULE)
        print(f"{id_col:>{idw}}{'current':>12}{'baseline':>12}{'delta':>9}")
        print("-" * (idw + 33))
        for idv in ids:
            cur = _sweep_fps(current, sweep_key, id_col, idv)
            base = _sweep_fps(baseline, sweep_key, id_col, idv)
            row = _id_label(idv, idw)
            if cur is not None and base is not None:
                row += f"{cur:>12,.0f}{base:>12,.0f}{_delta(cur, base):>9}"
            else:
                row += f"{'n/a':>12}{'n/a':>12}{'n/a':>9}"
            print(row)
        print()


def _print_mode[F](
    columns: dict[str, tuple[str, F]],
    side_by_side: Callable[[dict[str, F]], None],
    against: Callable[[str, F, F], None],
) -> None:
    """One mode's side-by-side table, then a table per binding given with its baseline."""
    side_by_side({label: data for label, (_, data) in columns.items()})
    for lang, current, baseline in _pairs(columns):
        against(lang, current, baseline)


def main() -> int:
    """CLI entry point: load the result files and print the comparison tables."""
    if len(sys.argv) < _MIN_ARGV:
        print("Usage: compare.py <result1.json> [result2.json] ...", file=sys.stderr)
        return 1

    by_mode = load_results(sys.argv[1:])
    if not by_mode:
        print("No results loaded.", file=sys.stderr)
        return 1

    print()
    print("Aletheia Cross-Language Benchmark Comparison")
    print(f"Files: {', '.join(sys.argv[1:])}")
    print()

    if "throughput" in by_mode:
        throughput = cast("dict[str, tuple[str, _ThroughputFile]]", by_mode["throughput"])
        _print_mode(throughput, compare_throughput, against_baseline_throughput)
    if "latency" in by_mode:
        latency = cast("dict[str, tuple[str, _LatencyFile]]", by_mode["latency"])
        _print_mode(latency, compare_latency, against_baseline_latency)
    if "scaling" in by_mode:
        scaling = cast("dict[str, tuple[str, _ScalingFile]]", by_mode["scaling"])
        _print_mode(scaling, compare_scaling, against_baseline_scaling)

    return 0


if __name__ == "__main__":
    sys.exit(main())
