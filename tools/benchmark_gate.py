# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Throughput regression gate for the cross-language benchmark.

Compares the per-lane mean throughput in ``benchmarks/results/*_<bench>.json``
(produced by ``benchmarks/run_all.sh``) against a committed GitHub-runner
baseline (``benchmarks/gha_baseline.json``) and exits non-zero if any lane is
slower than its baseline by more than ``--threshold-pct``.

The gate runs on the GitHub-hosted runner, which is shared, variable, and a
different machine than the local benchmark host — so the baseline MUST itself be
GHA-measured (never the local numbers, which are several times faster), and the
threshold is deliberately generous: it catches a *noticeable* drop, not
run-to-run jitter. ``run_all.sh``'s 5-run mean already damps within-run noise.

With no baseline file the gate is in *bootstrap* mode: it prints the current
numbers as a baseline-shaped JSON object (copy it into the baseline file from a
known-good run) and exits 0.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import TypedDict, cast

# The three bindings benchmarked by run_all.sh. A lane absent from a run (a
# binding that failed to build) is skipped, not scored as a 100% regression —
# build failures are pr-full-ci's job to report.
BINDINGS = ("cpp", "go", "python")

# Baseline JSON shape: {binding: {lane_name: fps_mean}}.
Baseline = dict[str, dict[str, float]]


class _Row(TypedDict):
    """One lane in a per-binding result file."""

    name: str
    fps_mean: float


class _ResultFile(TypedDict):
    """Shape of ``benchmarks/results/<binding>_<bench>.json`` (fields we read)."""

    results: list[_Row]


def _emit(message: str = "") -> None:
    """Write a line to stdout (ruff ``ALL`` bans bare ``print``; tools write directly)."""
    _ = sys.stdout.write(message + "\n")


def _fail(message: str) -> None:
    """Write a line to stderr."""
    _ = sys.stderr.write(message + "\n")


def _load_results(results_dir: Path, bench: str) -> Baseline:
    """Read each binding's ``<binding>_<bench>.json`` into {binding: {lane: fps}}."""
    out: Baseline = {}
    for binding in BINDINGS:
        path = results_dir / f"{binding}_{bench}.json"
        if not path.is_file():
            continue
        data = cast("_ResultFile", json.loads(path.read_text(encoding="utf-8")))
        out[binding] = {row["name"]: float(row["fps_mean"]) for row in data["results"]}
    return out


def _compare(current: Baseline, baseline: Baseline, threshold_pct: float) -> list[str]:
    """Print a per-lane table; return the lanes that regressed beyond the threshold."""
    regressions: list[str] = []
    _emit(f"benchmark-gate: fail if any lane is >{threshold_pct:.0f}% slower than baseline\n")
    for binding in BINDINGS:
        cur = current.get(binding, {})
        for lane, base_fps in baseline.get(binding, {}).items():
            cur_fps = cur.get(lane)
            if cur_fps is None or base_fps <= 0.0:
                continue
            delta_pct = (cur_fps - base_fps) / base_fps * 100.0
            regressed = -delta_pct > threshold_pct
            flag = "  <-- REGRESSION" if regressed else ""
            cells = f"{base_fps:>11.0f} -> {cur_fps:>11.0f} ({delta_pct:+5.1f}%)"
            _emit(f"  {binding:7s} {lane:32s} {cells}{flag}")
            if regressed:
                regressions.append(
                    f"{binding} / {lane}: {base_fps:.0f} -> {cur_fps:.0f} ({delta_pct:+.1f}%)"
                )
    return regressions


def _parse_args(argv: list[str] | None) -> tuple[str, Path, Path, float]:
    """Parse CLI args into (bench, results_dir, baseline, threshold_pct)."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--bench", default="throughput", help="Benchmark suite (default: throughput)."
    )
    _ = parser.add_argument(
        "--results-dir",
        type=Path,
        default=Path("benchmarks/results"),
        help="Directory of <binding>_<bench>.json (default: benchmarks/results).",
    )
    _ = parser.add_argument(
        "--baseline",
        type=Path,
        default=Path("benchmarks/gha_baseline.json"),
        help="Committed GHA baseline (default: benchmarks/gha_baseline.json).",
    )
    _ = parser.add_argument(
        "--threshold-pct",
        type=float,
        default=30.0,
        help="Fail if a lane is slower than baseline by more than this %% (default: 30).",
    )
    args = parser.parse_args(argv)
    return (
        cast("str", args.bench),
        cast("Path", args.results_dir),
        cast("Path", args.baseline),
        cast("float", args.threshold_pct),
    )


def main(argv: list[str] | None = None) -> int:
    """Compare the latest benchmark run against the baseline; return the exit code."""
    bench, results_dir, baseline_path, threshold_pct = _parse_args(argv)

    current = _load_results(results_dir, bench)
    if not current:
        _fail(f"benchmark-gate: no result JSON in {results_dir} for '{bench}'")
        return 1

    if not baseline_path.is_file():
        _emit(f"benchmark-gate: no baseline at {baseline_path} — bootstrap mode (reporting only).")
        _emit("Copy the object below into the baseline file once the run is known-good:\n")
        _emit(json.dumps(current, indent=2, sort_keys=True))
        return 0

    baseline = cast("Baseline", json.loads(baseline_path.read_text(encoding="utf-8")))
    regressions = _compare(current, baseline, threshold_pct)
    if regressions:
        _fail("\nbenchmark-gate: FAIL — noticeable performance regression:")
        for line in regressions:
            _fail(f"  {line}")
        return 1
    _emit("\nbenchmark-gate: ok (no lane regressed beyond threshold)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
