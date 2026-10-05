# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Regression gates for the cross-language benchmark.

``--bench scaling`` checks the ``dbc_size`` sweep instead: in every binding,
doubling a DBC's messages must not multiply its load time by more than
``MAX_DOUBLING``.  A linear load doubles its time; a load quadratic in its
messages quadruples it.  Every binding must have reported, since this check
is required: a missing result fails it.

Otherwise, the throughput gate:

Compares the per-lane mean throughput in ``benchmarks/results/*_<bench>.json``
(produced by ``benchmarks/run_all.sh``) against a committed GitHub-runner
baseline (``benchmarks/gha_baseline.json``) and exits non-zero if any lane is
slower than its baseline by more than ``--threshold-pct``, or if a binding whose
result file is present lacks a lane the baseline names.

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
import itertools
import json
import sys
from pathlib import Path
from typing import NewType, TypedDict, cast

from aletheia.common_types import ExitStatus, Prose

# The four bindings benchmarked by run_all.sh, the languages benchmarks/SCHEMA.yaml
# names. A binding absent from a run (one that failed to build) is skipped, not
# scored as a 100% regression: build failures are pr-full-ci's job to report. A
# binding that is present and reports fewer lanes than the baseline names fails.
BINDINGS = ("cpp", "go", "python", "rust")

# Baseline JSON shape: {binding: {lane_name: fps_mean}}.
Baseline = dict[str, dict[str, float]]


class _Row(TypedDict):
    """One lane in a per-binding result file."""

    name: str
    fps_mean: float


class _ResultFile(TypedDict):
    """Shape of ``benchmarks/results/<binding>_<bench>.json`` (fields we read)."""

    results: list[_Row]


# A number of DBC messages, a load time, and how many times one time is another.
MessageCount = NewType("MessageCount", int)
Seconds = NewType("Seconds", float)
GrowthFactor = NewType("GrowthFactor", float)

# A linear load doubles its time when its messages double, and a quadratic one
# quadruples it; this sits between.  Measured on one machine, best of five
# loads per point, over the quick sweep's two doublings (2,500 to 10,000
# messages): the four bindings grew x4.07 to x4.39, a validator comparing every
# pair of messages x21.5, against the x9 this allows.
MAX_DOUBLING = GrowthFactor(3.0)


class _DbcSizeRow(TypedDict):
    """One point of the ``dbc_size`` scaling sweep (fields we read)."""

    messages: MessageCount
    seconds: Seconds


class _ScalingResults(TypedDict):
    """The scaling sweeps of a result file (the one this gate reads)."""

    dbc_size: list[_DbcSizeRow]


class _ScalingFile(TypedDict):
    """Shape of ``benchmarks/results/<binding>_scaling.json`` (fields we read)."""

    results: _ScalingResults


def _check_dbc_size(results_dir: Path, max_doubling: GrowthFactor) -> ExitStatus:
    """Fail when a binding is missing or its load time outgrows the doublings of its messages.

    Each step of the sweep doubles the messages.  The check is on the whole
    sweep, the last time over the first against ``max_doubling`` to the power
    of the doublings: a single step's ratio carries one step's noise, and the
    wider the range the further a quadratic load's growth sits from a linear one.
    """
    _emit(
        "benchmark-gate: each doubling of a DBC's messages may multiply its load time"
        + f" by at most {max_doubling}, over the whole sweep\n"
    )
    failures: list[Prose] = []
    for binding in BINDINGS:
        path = results_dir / f"{binding}_scaling.json"
        if not path.is_file():
            failures.append(Prose(f"{binding}: no {path.name}"))
            continue
        data = cast("_ScalingFile", json.loads(path.read_text(encoding="utf-8")))
        rows = data["results"].get("dbc_size", [])
        if len(rows) < len(("small", "large")):
            failures.append(
                Prose(f"{binding}: dbc_size has {len(rows)} point(s), a doubling needs two")
            )
            continue
        steps = list(itertools.pairwise(rows))
        if any(large["messages"] != 2 * small["messages"] for small, large in steps):
            failures.append(Prose(f"{binding}: the dbc_size points do not double"))
            continue
        for small, large in steps:
            _emit(
                f"  {binding:7s} {small['messages']:>6} -> {large['messages']:>6} messages:"
                + f" {small['seconds']:.4f} s -> {large['seconds']:.4f} s"
                + f" (x{large['seconds'] / small['seconds']:.2f})"
            )
        growth = rows[-1]["seconds"] / rows[0]["seconds"]
        allowed = max_doubling ** len(steps)
        flag = "  <-- SUPERLINEAR" if growth > allowed else ""
        _emit(
            f"  {binding:7s} {rows[0]['messages']:>6} -> {rows[-1]['messages']:>6} messages:"
            + f" x{growth:.2f} (at most x{allowed:.2f}){flag}"
        )
        if growth > allowed:
            failures.append(
                Prose(
                    f"{binding}: {rows[0]['messages']} -> {rows[-1]['messages']} messages took"
                    + f" {growth:.2f} times as long (at most {allowed:.2f})"
                )
            )
    if failures:
        _fail("\nbenchmark-gate: FAIL:")
        for line in failures:
            _fail(f"  {line}")
        return ExitStatus(1)
    _emit("\nbenchmark-gate: ok (no binding's load time outgrew its messages past the factor)")
    return ExitStatus(0)


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


def _compare(
    current: Baseline, baseline: Baseline, threshold_pct: float
) -> tuple[list[str], list[str]]:
    """Print a per-lane table; return (lanes past the threshold, lanes a present binding lacks)."""
    regressions: list[str] = []
    missing: list[str] = []
    _emit(f"benchmark-gate: fail if any lane is >{threshold_pct:.0f}% slower than baseline\n")
    for binding in BINDINGS:
        if binding not in current:
            continue
        cur = current[binding]
        for lane, base_fps in baseline.get(binding, {}).items():
            cur_fps = cur.get(lane)
            if cur_fps is None:
                _emit(f"  {binding:7s} {lane:32s} {base_fps:>11.0f} -> (absent)  <-- MISSING")
                missing.append(f"{binding} / {lane}: {base_fps:.0f} -> absent from the run")
                continue
            if base_fps <= 0.0:
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
    return regressions, missing


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
    if bench == "scaling":
        return _check_dbc_size(results_dir, MAX_DOUBLING)

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
    regressions, missing = _compare(current, baseline, threshold_pct)
    if missing:
        _fail("\nbenchmark-gate: FAIL: a binding that ran reports no number for a baseline lane:")
        for line in missing:
            _fail(f"  {line}")
    if regressions:
        _fail("\nbenchmark-gate: FAIL: noticeable performance regression:")
        for line in regressions:
            _fail(f"  {line}")
    if missing or regressions:
        return 1
    _emit("\nbenchmark-gate: ok (no lane regressed beyond threshold)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
