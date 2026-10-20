# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Regression gates for the cross-language benchmark.

``--bench scaling`` checks the load sweeps instead, ``dbc_size`` sized by its
messages, and ``text_literal_length`` and ``json_literal_length`` by the digits
of a DBC's one long number, loaded from DBC text and from a ``parseDBC``
command: in every binding, each doubling of a sweep's size may multiply the
bytes the kernel allocates for one load by at most ``MAX_ALLOCATION_DOUBLING``,
over the whole sweep.  Allocation is counted rather than timed, and the count
repeats to within a few kilobytes from run to run, so the runner's load does
not move the verdict; the load times are printed beside it and decide nothing.
The measurements the factor rests on are in the comment on
``MAX_ALLOCATION_DOUBLING``.  Every binding must have reported every load
sweep, since this check is required: a binding with no result file, or one
missing a sweep, fails it.

Otherwise, the throughput gate:

Compares the per-lane mean throughput in ``benchmarks/results/*_<bench>.json``
(produced by ``benchmarks/run_all.sh``) against a committed GitHub-runner
baseline (``benchmarks/gha_baseline.json``) and exits non-zero if any lane is
slower than its baseline by more than ``--threshold-pct``, or if a binding whose
result file is present lacks a lane the baseline names.

The gate runs on the GitHub-hosted runner, which is shared, variable, and a
different machine than the local benchmark host, so the baseline MUST itself be
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
from typing import Literal, NamedTuple, NewType, TypedDict, cast

from aletheia.common_types import ExitStatus, Prose

# The bindings benchmarked by run_all.sh, the languages benchmarks/SCHEMA.yaml
# names. The throughput gate skips a binding absent from a run (one that failed
# to build) rather than scoring it as a 100% regression, build failures being
# pr-full-ci's job to report, and fails one that is present and reports fewer
# lanes than the baseline names. The scaling check fails a binding with no
# result file.
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


# A point's size (the messages of a ``dbc_size`` DBC, or the digits of the one
# long number in a literal sweep's DBC), a load time, the bytes the kernel
# allocated for one load, and how many times one number is another.
PointSize = NewType("PointSize", int)
Seconds = NewType("Seconds", float)
ByteCount = NewType("ByteCount", int)
GrowthFactor = NewType("GrowthFactor", float)

# A load sweep's key in a scaling result file's ``results``, and the column of
# its rows that holds a point's size.
type SweepKey = Literal["dbc_size", "text_literal_length", "json_literal_length"]
type SizeColumn = Literal["messages", "digits"]


class Sweep(NamedTuple):
    """A load sweep the scaling check reads: its key and the column its sizes are in."""

    key: SweepKey
    size: SizeColumn


# The load sweeps, in the order benchmarks/SCHEMA.yaml lists them.
SWEEPS = (
    Sweep("dbc_size", "messages"),
    Sweep("text_literal_length", "digits"),
    Sweep("json_literal_length", "digits"),
)

# The width of the sweep column the check prints, its longest key's.
_KEY_WIDTH = max(len(sweep.key) for sweep in SWEEPS)

# A load linear in its size doubles its allocation when the size doubles, one
# quadratic in it quadruples it, and one allocating n log n grows x2.18 per
# doubling at 2,500 messages; this sits above n log n and below the defects
# measured.  Measured with the kernel's allocation count, which repeats to
# within a few kilobytes from run to run: dbc_size x2.04 to x2.07 per doubling,
# x4.20 to x4.21 over the quick sweep's two doublings, against the x5.06 this
# allows over two; text_literal_length x1.99 to x2.00 per doubling, x3.98 over
# the quick sweep; json_literal_length x3.92 over the quick sweep; a JSON array
# parser appending each element at the end x6.93 to x7.01 over the quick
# message sweep; a literal parser folding each digit into one growing number
# x15.00 over the quick text digit sweep and x15.10 over the quick JSON one.
MAX_ALLOCATION_DOUBLING = GrowthFactor(2.25)


class _SweepRow(TypedDict, total=False):
    """One point of a load sweep (fields we read): its size is under the sweep's column."""

    messages: PointSize
    digits: PointSize
    seconds: Seconds
    allocated_bytes: ByteCount


class _ScalingResults(TypedDict, total=False):
    """The load sweeps of a scaling result file (the ones this gate reads)."""

    dbc_size: list[_SweepRow]
    text_literal_length: list[_SweepRow]
    json_literal_length: list[_SweepRow]


class _ScalingFile(TypedDict):
    """Shape of ``benchmarks/results/<binding>_scaling.json`` (fields we read)."""

    results: _ScalingResults


class _Point(NamedTuple):
    """One point of a load sweep, read: its size, its load time if reported, its allocation."""

    size: PointSize
    seconds: Seconds | None
    allocated: ByteCount


class _Verdict(NamedTuple):
    """One sweep of one result file, judged: the lines to print, and why it fails if it does."""

    lines: list[Prose]
    failure: Prose | None


def _times(before: Seconds | ByteCount | None, after: Seconds | ByteCount | None) -> Prose:
    """Return ``after`` over ``before``, n/a when either is unread or ``before`` is not positive."""
    if before is None or after is None or before <= 0:
        return Prose("x n/a")
    return Prose(f"x{after / before:.2f}")


def _seconds(value: Seconds | None) -> Prose:
    """Return a load time as the check prints it."""
    return Prose("n/a s") if value is None else Prose(f"{value:.4f} s")


def _points(sweep: Sweep, rows: list[_SweepRow] | None) -> list[_Point] | Prose:
    """Read a sweep's points, or the reason they cannot be judged.

    A sweep is judged on two points at least, sizes that double from one to
    the next, and an allocation each point reports as a positive count.
    """
    if rows is None:
        return Prose(f"no {sweep.key} sweep")
    if len(rows) < len(("small", "large")):
        return Prose(f"{sweep.key} has {len(rows)} point(s), a doubling needs two")
    sizes = [size for row in rows if (size := row.get(sweep.size)) is not None]
    if len(sizes) < len(rows) or any(
        large != 2 * small for small, large in itertools.pairwise(sizes)
    ):
        return Prose(f"the {sweep.key} points do not double their {sweep.size}")
    points: list[_Point] = []
    for size, row in zip(sizes, rows, strict=True):
        allocated = row.get("allocated_bytes")
        where = f"{sweep.key} at {size} {sweep.size}"
        if allocated is None:
            return Prose(f"{where} reports no allocated_bytes")
        if allocated <= 0:
            return Prose(f"{where} reports allocated_bytes {allocated}, not a positive count")
        points.append(_Point(size, row.get("seconds"), allocated))
    return points


def _judge(sweep: Sweep, rows: list[_SweepRow] | None, max_doubling: GrowthFactor) -> _Verdict:
    """Judge one load sweep of one result file against ``max_doubling``.

    Each step of the sweep doubles the size.  The check is on the whole sweep,
    the last point's allocation over the first's against ``max_doubling`` to
    the power of the doublings: the wider the range, the further a superlinear
    load's growth sits from a linear one.  Each step's load times and
    allocations are printed with their ratios, and the whole sweep's time
    ratio beside its allocation's; the times decide nothing.
    """
    points = _points(sweep, rows)
    if not isinstance(points, list):
        return _Verdict([], points)
    steps = list(itertools.pairwise(points))
    lines = [
        Prose(
            f"{sweep.key:{_KEY_WIDTH}s} {small.size:>6} -> {large.size:>6} {sweep.size}:"
            + f" {_seconds(small.seconds)} -> {_seconds(large.seconds)}"
            + f" ({_times(small.seconds, large.seconds)}),"
            + f" {small.allocated:,} -> {large.allocated:,} bytes"
            + f" ({_times(small.allocated, large.allocated)})"
        )
        for small, large in steps
    ]
    first, last = points[0], points[-1]
    growth = GrowthFactor(last.allocated / first.allocated)
    allowed = GrowthFactor(max_doubling ** len(steps))
    flag = "  <-- SUPERLINEAR" if growth > allowed else ""
    lines.append(
        Prose(
            f"{sweep.key:{_KEY_WIDTH}s} {first.size:>6} -> {last.size:>6} {sweep.size}:"
            + f" seconds {_times(first.seconds, last.seconds)},"
            + f" allocated bytes x{growth:.2f} (at most x{allowed:.2f}){flag}"
        )
    )
    if growth > allowed:
        reason = Prose(
            f"{sweep.key}: {first.size} -> {last.size} {sweep.size} allocated"
            + f" {growth:.2f} times the bytes (at most {allowed:.2f})"
        )
        return _Verdict(lines, reason)
    return _Verdict(lines, None)


def _check_scaling(results_dir: Path, max_doubling: GrowthFactor) -> ExitStatus:
    """Fail when a binding is missing a load sweep, or a load's allocation outgrows its size."""
    _emit(
        "benchmark-gate: each doubling of a load sweep's size may multiply the bytes one load"
        + f" allocates by at most {max_doubling}, over the whole sweep; the load times are"
        + " printed and decide nothing\n"
    )
    failures: list[Prose] = []
    for binding in BINDINGS:
        path = results_dir / f"{binding}_scaling.json"
        if not path.is_file():
            failures.append(Prose(f"{binding}: no {path.name}"))
            continue
        data = cast("_ScalingFile", json.loads(path.read_text(encoding="utf-8")))
        for sweep in SWEEPS:
            verdict = _judge(sweep, data["results"].get(sweep.key), max_doubling)
            for line in verdict.lines:
                _emit(f"  {binding:7s} {line}")
            if verdict.failure is not None:
                failures.append(Prose(f"{binding}: {verdict.failure}"))
    if failures:
        _fail("\nbenchmark-gate: FAIL:")
        for line in failures:
            _fail(f"  {line}")
        return ExitStatus(1)
    _emit("\nbenchmark-gate: ok (no binding's load allocation outgrew its size past the factor)")
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
        return _check_scaling(results_dir, MAX_ALLOCATION_DOUBLING)

    current = _load_results(results_dir, bench)
    if not current:
        _fail(f"benchmark-gate: no result JSON in {results_dir} for '{bench}'")
        return 1

    if not baseline_path.is_file():
        _emit(f"benchmark-gate: no baseline at {baseline_path}: bootstrap mode (reporting only).")
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
