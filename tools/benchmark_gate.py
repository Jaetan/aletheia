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

``--bench instructions`` checks the throughput lanes' cost: each lane's
instructions per operation, counted by ``tools/benchmark_instructions.py``
under valgrind, against the counts committed in
``benchmarks/instruction_counts.json``.  A lane more than
``MAX_INSTRUCTION_DRIFT_PERCENT`` above its count is a slowdown and fails; one
more than that below it fails too, since a count left above a speedup would
let a later slowdown through unseen, so a change that moves a lane past the
bound either way commits the counts its run measured, saying why.  A count
repeats far inside the bound from run to run and runner to runner, so the
runner's speed and load do not move the verdict; the frames per second the
throughput mode prints decide nothing.  Counts taken with another toolchain
or at other frame counts are not compared: the check names what differs, and
the counts are refreshed.  A lane or a binding either side lacks fails by
name.

The same check holds each lane to the bus it serves: a lane whose count is
over its budget in ``benchmarks/instruction_budgets.json``, the most
instructions per operation the runner class the record was calibrated on
executes at the bus's frames a second (``tools/benchmark_budgets.py``),
fails.  A noted limitation, a lane the record lists as under its bus when
calibrated, is reported over its budget without failing, and fails once within
it, since the record then says less than the lanes do.  Budgets calibrated
with another toolchain or at other frame counts fail naming what differs, a
missing record fails, and a lane either side lacks fails by name.  A run on a
class ranked slower than the record's, or on a class the ranking lacks, is
noted for a recalibration from it, without failing: the verdict is the
counts', whatever runner the run drew.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, TypedDict, cast

from tools.benchmark_budgets import BUDGETS_PATH, budget_of, class_rank
from tools.benchmark_instructions import RESULT_PATH, ToolName

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from tools.benchmark_budgets import BudgetRecord
    from tools.benchmark_instructions import (
        BindingName,
        FrameCount,
        InstructionCount,
        InstructionReport,
        LaneName,
        ToolVersion,
    )

# The bindings benchmarked by run_all.sh, the languages benchmarks/SCHEMA.yaml
# names. The scaling check fails a binding with no result file.
BINDINGS = ("cpp", "go", "python", "rust")

# A lane whose instructions per operation moved more than this percentage from
# its committed count, either way, fails.  Three runs of one tree on three
# runner classes, the GHC runtime's idle collector off, spread 20 lanes of 24 by
# under 0.1% and the widest, Go's CAN-FD signal extraction, by 1.76%.
MAX_INSTRUCTION_DRIFT_PERCENT = 5

# The counts the instruction check holds each lane to.
COUNTS_PATH = Path("benchmarks/instruction_counts.json")


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


_SLOWDOWN = Prose("more instructions than the bound allows: a slowdown")
_SPEEDUP = Prose(
    "fewer instructions than the bound allows: commit this run's counts, so a later"
    + " slowdown cannot pass in the gap"
)


def _drift(was: InstructionCount, now: InstructionCount) -> Prose | None:
    """Answer why ``now`` is more than the bound from ``was``, either way, or None."""
    if now * 100 > was * (100 + MAX_INSTRUCTION_DRIFT_PERCENT):
        return _SLOWDOWN
    if now * 100 < was * (100 - MAX_INSTRUCTION_DRIFT_PERCENT):
        return _SPEEDUP
    return None


def _unlike(
    toolchain: dict[ToolName, ToolVersion], frames: list[FrameCount], measured: InstructionReport
) -> list[Prose]:
    """Answer each tool, and the frame counts, a record and this run were taken with differently."""
    now = measured["toolchain"]
    unlike = [
        Prose(f"{tool}: committed {toolchain.get(tool)!r}, this run {now.get(tool)!r}")
        for tool in sorted(toolchain.keys() | now.keys())
        if toolchain.get(tool) != now.get(tool)
    ]
    if frames != measured["frames"]:
        unlike.append(Prose(f"frames: committed {frames}, this run {measured['frames']}"))
    return unlike


def _lane_failures(committed: InstructionReport, measured: InstructionReport) -> list[Prose]:
    """Print each lane's two counts, and answer each lane past the bound or on one side only."""
    failures: list[Prose] = []
    for binding in sorted(committed["counts"].keys() | measured["counts"].keys()):
        was_lanes = committed["counts"].get(binding, {})
        now_lanes = measured["counts"].get(binding, {})
        for lane in sorted(was_lanes.keys() | now_lanes.keys()):
            was, now = was_lanes.get(lane), now_lanes.get(lane)
            if was is None or now is None:
                side = "no committed count" if was is None else "no count in this run"
                failures.append(Prose(f"{binding} / {lane}: {side}"))
                continue
            reason = _drift(was, now)
            cells = f"{was:>11,} -> {now:>11,} ({100 * (now - was) / was:+6.2f}%)"
            flag = f"  <-- {reason}" if reason is not None else ""
            _emit(f"  {binding:7s} {lane:32s} {cells}{flag}")
            if reason is not None:
                failures.append(Prose(f"{binding} / {lane}: {was:,} -> {now:,}, {reason}"))
    return failures


_OVER_BUDGET = Prose(
    "over its budget: the lane no longer keeps up with its bus on the calibrating runner"
)
_NO_LONGER_LIMITED = Prose(
    "within its budget, so no longer a limitation: recalibrate, so the record gates it"
)


def _judged(
    binding: BindingName,
    lane: LaneName,
    now: InstructionCount,
    budget: InstructionCount,
    *,
    noted: bool,
) -> Prose | None:
    """Print a lane's count against its budget, and answer why the budgets refuse it, or None."""
    over = now > budget
    reason = None
    if noted and not over:
        reason = _NO_LONGER_LIMITED
    elif over and not noted:
        reason = _OVER_BUDGET
    note = "  (a noted limitation)" if noted else ""
    flag = f"  <-- {reason}" if reason is not None else note
    cells = f"{now:>11,} of {budget:>11,} ({100 * (budget - now) / budget:+6.2f}% left)"
    _emit(f"  {binding:7s} {lane:32s} {cells}{flag}")
    if reason is None:
        return None
    return Prose(f"{binding} / {lane}: {now:,} of a budget of {budget:,}, {reason}")


def _budget_failures(budgets: BudgetRecord, measured: InstructionReport) -> list[Prose]:
    """Print each lane's count against its budget, and answer each lane the budgets refuse."""
    failures: list[Prose] = []
    bindings = budgets["lanes"].keys() | budgets["limitations"].keys() | measured["counts"].keys()
    for binding in sorted(bindings):
        calibrated = budgets["lanes"].get(binding, {})
        counted = measured["counts"].get(binding, {})
        noted = set(budgets["limitations"].get(binding, []))
        failures.extend(
            Prose(f"{binding} / {lane}: a noted limitation with no budget")
            for lane in sorted(noted - calibrated.keys())
        )
        for lane in sorted(calibrated.keys() | counted.keys()):
            calibration, now = calibrated.get(lane), counted.get(lane)
            if calibration is None or now is None:
                side = "no budget" if calibration is None else "no count in this run"
                failures.append(Prose(f"{binding} / {lane}: {side}"))
                continue
            failure = _judged(binding, lane, now, budget_of(lane, calibration), noted=lane in noted)
            if failure is not None:
                failures.append(failure)
    return failures


def _read_records(
    measured_path: Path, counts_path: Path, budgets_path: Path
) -> tuple[InstructionReport, InstructionReport, BudgetRecord] | None:
    """Answer the run's report, the committed counts and the budgets, or None, naming the absent."""
    if not measured_path.is_file():
        _fail(f"benchmark-gate: no instruction report at {measured_path}")
        return None
    measured = cast("InstructionReport", json.loads(measured_path.read_text(encoding="utf-8")))
    if not counts_path.is_file():
        _fail(
            f"benchmark-gate: no committed counts at {counts_path}: commit this run's"
            + f" {measured_path.name} there once its counts are known-good"
        )
        return None
    if not budgets_path.is_file():
        _fail(
            f"benchmark-gate: no budgets at {budgets_path}: calibrate them with"
            + " tools/benchmark_budgets.py from a run on the slowest runner class drawn"
        )
        return None
    committed = cast("InstructionReport", json.loads(counts_path.read_text(encoding="utf-8")))
    budgets = cast("BudgetRecord", json.loads(budgets_path.read_text(encoding="utf-8")))
    return measured, committed, budgets


def runner_notice(budgets: BudgetRecord, measured: InstructionReport) -> Prose | None:
    """Answer the notice a run on a class ranked slower than the record's owes, or None.

    A class the ranking lacks may be slower than every class it holds, so a
    run on one is noted too.  The notice is GitHub's annotation, and fails
    nothing.
    """
    calibrated = budgets["host"].get(ToolName("cpu"))
    drawn = measured["host"].get(ToolName("cpu"))
    rank = class_rank(drawn)
    if rank is None:
        return Prose(
            f"::notice::benchmark-gate: this run drew {drawn!r}, a runner class"
            + " tools/benchmark_budgets.py's RUNNER_CLASSES does not rank: rank it, and"
            + " recalibrate the budgets from this run if it ranks slowest"
        )
    calibrated_rank = class_rank(calibrated)
    if calibrated_rank is not None and rank >= calibrated_rank:
        return None
    return Prose(
        f"::notice::benchmark-gate: this run drew the {drawn}, ranked slower than the"
        + f" {calibrated} the budgets were calibrated on: recalibrate them from this run's"
        + " artifact with python -m tools.benchmark_budgets"
    )


def _check_instructions(measured_path: Path, counts_path: Path, budgets_path: Path) -> ExitStatus:
    """Fail on a lane past the bound or over its budget, or on records that cannot be compared."""
    records = _read_records(measured_path, counts_path, budgets_path)
    if records is None:
        return ExitStatus(1)
    measured, committed, budgets = records
    notice = runner_notice(budgets, measured)
    if notice is not None:
        _emit(notice)
    unlike_counts = _unlike(committed["toolchain"], committed["frames"], measured)
    unlike_budgets = _unlike(budgets["toolchain"], budgets["frames"], measured)
    if unlike_counts:
        _fail("benchmark-gate: FAIL: the committed counts rest on another toolchain or frames:")
        for line in unlike_counts:
            _fail(f"  {line}")
        _fail(f"Refresh {counts_path} from this run's {measured_path.name}.")
    if unlike_budgets:
        _fail("benchmark-gate: FAIL: the budgets rest on another toolchain or frames:")
        for line in unlike_budgets:
            _fail(f"  {line}")
        _fail(
            f"Recalibrate {budgets_path} with tools/benchmark_budgets.py"
            + " from a run on the slowest runner class drawn."
        )
    if unlike_counts or unlike_budgets:
        return ExitStatus(1)
    _emit(
        "benchmark-gate: fail if any lane's instructions per operation moved more than"
        + f" {MAX_INSTRUCTION_DRIFT_PERCENT}% from its committed count, either way\n"
    )
    failures = _lane_failures(committed, measured)
    _emit(
        "\nbenchmark-gate: fail if any lane's instructions per operation are over its budget,"
        + " the most the calibrating runner executes at its bus's frames a second\n"
    )
    failures += _budget_failures(budgets, measured)
    if failures:
        _fail("\nbenchmark-gate: FAIL:")
        for line in failures:
            _fail(f"  {line}")
        return ExitStatus(1)
    _emit(
        "\nbenchmark-gate: ok (every lane within the bound of its committed count"
        + " and within its budget)"
    )
    return ExitStatus(0)


# The checks this gate runs.
type Check = Literal["scaling", "instructions"]


def _parse_args(argv: list[str] | None) -> tuple[Check, Path, Path, Path]:
    """Parse CLI args into (bench, results_dir, counts, budgets)."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--bench", choices=("scaling", "instructions"), required=True, help="The check to run."
    )
    _ = parser.add_argument(
        "--results-dir",
        type=Path,
        default=RESULT_PATH.parent,
        help="Directory of the run's result files (default: benchmarks/results).",
    )
    _ = parser.add_argument(
        "--counts",
        type=Path,
        default=COUNTS_PATH,
        help="Committed instruction counts (default: benchmarks/instruction_counts.json).",
    )
    _ = parser.add_argument(
        "--budgets",
        type=Path,
        default=BUDGETS_PATH,
        help="The lanes' budgets (default: benchmarks/instruction_budgets.json).",
    )
    args = parser.parse_args(argv)
    return (
        cast("Check", args.bench),
        cast("Path", args.results_dir),
        cast("Path", args.counts),
        cast("Path", args.budgets),
    )


def main(argv: list[str] | None = None) -> int:
    """Run the check ``--bench`` names; return the exit code."""
    bench, results_dir, counts_path, budgets_path = _parse_args(argv)
    if bench == "scaling":
        return _check_scaling(results_dir, MAX_ALLOCATION_DOUBLING)
    return _check_instructions(results_dir / RESULT_PATH.name, counts_path, budgets_path)


if __name__ == "__main__":
    sys.exit(main())
