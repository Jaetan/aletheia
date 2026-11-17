# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Calibrate the throughput lanes' instruction budgets from a run on GitHub's slowest runner.

A lane keeps up with a saturated bus when it handles as many frames a second
as the bus carries.  One run on a slow runner class measures each lane's
instructions per operation, counted under valgrind by
``tools/benchmark_instructions.py``, and its worst run's frames a second, in the
binding's throughput result file: their product is the rate that runner
executes the lane's instructions at, and that rate over the bus's frames a
second is the most instructions per operation the lane can take there and keep
up, its budget.  ``tools/benchmark_gate.py --bench instructions`` fails a lane
whose count is over its budget.

This tool writes the record the gate reads, ``benchmarks/instruction_budgets.json``,
from the run, of the result directories it is given, whose runner class ranks
slowest in ``RUNNER_CLASSES``, and refuses a run of a class the ranking does
not hold, which may be slower than every class it does.  A lane of the noted
limitation already under its bus at calibration is written as a limitation,
which the gate reports without failing while it stays over its budget; any
other lane under its bus refuses the calibration.  The record is recalibrated
when a toolchain moves, the gate naming the tool that differs, and when a run
lands on a class ranked slower than the record's, which the gate notes.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NewType, TypedDict, cast

from tools.benchmark_instructions import (
    RESULT_PATH,
    BindingName,
    CommandWord,
    FrameCount,
    InstructionCount,
    LaneName,
    ToolName,
    ToolVersion,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Sequence

    from tools.benchmark_instructions import InstructionReport

# A bus as a lane's name begins with it, and a rate in frames a second.
BusName = NewType("BusName", str)
FramesPerSecond = NewType("FramesPerSecond", float)

# A saturated bus's frames a second at the lanes' frame shapes, with no stuff
# bits: a CAN 2.0B standard frame of 8 bytes is 111 bits at 1 Mbit/s, and a
# CAN-FD standard frame of 64 bytes is 30 bits at the 1 Mbit/s arbitration
# rate and 549 at the 8 Mbit/s data rate, 98.625 microseconds.
BUS_FRAMES_PER_SECOND: dict[BusName, FramesPerSecond] = {
    BusName("CAN 2.0B"): FramesPerSecond(9009),
    BusName("CAN-FD"): FramesPerSecond(10139),
}

# GitHub's standard Linux runner classes, as the host line of an instruction
# report names their CPU, slowest first: ranked by Python's CAN-FD signal
# extraction, the lane nearest its bus, whose worst run's frames a second over
# two samplings of eight jobs read 7,757 on the 7763, 8,949 on the 8370C, 9,590
# on the 8573C, 10,881 on the 6973P-C, 12,057 on the 9V74, 12,342 on the
# 6975P-C and 15,970 on the 9V45.  A class GitHub draws that this lacks is
# placed in it by that rate, which the refusal of its run names, before the
# budgets are recalibrated.
RUNNER_CLASSES: tuple[ToolVersion, ...] = (
    ToolVersion("AMD EPYC 7763 64-Core Processor"),
    ToolVersion("Intel(R) Xeon(R) Platinum 8370C CPU @ 2.80GHz"),
    ToolVersion("INTEL(R) XEON(R) PLATINUM 8573C"),
    ToolVersion("Intel(R) Xeon(R) 6973P-C"),
    ToolVersion("AMD EPYC 9V74 80-Core Processor"),
    ToolVersion("Intel(R) Xeon(R) 6975P-C"),
    ToolVersion("AMD EPYC 9V45 96-Core Processor"),
)

# The lane the classes are ranked by, and its binding.
RANKING_BINDING = BindingName("python")
RANKING_LANE = LaneName("CAN-FD:   Signal Extraction")

# A runner class's place in ``RUNNER_CLASSES``, the slowest at 0.
ClassRank = NewType("ClassRank", int)

# The record the gate holds each lane to.
BUDGETS_PATH = Path("benchmarks/instruction_budgets.json")

# The lanes that may stay under their bus on a slow runner, the noted
# limitation: Python's two CAN-FD lanes that read or write a frame's 64 bytes.
# A calibrating run with any other lane under its bus is refused.
NOTED_LIMITATIONS: dict[BindingName, frozenset[LaneName]] = {
    BindingName("python"): frozenset(
        {LaneName("CAN-FD:   Frame Building"), LaneName("CAN-FD:   Signal Extraction")}
    ),
}


class LaneCalibration(TypedDict):
    """One lane's count and worst run's frames a second, from the calibrating run."""

    instructions: InstructionCount
    fps_min: FramesPerSecond


class BudgetRecord(TypedDict):
    """The calibrating run's host, toolchain, frame counts, lanes and limitations."""

    host: dict[ToolName, ToolVersion]
    toolchain: dict[ToolName, ToolVersion]
    frames: list[FrameCount]
    lanes: dict[BindingName, dict[LaneName, LaneCalibration]]
    limitations: dict[BindingName, list[LaneName]]


class _ThroughputRow(TypedDict):
    name: LaneName
    fps_min: FramesPerSecond


class _ThroughputFile(TypedDict):
    results: list[_ThroughputRow]


class CalibrationError(Exception):
    """A result directory no budget can be calibrated from, with the reason."""


def bus_of(lane: LaneName) -> FramesPerSecond:
    """Answer the frames a second of the bus a lane's name begins with."""
    bus = BusName(lane.split(":", 1)[0])
    if bus not in BUS_FRAMES_PER_SECOND:
        raise CalibrationError(
            Prose(f"lane {lane!r} names no bus of {sorted(BUS_FRAMES_PER_SECOND)}")
        )
    return BUS_FRAMES_PER_SECOND[bus]


def budget_of(lane: LaneName, calibration: LaneCalibration) -> InstructionCount:
    """Answer the most instructions per operation the lane takes and keeps up with its bus."""
    rate = calibration["instructions"] * calibration["fps_min"]
    return InstructionCount(math.floor(rate / bus_of(lane)))


def _throughput(results_dir: Path, binding: BindingName) -> dict[LaneName, FramesPerSecond]:
    """Answer each lane's worst run's frames a second in a binding's throughput result file."""
    path = results_dir / f"{binding}_throughput.json"
    if not path.is_file():
        raise CalibrationError(Prose(f"no throughput result file at {path}"))
    rows = cast("_ThroughputFile", json.loads(path.read_text(encoding="utf-8")))["results"]
    return {row["name"]: row["fps_min"] for row in rows}


def _report(results_dir: Path) -> InstructionReport:
    """Answer a run's instruction report, or raise naming where it is missing."""
    report_path = results_dir / RESULT_PATH.name
    if not report_path.is_file():
        raise CalibrationError(Prose(f"no instruction report at {report_path}"))
    return cast("InstructionReport", json.loads(report_path.read_text(encoding="utf-8")))


def class_rank(cpu: ToolVersion | None) -> ClassRank | None:
    """Answer a CPU's place in ``RUNNER_CLASSES``, slowest at 0, or None for a class it lacks."""
    return ClassRank(RUNNER_CLASSES.index(cpu)) if cpu in RUNNER_CLASSES else None


def _ranking_rate(results_dir: Path) -> Prose:
    """Say how fast a run's ranking lane ran at worst, the rate its class is ranked by."""
    path = results_dir / f"{RANKING_BINDING}_throughput.json"
    rows = (
        cast("_ThroughputFile", json.loads(path.read_text(encoding="utf-8")))["results"]
        if path.is_file()
        else []
    )
    rates = [row["fps_min"] for row in rows if row["name"] == RANKING_LANE]
    if not rates:
        return Prose(f"and ran no {RANKING_BINDING} {RANKING_LANE!r} lane to rank it by")
    return Prose(
        f"its {RANKING_BINDING} {RANKING_LANE!r} lane's worst run at {rates[0]:,} frames a second"
    )


def slowest_run(results_dirs: Sequence[Path]) -> Path:
    """Answer the run of the slowest ranked class among ``results_dirs``, the first on a tie.

    Raises ``CalibrationError`` on no run at all, and on a run of a class the
    ranking lacks, which may be slower than every class it holds.
    """
    ranked: list[tuple[ClassRank, Path]] = []
    for results_dir in results_dirs:
        cpu = _report(results_dir)["host"].get(ToolName("cpu"))
        rank = class_rank(cpu)
        if rank is None:
            raise CalibrationError(
                Prose(
                    f"{results_dir} ran on {cpu!r}, a runner class RUNNER_CLASSES does not rank,"
                    + f" {_ranking_rate(results_dir)}: rank it by that among the classes first,"
                    + " since it may be the slowest"
                )
            )
        ranked.append((rank, results_dir))
    if not ranked:
        raise CalibrationError(Prose("no run to calibrate from"))
    return min(ranked, key=lambda run: run[0])[1]


def calibrate(results_dir: Path) -> BudgetRecord:
    """Answer the budget record one run's result directory calibrates, or raise why it cannot."""
    report = _report(results_dir)
    cpu = report["host"].get(ToolName("cpu"))
    if class_rank(cpu) is None:
        raise CalibrationError(Prose(f"the run's CPU {cpu!r} is no class RUNNER_CLASSES ranks"))
    lanes: dict[BindingName, dict[LaneName, LaneCalibration]] = {}
    limitations: dict[BindingName, list[LaneName]] = {}
    for binding, counts in sorted(report["counts"].items()):
        fps = _throughput(results_dir, binding)
        if fps.keys() != counts.keys():
            unmatched = sorted(fps.keys() ^ counts.keys())
            raise CalibrationError(Prose(f"{binding}: lanes on one side only: {unmatched}"))
        lanes[binding] = {
            lane: {"instructions": counts[lane], "fps_min": fps[lane]} for lane in sorted(counts)
        }
        under = [lane for lane in sorted(counts) if fps[lane] < bus_of(lane)]
        unnoted = [
            lane for lane in under if lane not in NOTED_LIMITATIONS.get(binding, frozenset())
        ]
        if unnoted:
            raise CalibrationError(
                Prose(f"{binding}: under its bus and not a noted limitation: {unnoted}")
            )
        if under:
            limitations[binding] = under
    return {
        "host": report["host"],
        "toolchain": report["toolchain"],
        "frames": report["frames"],
        "lanes": lanes,
        "limitations": limitations,
    }


def main(argv: list[CommandWord] | None = None) -> ExitStatus:
    """Write the budget record a run's result directory calibrates; answer the exit code."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--results-dir",
        type=Path,
        action="append",
        help="A run's result directory, given once per run; the slowest class's run"
        + " calibrates the record (default: benchmarks/results).",
    )
    _ = parser.add_argument(
        "--out", type=Path, default=BUDGETS_PATH, help="The record written (default: %(default)s)."
    )
    args = parser.parse_args(argv)
    given = cast("list[Path] | None", args.results_dir) or [RESULT_PATH.parent]
    try:
        chosen = slowest_run(given)
        record = calibrate(chosen)
    except CalibrationError as refusal:
        _ = sys.stderr.write(f"benchmark-budgets: {refusal}\n")
        return ExitStatus(1)
    out = cast("Path", args.out)
    _ = out.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    for binding, lanes in record["limitations"].items():
        for lane in lanes:
            _ = sys.stdout.write(
                f"benchmark-budgets: {binding} / {lane} is under its bus: a limitation\n"
            )
    cpu = record["host"].get(ToolName("cpu"))
    _ = sys.stdout.write(f"benchmark-budgets: wrote {out} from {chosen}, a run on the {cpu}\n")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())
