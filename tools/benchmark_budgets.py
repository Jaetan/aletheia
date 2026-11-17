# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Calibrate the throughput lanes' instruction budgets from one run on GitHub's slower runner.

A lane keeps up with a saturated bus when it handles as many frames a second
as the bus carries.  One run on the slower runner class measures each lane's
instructions per operation, counted under valgrind by
``tools/benchmark_instructions.py``, and its worst run's frames a second, in the
binding's throughput result file: their product is the rate that runner
executes the lane's instructions at, and that rate over the bus's frames a
second is the most instructions per operation the lane can take there and keep
up, its budget.  ``tools/benchmark_gate.py --bench instructions`` fails a lane
whose count is over its budget.

This tool writes the record the gate reads, ``benchmarks/instruction_budgets.json``,
from one run's result directory, and refuses a run from another runner class.
A lane of the noted limitation already under its bus at calibration is
written as a limitation, which the gate reports without failing while it stays
over its budget; any other lane under its bus refuses the calibration.  The record is
recalibrated when the runner class or a toolchain moves, the gate naming the
tool that differs.
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

# GitHub's standard Linux runner class on which the lanes run slowest of the
# classes measured (the others an Intel Xeon 6975P-C and an AMD EPYC 9V74), as
# the host line of an instruction report names its CPU.
SLOWER_RUNNER_CPU = ToolVersion("AMD EPYC 7763 64-Core Processor")

# The record the gate holds each lane to.
BUDGETS_PATH = Path("benchmarks/instruction_budgets.json")

# The lanes that may stay under their bus on the slower runner, the noted
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


def calibrate(results_dir: Path) -> BudgetRecord:
    """Answer the budget record one run's result directory calibrates, or raise why it cannot."""
    report_path = results_dir / RESULT_PATH.name
    if not report_path.is_file():
        raise CalibrationError(Prose(f"no instruction report at {report_path}"))
    report = cast("InstructionReport", json.loads(report_path.read_text(encoding="utf-8")))
    cpu = report["host"].get(ToolName("cpu"))
    if cpu != SLOWER_RUNNER_CPU:
        raise CalibrationError(
            Prose(f"the run's CPU is {cpu!r}, not the slower runner's {SLOWER_RUNNER_CPU!r}")
        )
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
        default=RESULT_PATH.parent,
        help="The calibrating run's result directory (default: benchmarks/results).",
    )
    _ = parser.add_argument(
        "--out", type=Path, default=BUDGETS_PATH, help="The record written (default: %(default)s)."
    )
    args = parser.parse_args(argv)
    try:
        record = calibrate(cast("Path", args.results_dir))
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
    _ = sys.stdout.write(f"benchmark-budgets: wrote {out}\n")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())
