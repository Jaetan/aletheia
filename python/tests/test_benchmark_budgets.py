# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.benchmark_budgets``: the lanes' instruction budgets, calibrated from one run.

The bus rates are a saturated bus's frames a second at the lanes' frame
shapes, derived from their bit counts. A run on the slower runner calibrates
every lane, its count and its worst run's frames a second, with the run's
host, toolchain and frame counts; a noted lane under its bus is written as a
limitation and a lane at its bus is not. A lane's budget is its calibrated
rate over its bus's frames a second. A run on another runner class, a binding
without a throughput result file, lanes only one side holds, a lane under its
bus that is no noted limitation and a lane naming no bus are refused, and
``main`` writes the record or exits 1 naming why not.
"""

from __future__ import annotations

import json
import math
from typing import TYPE_CHECKING

import pytest

from tools.benchmark_budgets import (
    BUS_FRAMES_PER_SECOND,
    SLOWER_RUNNER_CPU,
    BudgetRecord,
    BusName,
    CalibrationError,
    FramesPerSecond,
    LaneCalibration,
    budget_of,
    calibrate,
    main,
)
from tools.benchmark_instructions import (
    BindingName,
    CommandWord,
    FrameCount,
    InstructionCount,
    InstructionReport,
    LaneName,
    ToolName,
    ToolVersion,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_CPP, _PYTHON = BindingName("cpp"), BindingName("python")
_CLASSIC = LaneName("CAN 2.0B: Frame Building")
_FD = LaneName("CAN-FD:   Signal Extraction")
_TOOLCHAIN = {ToolName("python"): ToolVersion("3.14.10")}
_FRAMES = [FrameCount(100), FrameCount(1100)]

# Each binding's lanes and a number per lane: a count or a worst run's rate.
type _Counts = dict[BindingName, dict[LaneName, InstructionCount]]
type _Rates = dict[BindingName, dict[LaneName, FramesPerSecond]]


def _write_run(
    tmp_path: Path, counts: _Counts, rates: _Rates, cpu: ToolVersion = SLOWER_RUNNER_CPU
) -> Path:
    """Write a run's instruction report and each rated binding's throughput result file."""
    results = tmp_path / "results"
    results.mkdir()
    report: InstructionReport = {
        "toolchain": dict(_TOOLCHAIN),
        "host": {ToolName("cpu"): cpu},
        "frames": list(_FRAMES),
        "counts": counts,
    }
    _ = (results / "instructions.json").write_text(json.dumps(report), encoding="utf-8")
    for binding, lanes in rates.items():
        rows = [{"name": lane, "fps_min": fps, "fps_mean": fps * 2} for lane, fps in lanes.items()]
        _ = (results / f"{binding}_throughput.json").write_text(
            json.dumps({"results": rows}), encoding="utf-8"
        )
    return results


def test_the_bus_rates_are_a_saturated_bus_s_frames_a_second() -> None:
    """CAN 2.0B carries one 111-bit frame each 111 microseconds; CAN-FD one in 30 + 549/8."""
    assert BUS_FRAMES_PER_SECOND[BusName("CAN 2.0B")] == math.floor(1_000_000 / 111)
    assert BUS_FRAMES_PER_SECOND[BusName("CAN-FD")] == math.floor(1_000_000 / (30 + 549 / 8))


def test_a_run_on_the_slower_runner_calibrates_every_lane(tmp_path: Path) -> None:
    """Every lane's count and worst rate are recorded, with the run's host, toolchain and frames."""
    counts = {
        _CPP: {_CLASSIC: InstructionCount(100_000), _FD: InstructionCount(800_000)},
        _PYTHON: {_FD: InstructionCount(1_000_000)},
    }
    rates = {
        _CPP: {_CLASSIC: FramesPerSecond(9009), _FD: FramesPerSecond(11_625.5)},
        _PYTHON: {_FD: FramesPerSecond(10_138.9)},
    }
    record = calibrate(_write_run(tmp_path, counts, rates))
    assert record["host"] == {ToolName("cpu"): SLOWER_RUNNER_CPU}
    assert record["toolchain"] == _TOOLCHAIN
    assert record["frames"] == _FRAMES
    assert record["lanes"] == {
        _CPP: {
            _CLASSIC: {"instructions": 100_000, "fps_min": 9009},
            _FD: {"instructions": 800_000, "fps_min": 11_625.5},
        },
        _PYTHON: {_FD: {"instructions": 1_000_000, "fps_min": 10_138.9}},
    }
    assert record["limitations"] == {_PYTHON: [_FD]}


@pytest.mark.parametrize(
    ("lane", "fps", "budget"),
    [
        (_CLASSIC, 18_018, 200_000),
        (_CLASSIC, 9009, 100_000),
        (_FD, 10_139, 100_000),
        (_FD, 5069.5, 50_000),
    ],
)
def test_a_budget_is_the_calibrated_rate_over_the_bus(
    lane: LaneName, fps: FramesPerSecond, budget: InstructionCount
) -> None:
    """A lane of 100,000 instructions run at twice, once or half its bus is budgeted as much."""
    calibration: LaneCalibration = {"instructions": InstructionCount(100_000), "fps_min": fps}
    assert budget_of(lane, calibration) == budget


@pytest.mark.parametrize(
    ("cpu", "counts", "rates", "reason"),
    [
        (
            ToolVersion("Intel(R) Xeon(R) 6975P-C"),
            {_CPP: {_CLASSIC: InstructionCount(1)}},
            {_CPP: {_CLASSIC: FramesPerSecond(1)}},
            Prose("not the slower runner's"),
        ),
        (
            SLOWER_RUNNER_CPU,
            {_CPP: {_CLASSIC: InstructionCount(1)}},
            {},
            Prose("no throughput result file"),
        ),
        (
            SLOWER_RUNNER_CPU,
            {_CPP: {_CLASSIC: InstructionCount(1)}},
            {_CPP: {_FD: FramesPerSecond(1)}},
            Prose("lanes on one side only"),
        ),
        (
            SLOWER_RUNNER_CPU,
            {_CPP: {_FD: InstructionCount(1)}},
            {_CPP: {_FD: FramesPerSecond(10_138)}},
            Prose("not a noted limitation"),
        ),
        (
            SLOWER_RUNNER_CPU,
            {_CPP: {LaneName("LIN: Frame Building"): InstructionCount(1)}},
            {_CPP: {LaneName("LIN: Frame Building"): FramesPerSecond(1)}},
            Prose("names no bus"),
        ),
    ],
)
def test_a_run_no_budget_rests_on_is_refused(
    tmp_path: Path, cpu: ToolVersion, counts: _Counts, rates: _Rates, reason: Prose
) -> None:
    """Each run no budget rests on is refused, naming why.

    That is a run on another runner class, one missing a throughput result, one
    whose lanes do not match, one with a lane under its bus that is no noted
    limitation, and one with a lane naming no bus.
    """
    with pytest.raises(CalibrationError, match=reason):
        _ = calibrate(_write_run(tmp_path, counts, rates, cpu))


def test_main_writes_the_record_or_exits_1_naming_why(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A run calibrates the record main writes; a run on another runner writes none and exits 1."""
    counts = {_CPP: {_CLASSIC: InstructionCount(100_000)}}
    results = _write_run(tmp_path, counts, {_CPP: {_CLASSIC: FramesPerSecond(9009)}})
    out = tmp_path / "budgets.json"
    assert (
        main(
            [
                CommandWord("--results-dir"),
                CommandWord(str(results)),
                CommandWord("--out"),
                CommandWord(str(out)),
            ]
        )
        == 0
    )
    record: BudgetRecord = json.loads(out.read_text(encoding="utf-8"))
    assert record["lanes"][_CPP][_CLASSIC] == {"instructions": 100_000, "fps_min": 9009}
    other = tmp_path / "other"
    other.mkdir()
    elsewhere = _write_run(other, counts, {}, ToolVersion("AMD EPYC 9V74 96-Core Processor"))
    absent = tmp_path / "absent.json"
    assert (
        main(
            [
                CommandWord("--results-dir"),
                CommandWord(str(elsewhere)),
                CommandWord("--out"),
                CommandWord(str(absent)),
            ]
        )
        == 1
    )
    assert not absent.exists()
    assert "not the slower runner's" in capsys.readouterr().err
