# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.benchmark_instructions``: how a lane's instructions per operation are counted.

A valgrind log is read for its one instruction total and refused with none or
two; one operation's count is the two totals' difference over the frame
counts' difference, refused when the larger run counted no more; each lane of
each binding runs at both frame counts, one lane alone, under valgrind; and
the counts land under their binding and lane in the schema's order, whatever
order the runs finish in.  The runs are a stand-in here, driven on the test's
own thread.
"""

from __future__ import annotations

import sys
from functools import partial
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _executors import DrivenExecutor, Order

from tools.benchmark_instructions import (
    FRAMES_HIGH,
    FRAMES_LOW,
    VALGRIND,
    BindingName,
    CommandWord,
    CountedRun,
    CountError,
    InstructionCount,
    LaneName,
    LaneNumber,
    RunText,
    count_lanes,
    lane_names,
    parse_total,
    per_operation,
    run_argv,
)
from tools.check_bench_schema import Binding

if TYPE_CHECKING:
    from aletheia.common_types import Prose

_PYTHON = Binding(
    "python",
    Path("/venv/bin/python3"),
    Path("/repo/python"),
    available=True,
    required=True,
    python_module=True,
)
_GO = Binding(
    "go",
    Path("/repo/go/benchmarks/benchmark"),
    Path("/repo"),
    available=True,
    required=True,
    python_module=False,
)


def test_a_log_s_one_total_is_read() -> None:
    """The total valgrind ends its log with is read, its thousands separators dropped."""
    log = RunText("==7== Cachegrind\n==7== \n==7== I   refs:      6,248,492,753\n")
    assert parse_total(log) == 6_248_492_753


@pytest.mark.parametrize(
    "log",
    [
        RunText("==7== Cachegrind\n"),
        RunText("==7== I   refs:      1,000\n==8== I   refs:      2,000\n"),
        RunText("I   refs:      1,000\n"),
    ],
)
def test_a_log_without_exactly_one_total_is_refused(log: RunText) -> None:
    """No total, two totals, or a total valgrind did not print are each refused."""
    with pytest.raises(CountError, match="instruction totals, not one"):
        _ = parse_total(log)


def test_one_operation_is_the_difference_over_the_frames() -> None:
    """The extra frames' instructions, divided among them."""
    low = InstructionCount(5_000_000)
    high = InstructionCount(5_000_000 + (FRAMES_HIGH - FRAMES_LOW) * 283_716 + 999)
    assert per_operation(low, high) == 283_716


@pytest.mark.parametrize("high", [InstructionCount(5_000_000), InstructionCount(4_999_999)])
def test_a_larger_run_counting_no_more_is_refused(high: InstructionCount) -> None:
    """A run of more frames that counted no more instructions measured nothing."""
    with pytest.raises(CountError, match="not more than"):
        _ = per_operation(InstructionCount(5_000_000), high)


def test_each_run_counts_one_lane_alone_under_valgrind() -> None:
    """The Python harness runs as a module and a compiled one by its mode, one pass, one lane."""
    flags = ["--frames", "1100", "--runs", "1", "--warmup", "0", "--lane", "3"]
    python = run_argv(CountedRun(_PYTHON, LaneNumber(3), FRAMES_HIGH))
    go = run_argv(CountedRun(_GO, LaneNumber(3), FRAMES_HIGH))
    assert python == [*VALGRIND, "/venv/bin/python3", "-m", "benchmarks.throughput", *flags]
    assert go == [*VALGRIND, "/repo/go/benchmarks/benchmark", "throughput", *flags]


def test_the_lanes_are_the_schema_s_six_in_order() -> None:
    """The lanes counted are the throughput lanes the schema lists, in its order."""
    lanes = lane_names()
    assert len(lanes) == 6
    assert lanes[2] == LaneName("CAN 2.0B: Frame Building")


def _stand_in(run: CountedRun) -> InstructionCount:
    """Count a run from its binding, lane and frames: a fixed start, then each frame's cost."""
    per_frame = (100 if run.binding.name == "python" else 10) * run.lane
    return InstructionCount(1_000_000 + per_frame * run.frames)


@pytest.mark.parametrize("order", [Order.FIRST_SUBMITTED, Order.LAST_SUBMITTED])
def test_every_lane_of_every_binding_lands_at_its_own_place(order: Order) -> None:
    """Each binding's lanes get their own counts, whichever run finishes first."""
    lanes = [LaneName("a"), LaneName("b")]
    counts = count_lanes(
        [_PYTHON, _GO], lanes, count=_stand_in, executor=partial(DrivenExecutor, order=order)
    )
    want = {
        BindingName("python"): {
            LaneName("a"): InstructionCount(100),
            LaneName("b"): InstructionCount(200),
        },
        BindingName("go"): {
            LaneName("a"): InstructionCount(10),
            LaneName("b"): InstructionCount(20),
        },
    }
    assert counts == want


def _said_stand_in(run: CountedRun) -> InstructionCount:
    """Count a run as ``_stand_in`` does, saying on stderr which run it is."""
    _ = sys.stderr.write(f"ran {run.binding.name} {run.frames}\n")
    return _stand_in(run)


def test_the_count_is_reported_as_the_runs_arrive(capsys: pytest.CaptureFixture[Prose]) -> None:
    """The count reports on stderr before the first run's total is read and as each one is read."""
    _ = count_lanes([_PYTHON, _GO], [LaneName("a")], count=_said_stand_in, executor=DrivenExecutor)
    runs = [(name, frames) for name in ("python", "go") for frames in (FRAMES_LOW, FRAMES_HIGH)]
    assert capsys.readouterr().err.splitlines() == [
        "progress: 0/4 lane runs counted",
        *(
            line
            for done, (name, frames) in enumerate(runs, 1)
            for line in (f"ran {name} {frames}", f"progress: {done}/4 lane runs counted")
        ),
    ]


def test_a_run_that_fails_ends_the_count() -> None:
    """A counted run that raises is the count's error, not a missing lane."""

    def failing(run: CountedRun) -> InstructionCount:
        if run.binding.name == "go":
            message = "go lane 1 at 100 frames exited 1: boom"
            raise CountError(message)
        return _stand_in(run)

    with pytest.raises(CountError, match="go lane 1"):
        _ = count_lanes([_PYTHON, _GO], [LaneName("a")], count=failing, executor=DrivenExecutor)


def test_valgrind_counts_and_writes_nothing_beside_its_log() -> None:
    """Cachegrind runs without its cache simulation and writes no output file."""
    expected = (
        CommandWord("valgrind"),
        CommandWord("--tool=cachegrind"),
        CommandWord("--cache-sim=no"),
        CommandWord("--cachegrind-out-file=/dev/null"),
    )
    assert expected == VALGRIND
