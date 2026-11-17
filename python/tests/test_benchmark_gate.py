# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.benchmark_gate``: the instruction check, and the load scaling check.

The instruction check, ``--bench instructions``: the bindings the gate reads
are the languages ``benchmarks/SCHEMA.yaml`` names. A lane within 5% of its
committed count either way passes, at either end of the bound; a lane a count
past it either way fails, naming the lane and why; a lane or a binding one
side lacks fails by name; counts taken with another toolchain or at other
frame counts fail naming what differs, before any lane is compared; and a run
with no report, no committed counts or no budgets fails rather than passing
vacuously. A lane at its budget passes and one instruction over it fails,
named; a noted limitation over its budget passes, reported as one, and fails
once within it, asking for a recalibration; a noted limitation with no budget,
and a lane only the budgets or only the run holds, fail by name; and budgets
calibrated with another toolchain or at other frame counts fail naming what
differs.

The load scaling check, ``--bench scaling``: its factor sits between a linear
load's doubling and a quadratic one's, and it reads the schema's sweeps that
carry an allocation, in the schema's order, whose pinned sizes double. In each
load sweep, an allocation linear in its size passes in every binding, one
growing n log n passes, and a quadratic one fails, naming its binding and
sweep; growth at the bound passes and a byte past it fails, naming them too.
Load times quadratic in the size pass beside a linear allocation, each step's
and the whole sweep's ratios printed; a first point without a load time prints
n/a for it and for every ratio it is in, and a first point timed at 0 s prints
n/a for the ratios it divides, both passing. A binding with no result file, a
missing sweep, a point without an allocation or with none counted, a point
without its size, a sweep of one point and points that do not double each fail
with their reason named.
"""

from __future__ import annotations

import itertools
import json
import math
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, TypedDict

import pytest
from _bench_schema import BindingId, RowKey, SweepName, schema

from tools.benchmark_budgets import (
    RUNNER_CLASSES,
    BudgetRecord,
    FramesPerSecond,
    bus_of,
)
from tools.benchmark_gate import (
    BINDINGS,
    MAX_ALLOCATION_DOUBLING,
    SWEEPS,
    ByteCount,
    PointSize,
    Seconds,
    main,
)
from tools.benchmark_instructions import (
    BindingName,
    FrameCount,
    InstructionCount,
    InstructionReport,
    LaneName,
    ToolName,
    ToolVersion,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence

    from _bench_schema import Sizes

    from tools.benchmark_gate import SizeColumn, Sweep, SweepKey

_REPO_ROOT = Path(__file__).resolve().parents[2]
_LANE = LaneName("CAN 2.0B: Frame Building")
_OTHER_LANE = LaneName("CAN 2.0B: Signal Extraction")
_CPP, _GO = BindingName("cpp"), BindingName("go")
_TOOLCHAIN = {ToolName("python"): ToolVersion("3.14.10"), ToolName("go"): ToolVersion("go1.27.4")}
_FRAMES = [FrameCount(100), FrameCount(1100)]

# Each binding's lanes and their instructions per operation.
type _Counts = dict[BindingName, dict[LaneName, InstructionCount]]
# A calibrating run's worst rate as a multiple of its lane's bus.
RateOverBus = NewType("RateOverBus", float)
# The lanes a budget record lists as under their bus.
type _Limitations = dict[BindingName, list[LaneName]]


def _one(binding: BindingName, count: InstructionCount) -> _Counts:
    """Answer one binding's frame-building lane at ``count``."""
    return {binding: {_LANE: count}}


def _report(
    counts: _Counts,
    *,
    toolchain: dict[ToolName, ToolVersion] | None = None,
    frames: list[FrameCount] | None = None,
) -> InstructionReport:
    """Return an instruction report holding ``counts``, the toolchain and frames as given."""
    return {
        "toolchain": dict(_TOOLCHAIN) if toolchain is None else toolchain,
        "host": {ToolName("cpu"): RUNNER_CLASSES[0]},
        "frames": list(_FRAMES) if frames is None else frames,
        "counts": counts,
    }


def _budgets(
    counts: _Counts,
    rate: RateOverBus = RateOverBus(100),
    *,
    limitations: _Limitations | None = None,
    toolchain: dict[ToolName, ToolVersion] | None = None,
    frames: list[FrameCount] | None = None,
) -> BudgetRecord:
    """Return budgets calibrated from ``counts`` at ``rate`` times each lane's bus."""
    return {
        "host": {ToolName("cpu"): RUNNER_CLASSES[0]},
        "toolchain": dict(_TOOLCHAIN) if toolchain is None else toolchain,
        "frames": list(_FRAMES) if frames is None else frames,
        "lanes": {
            binding: {
                lane: {"instructions": count, "fps_min": FramesPerSecond(bus_of(lane) * rate)}
                for lane, count in lanes.items()
            }
            for binding, lanes in counts.items()
        },
        "limitations": {} if limitations is None else limitations,
    }


def _instructions(
    tmp_path: Path,
    committed: InstructionReport | None,
    measured: InstructionReport | None,
    budgets: BudgetRecord | Literal["absent"] | None = None,
) -> int:
    """Write the reports and the budgets, as present, and run the instruction check on them.

    Unless given, the budgets are a hundred times each committed lane's count,
    so no lane meets them.
    """
    results = tmp_path / "results"
    results.mkdir()
    if measured is not None:
        _ = (results / "instructions.json").write_text(json.dumps(measured), encoding="utf-8")
    counts = tmp_path / "instruction_counts.json"
    if committed is not None:
        _ = counts.write_text(json.dumps(committed), encoding="utf-8")
    record = tmp_path / "instruction_budgets.json"
    if budgets != "absent":
        written = (
            _budgets({} if committed is None else committed["counts"])
            if budgets is None
            else budgets
        )
        _ = record.write_text(json.dumps(written), encoding="utf-8")
    return main(
        [
            "--bench",
            "instructions",
            "--results-dir",
            str(results),
            "--counts",
            str(counts),
            "--budgets",
            str(record),
        ]
    )


def test_the_gate_reads_every_language_the_schema_names() -> None:
    """The bindings the gate compares are exactly the schema's languages."""
    assert set(BINDINGS) == set(schema()["envelope"]["languages"])


@pytest.mark.parametrize(
    "now", [InstructionCount(95_000), InstructionCount(100_000), InstructionCount(105_000)]
)
def test_a_lane_within_the_bound_passes(tmp_path: Path, now: InstructionCount) -> None:
    """A lane 5% either side of its count, or at it, passes."""
    committed = _report(_one(_CPP, InstructionCount(100_000)))
    assert _instructions(tmp_path, committed, _report(_one(_CPP, now))) == 0


@pytest.mark.parametrize(
    ("now", "why"),
    [
        (InstructionCount(105_001), Prose("a slowdown")),
        (InstructionCount(94_999), Prose("commit this run's counts")),
    ],
)
def test_a_lane_past_the_bound_either_way_fails_named(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose], now: InstructionCount, why: Prose
) -> None:
    """A lane a count past 5% above or below its count fails, naming the lane and why."""
    committed = _report(_one(_CPP, InstructionCount(100_000)))
    assert _instructions(tmp_path, committed, _report(_one(_CPP, now))) == 1
    err = capsys.readouterr().err
    assert f"cpp / {_LANE}: 100,000 -> {now:,}" in err
    assert why in err


@pytest.mark.parametrize(
    ("committed", "measured", "missing"),
    [
        (_one(_CPP, InstructionCount(1)), {}, Prose(f"cpp / {_LANE}: no count in this run")),
        ({}, _one(_GO, InstructionCount(1)), Prose(f"go / {_LANE}: no committed count")),
        (
            {_CPP: {_LANE: InstructionCount(1), _OTHER_LANE: InstructionCount(1)}},
            _one(_CPP, InstructionCount(1)),
            Prose(f"cpp / {_OTHER_LANE}: no count in this run"),
        ),
    ],
)
def test_a_lane_one_side_lacks_fails_named(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    committed: _Counts,
    measured: _Counts,
    missing: Prose,
) -> None:
    """A lane or a binding only one report holds fails, named."""
    assert _instructions(tmp_path, _report(committed), _report(measured)) == 1
    assert missing in capsys.readouterr().err


@pytest.mark.parametrize(
    ("toolchain", "frames", "named"),
    [
        (
            {**_TOOLCHAIN, ToolName("go"): ToolVersion("go1.27.5")},
            None,
            Prose("go: committed 'go1.27.4', this run 'go1.27.5'"),
        ),
        (
            {ToolName("python"): ToolVersion("3.14.10")},
            None,
            Prose("go: committed 'go1.27.4', this run None"),
        ),
        (
            None,
            [FrameCount(100), FrameCount(2100)],
            Prose("frames: committed [100, 1100], this run [100, 2100]"),
        ),
    ],
)
def test_counts_taken_otherwise_are_not_compared(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    toolchain: dict[ToolName, ToolVersion] | None,
    frames: list[FrameCount] | None,
    named: Prose,
) -> None:
    """Another toolchain or other frame counts fail naming the difference, comparing no lane."""
    counts = _one(_CPP, InstructionCount(100_000))
    measured = _report(counts, toolchain=toolchain, frames=frames)
    assert _instructions(tmp_path, _report(counts), measured) == 1
    captured = capsys.readouterr()
    assert named in captured.err
    assert _LANE not in captured.out


@pytest.mark.parametrize("absent", ["committed", "measured", "budgets"])
def test_a_missing_report_fails(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    absent: Literal["committed", "measured", "budgets"],
) -> None:
    """No run report, no committed counts or no budgets fails rather than passing vacuously."""
    report = _report(_one(_CPP, InstructionCount(1)))
    committed = None if absent == "committed" else report
    measured = None if absent == "measured" else report
    budgets = "absent" if absent == "budgets" else None
    assert _instructions(tmp_path, committed, measured, budgets) == 1
    named = {
        "committed": "no committed counts",
        "measured": "no instruction report",
        "budgets": "no budgets",
    }
    assert named[absent] in capsys.readouterr().err


@pytest.mark.parametrize(
    ("now", "status"), [(InstructionCount(100_000), 0), (InstructionCount(100_001), 1)]
)
def test_a_lane_over_its_budget_fails_named(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose], now: InstructionCount, status: ExitStatus
) -> None:
    """A lane at its budget passes; an instruction over it fails, naming the lane and why."""
    counts = _one(_CPP, InstructionCount(100_000))
    budgets = _budgets(counts, RateOverBus(1))
    assert _instructions(tmp_path, _report(counts), _report(_one(_CPP, now)), budgets) == status
    err = capsys.readouterr().err
    assert (f"cpp / {_LANE}: {now:,} of a budget of 100,000, over its budget" in err) == bool(
        status
    )


@pytest.mark.parametrize(
    ("rate", "status", "said"),
    [
        (RateOverBus(0.5), 0, Prose("(a noted limitation)")),
        (RateOverBus(1), 1, Prose("no longer a limitation: recalibrate")),
    ],
)
def test_a_noted_limitation_passes_over_its_budget_and_fails_within_it(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    rate: RateOverBus,
    status: ExitStatus,
    said: Prose,
) -> None:
    """A noted lane over its budget is reported and passes; one within it asks to recalibrate."""
    counts = _one(_CPP, InstructionCount(100_000))
    budgets = _budgets(counts, rate, limitations={_CPP: [_LANE]})
    assert _instructions(tmp_path, _report(counts), _report(counts), budgets) == status
    captured = capsys.readouterr()
    assert said in captured.out + captured.err


@pytest.mark.parametrize(
    ("budgeted", "limitations", "missing"),
    [
        ({}, {}, Prose(f"cpp / {_LANE}: no budget")),
        (
            {_CPP: {_LANE: InstructionCount(1), _OTHER_LANE: InstructionCount(1)}},
            {},
            Prose(f"cpp / {_OTHER_LANE}: no count in this run"),
        ),
        (
            _one(_CPP, InstructionCount(1)),
            {_GO: [_LANE]},
            Prose(f"go / {_LANE}: a noted limitation with no budget"),
        ),
    ],
)
def test_a_lane_the_budgets_or_the_run_lacks_fails_named(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    budgeted: _Counts,
    limitations: _Limitations,
    missing: Prose,
) -> None:
    """A lane with no budget, a budget with no count and an unbudgeted limitation fail, named."""
    counts = _one(_CPP, InstructionCount(1))
    budgets = _budgets(budgeted, limitations=limitations)
    assert _instructions(tmp_path, _report(counts), _report(counts), budgets) == 1
    assert missing in capsys.readouterr().err


@pytest.mark.parametrize(
    ("toolchain", "frames", "named"),
    [
        (
            {**_TOOLCHAIN, ToolName("go"): ToolVersion("go1.27.3")},
            None,
            Prose("go: committed 'go1.27.3', this run 'go1.27.4'"),
        ),
        (
            None,
            [FrameCount(100), FrameCount(2100)],
            Prose("frames: committed [100, 2100], this run [100, 1100]"),
        ),
    ],
)
def test_budgets_calibrated_otherwise_ask_for_a_recalibration(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    toolchain: dict[ToolName, ToolVersion] | None,
    frames: list[FrameCount] | None,
    named: Prose,
) -> None:
    """Budgets taken with another toolchain or at other frame counts fail naming what differs."""
    counts = _one(_CPP, InstructionCount(100_000))
    budgets = _budgets(counts, toolchain=toolchain, frames=frames)
    assert _instructions(tmp_path, _report(counts), _report(counts), budgets) == 1
    captured = capsys.readouterr()
    assert named in captured.err
    assert "Recalibrate" in captured.err
    assert _LANE not in captured.out


@pytest.mark.parametrize(
    ("calibrated", "drawn", "noted"),
    [
        (RUNNER_CLASSES[1], RUNNER_CLASSES[0], Prose("ranked slower than the")),
        (RUNNER_CLASSES[1], RUNNER_CLASSES[1], None),
        (RUNNER_CLASSES[1], RUNNER_CLASSES[2], None),
        (RUNNER_CLASSES[1], ToolVersion("AMD EPYC 9999 Unseen"), Prose("does not rank")),
        (ToolVersion("AMD EPYC 9999 Unseen"), RUNNER_CLASSES[-1], Prose("ranked slower than")),
    ],
    ids=["slower", "the same", "faster", "unranked run", "unranked record"],
)
def test_a_run_on_a_slower_class_than_the_records_is_noted_and_fails_nothing(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    calibrated: ToolVersion,
    drawn: ToolVersion,
    noted: Prose | None,
) -> None:
    """A run on a class ranked slower, or on one the ranking lacks, is noted; the verdict stays."""
    counts = _one(_CPP, InstructionCount(100_000))
    budgets = _budgets(counts)
    budgets["host"] = {ToolName("cpu"): calibrated}
    measured = _report(counts)
    measured["host"] = {ToolName("cpu"): drawn}
    assert _instructions(tmp_path, _report(counts), measured, budgets) == 0
    notices = [
        line for line in capsys.readouterr().out.splitlines() if line.startswith("::notice::")
    ]
    if noted is None:
        assert notices == []
    else:
        assert len(notices) == 1, notices
        assert noted in notices[0]
        assert str(drawn) in notices[0]


_SWEEP_IDS = [sweep.key for sweep in SWEEPS]


def _sizes(key: SweepKey) -> Sizes:
    """Return a load sweep's sizes as the schema pins them, the literal sweeps sharing theirs."""
    experiment = schema()["experiment"]
    return experiment["dbc_sizes"] if key == "dbc_size" else experiment["literal_lengths"]


class _Point(NamedTuple):
    """One point a fixture writes: its size, its load time and its allocation, None for none."""

    size: PointSize
    seconds: Seconds | None
    allocated: ByteCount | None


class _Row(TypedDict, total=False):
    """One point of a load sweep as a result file holds it."""

    messages: PointSize
    digits: PointSize
    seconds: Seconds
    allocated_bytes: ByteCount


def _linear_bytes(size: PointSize) -> ByteCount:
    """Allocate a thousand bytes for each unit of size."""
    return ByteCount(1000 * size)


def _n_log_n_bytes(size: PointSize) -> ByteCount:
    """Allocate a thousand bytes for each unit of size, times the size's binary logarithm."""
    return ByteCount(round(1000 * size * math.log2(size)))


def _quadratic_bytes(size: PointSize) -> ByteCount:
    """Allocate the size's square in bytes."""
    return ByteCount(size * size)


def _linear_seconds(size: PointSize) -> Seconds:
    """Take a second for each hundred thousand units of size."""
    return Seconds(size / 100_000)


def _quadratic_seconds(size: PointSize) -> Seconds:
    """Take the square of a second for each hundred thousand units of size."""
    return Seconds((size / 100_000) ** 2)


def _points(
    key: SweepKey,
    allocated: Callable[[PointSize], ByteCount] = _linear_bytes,
    seconds: Callable[[PointSize], Seconds] = _linear_seconds,
) -> list[_Point]:
    """Return a sweep's points at its quick sizes, each load timed and allocating as given."""
    return [
        _Point(PointSize(n), seconds(PointSize(n)), allocated(PointSize(n)))
        for n in _sizes(key)["quick"]
    ]


def _row(column: SizeColumn, point: _Point) -> _Row:
    """Return a point as a result file holds it, its size under the sweep's column."""
    row: _Row = {}
    row[column] = point.size
    if point.seconds is not None:
        row["seconds"] = point.seconds
    if point.allocated is not None:
        row["allocated_bytes"] = point.allocated
    return row


def _write_rows(path: Path, rows: Mapping[SweepKey, Sequence[_Row]]) -> None:
    """Write one binding's scaling result file holding these load sweeps' rows."""
    path.parent.mkdir(parents=True, exist_ok=True)
    _ = path.write_text(json.dumps({"results": rows}), encoding="utf-8")


def _write(path: Path, sweeps: Mapping[SweepKey, Sequence[_Point]]) -> None:
    """Write one binding's scaling result file holding these load sweeps."""
    columns: dict[SweepKey, SizeColumn] = {sweep.key: sweep.size for sweep in SWEEPS}
    _write_rows(
        path, {key: [_row(columns[key], p) for p in points] for key, points in sweeps.items()}
    )


def _linear() -> dict[SweepKey, list[_Point]]:
    """Every load sweep, its load times and allocations linear in its size."""
    return {sweep.key: _points(sweep.key) for sweep in SWEEPS}


def _write_linear(results_dir: Path) -> None:
    """Write every binding's scaling result file with linear load sweeps."""
    for binding in BINDINGS:
        _write(results_dir / f"{binding}_scaling.json", _linear())


def _scaling(results_dir: Path) -> ExitStatus:
    """Run the load scaling check over a results directory."""
    return ExitStatus(main(["--bench", "scaling", "--results-dir", str(results_dir)]))


def _failures(capsys: pytest.CaptureFixture[Prose]) -> list[Prose]:
    """Return the lines the check printed under its failure banner."""
    err = capsys.readouterr().err
    return [Prose(line.strip()) for line in err.split("FAIL:", 1)[1].splitlines() if line]


def _printed(capsys: pytest.CaptureFixture[Prose], binding: BindingId, sweep: Sweep) -> list[Prose]:
    """Return the lines the check printed for one binding's sweep: each step's, then the whole's."""
    out = capsys.readouterr().out
    return [Prose(line) for line in out.splitlines() if line.split()[:2] == [binding, sweep.key]]


def test_the_factor_sits_between_a_linear_load_and_a_quadratic_one() -> None:
    """A doubling doubles a linear load's allocation and quadruples a quadratic one's."""
    assert 2.0 < MAX_ALLOCATION_DOUBLING < 4.0


def test_the_check_reads_every_sweep_the_schema_counts_allocation_in() -> None:
    """The sweeps read are the schema's sweeps whose rows carry allocated_bytes, in its order."""
    row_keys = schema()["modes"]["scaling"]["row_keys"]
    counted = [name for name, keys in row_keys.items() if RowKey("allocated_bytes") in keys]
    assert [SweepName(sweep.key) for sweep in SWEEPS] == counted
    for sweep in SWEEPS:
        assert RowKey(sweep.size) in row_keys[SweepName(sweep.key)], sweep.key


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_the_schema_s_sizes_double(sweep: Sweep) -> None:
    """The bound counts doublings, so every size the schema pins for a sweep doubles the last."""
    pinned = _sizes(sweep.key)
    for sizes in (pinned["full"], pinned["quick"]):
        assert len(sizes) >= len(("small", "large")), sizes
        assert all(large == 2 * small for small, large in itertools.pairwise(sizes)), sizes


def test_an_allocation_linear_in_its_size_passes(tmp_path: Path) -> None:
    """Every binding doubling its allocation with its size, in every sweep, passes."""
    _write_linear(tmp_path)
    assert _scaling(tmp_path) == 0


def test_an_allocation_growing_n_log_n_passes(tmp_path: Path) -> None:
    """The bound leaves room for a load that sorts what it reads."""
    _write_linear(tmp_path)
    _write(
        tmp_path / "go_scaling.json",
        {sweep.key: _points(sweep.key, _n_log_n_bytes) for sweep in SWEEPS},
    )
    assert _scaling(tmp_path) == 0


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_an_allocation_quadratic_in_its_size_fails(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """One sweep of one binding quadrupling its allocation with each doubling fails, alone."""
    _write_linear(tmp_path)
    _write(
        tmp_path / "rust_scaling.json",
        {**_linear(), sweep.key: _points(sweep.key, _quadratic_bytes)},
    )
    assert _scaling(tmp_path) == 1
    [failure] = _failures(capsys)
    assert failure.startswith(f"rust: {sweep.key}: "), failure


def test_load_times_quadratic_in_the_size_pass_and_are_printed(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The times decide nothing, but each step's and the whole sweep's ratios are printed."""
    for binding in BINDINGS:
        _write(
            tmp_path / f"{binding}_scaling.json",
            {sweep.key: _points(sweep.key, _linear_bytes, _quadratic_seconds) for sweep in SWEEPS},
        )
    assert _scaling(tmp_path) == 0
    out = capsys.readouterr().out
    for sweep in SWEEPS:
        sizes = _sizes(sweep.key)["quick"]
        lines = [line for line in out.splitlines() if f" {sweep.key} " in line]
        steps = [line for line in lines if " bytes (x" in line]
        assert len(steps) == len(BINDINGS) * (len(sizes) - 1), lines
        assert all(" s (x4.00), " in line and " bytes (x2.00)" in line for line in steps), steps
        whole = (
            f"seconds x{4 ** (len(sizes) - 1):.2f}, allocated bytes x{2 ** (len(sizes) - 1):.2f}"
        )
        assert sum(whole in line for line in lines) == len(BINDINGS), lines


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_growth_at_the_bound_passes_and_past_it_fails(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The bound is the factor to the power of the doublings, over the whole sweep, inclusive."""
    _write_linear(tmp_path)
    sizes = [PointSize(n) for n in _sizes(sweep.key)["quick"]]
    first = ByteCount(1_000_000)
    at_bound = ByteCount(math.floor(first * MAX_ALLOCATION_DOUBLING ** (len(sizes) - 1)))

    def ending_at(last: ByteCount) -> list[_Point]:
        allocated = [first] * (len(sizes) - 1) + [last]
        return [_Point(n, _linear_seconds(n), b) for n, b in zip(sizes, allocated, strict=True)]

    _write(tmp_path / "go_scaling.json", {**_linear(), sweep.key: ending_at(at_bound)})
    assert _scaling(tmp_path) == 0
    past_it = ByteCount(at_bound + 1)
    _write(tmp_path / "go_scaling.json", {**_linear(), sweep.key: ending_at(past_it)})
    assert _scaling(tmp_path) == 1
    [failure] = _failures(capsys)
    assert failure.startswith(f"go: {sweep.key}: "), failure


def test_a_binding_without_a_result_file_fails_named(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The check is required, so a binding that reported nothing fails it rather than passing."""
    _write_linear(tmp_path)
    (tmp_path / "cpp_scaling.json").unlink()
    assert _scaling(tmp_path) == 1
    assert _failures(capsys) == ["cpp: no cpp_scaling.json"]


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_a_point_without_a_load_time_reads_n_a_and_decides_nothing(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A first point reporting no seconds prints n/a for its time and every ratio it is in."""
    _write_linear(tmp_path)
    first, second, *rest = _points(sweep.key)
    _write(
        tmp_path / "python_scaling.json",
        {**_linear(), sweep.key: [first._replace(seconds=None), second, *rest]},
    )
    assert _scaling(tmp_path) == 0
    step, *_, whole = _printed(capsys, BindingId("python"), sweep)
    assert f": n/a s -> {second.seconds:.4f} s (x n/a), " in step, step
    assert ": seconds x n/a, allocated bytes x" in whole, whole


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_a_point_timed_at_zero_seconds_divides_no_ratio_and_decides_nothing(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A first point timed at 0 s prints its time, and n/a for the ratios it would divide."""
    _write_linear(tmp_path)
    first, second, *rest = _points(sweep.key)
    _write(
        tmp_path / "python_scaling.json",
        {**_linear(), sweep.key: [first._replace(seconds=Seconds(0.0)), second, *rest]},
    )
    assert _scaling(tmp_path) == 0
    step, *_, whole = _printed(capsys, BindingId("python"), sweep)
    assert f": 0.0000 s -> {second.seconds:.4f} s (x n/a), " in step, step
    assert ": seconds x n/a, allocated bytes x" in whole, whole


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_a_point_without_its_size_fails_named(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A point reporting no size cannot be placed on a doubling, so its sweep fails as undoubled."""
    _write_linear(tmp_path)
    rows: dict[SweepKey, list[_Row]] = {
        other.key: [_row(other.size, p) for p in _points(other.key)] for other in SWEEPS
    }
    del rows[sweep.key][0][sweep.size]
    _write_rows(tmp_path / "python_scaling.json", rows)
    assert _scaling(tmp_path) == 1
    assert _failures(capsys) == [f"python: the {sweep.key} points do not double their {sweep.size}"]


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_a_missing_sweep_fails_named(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A result file holding every load sweep but one fails on the one it lacks."""
    _write_linear(tmp_path)
    others: dict[SweepKey, list[_Point]] = {
        key: points for key, points in _linear().items() if key != sweep.key
    }
    _write(tmp_path / "python_scaling.json", others)
    assert _scaling(tmp_path) == 1
    assert _failures(capsys) == [f"python: no {sweep.key} sweep"]


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_a_point_without_an_allocation_fails_named(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A point that reports no allocated_bytes fails the check, rather than raising."""
    _write_linear(tmp_path)
    first, *rest = _points(sweep.key)
    _write(
        tmp_path / "python_scaling.json",
        {**_linear(), sweep.key: [first._replace(allocated=None), *rest]},
    )
    assert _scaling(tmp_path) == 1
    assert _failures(capsys) == [
        f"python: {sweep.key} at {first.size} {sweep.size} reports no allocated_bytes"
    ]


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_a_point_that_counted_no_allocation_fails_named(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A point reporting 0 bytes, an unread count, fails the check, rather than dividing by it."""
    _write_linear(tmp_path)
    first, *rest = _points(sweep.key)
    _write(
        tmp_path / "python_scaling.json",
        {**_linear(), sweep.key: [first._replace(allocated=ByteCount(0)), *rest]},
    )
    assert _scaling(tmp_path) == 1
    assert _failures(capsys) == [
        f"python: {sweep.key} at {first.size} {sweep.size} reports allocated_bytes 0,"
        + " not a positive count"
    ]


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_a_sweep_of_one_point_fails(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """One size measures no doubling."""
    _write_linear(tmp_path)
    _write(tmp_path / "python_scaling.json", {**_linear(), sweep.key: _points(sweep.key)[-1:]})
    assert _scaling(tmp_path) == 1
    assert _failures(capsys) == [f"python: {sweep.key} has 1 point(s), a doubling needs two"]


@pytest.mark.parametrize("sweep", SWEEPS, ids=_SWEEP_IDS)
def test_points_that_do_not_double_fail(
    sweep: Sweep, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The bound counts doublings, so a sweep whose sizes do not double cannot be judged by it."""
    _write_linear(tmp_path)
    *head, last = _points(sweep.key)
    short = last._replace(size=PointSize(last.size - 1))
    _write(tmp_path / "python_scaling.json", {**_linear(), sweep.key: [*head, short]})
    assert _scaling(tmp_path) == 1
    assert _failures(capsys) == [f"python: the {sweep.key} points do not double their {sweep.size}"]
