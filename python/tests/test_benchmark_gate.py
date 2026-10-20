# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.benchmark_gate``: the throughput gate and its baseline, and the load scaling check.

The committed runner baseline, ``benchmarks/gha_baseline.json``, carries a bar
for every lane the runner measures: the bindings the gate reads are the
languages ``benchmarks/SCHEMA.yaml`` names, and each carries every throughput
lane the schema pins, with a positive number. The throughput gate's ``main``:
a lane past the threshold fails, one inside it passes, a binding the run lacks
is skipped, a binding the run has that lacks a baseline lane fails with the
lane named, a run with no result file fails, and a missing baseline prints the
run in baseline shape and passes.

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
from typing import TYPE_CHECKING, NamedTuple, TypedDict, cast

import pytest
from _bench_schema import BindingId, RowKey, SweepName, schema

from tools.benchmark_gate import (
    BINDINGS,
    MAX_ALLOCATION_DOUBLING,
    SWEEPS,
    ByteCount,
    PointSize,
    Seconds,
    main,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence

    from _bench_schema import Sizes

    from tools.benchmark_gate import SizeColumn, Sweep, SweepKey

_REPO_ROOT = Path(__file__).resolve().parents[2]
_BASELINE = _REPO_ROOT / "benchmarks" / "gha_baseline.json"

LANE = "CAN 2.0B: Frame Building"
BASE_FPS = 1000.0


def _write_results(results_dir: Path, binding: str, fps: float, lane: str = LANE) -> None:
    """Write one binding's throughput result file with a single lane."""
    results_dir.mkdir(parents=True, exist_ok=True)
    payload = {"results": [{"name": lane, "fps_mean": fps}]}
    path = results_dir / f"{binding}_throughput.json"
    _ = path.write_text(json.dumps(payload), encoding="utf-8")


def _write_baseline(path: Path, baseline: dict[str, dict[str, float]]) -> None:
    """Write a baseline file in the gate's own shape."""
    _ = path.write_text(json.dumps(baseline), encoding="utf-8")


def _gate(results_dir: Path, baseline: Path, threshold_pct: float = 30.0) -> int:
    """Run the gate's ``main`` against a results directory and a baseline path."""
    return main(
        [
            "--results-dir",
            str(results_dir),
            "--baseline",
            str(baseline),
            "--threshold-pct",
            str(threshold_pct),
        ]
    )


def test_the_gate_reads_every_language_the_schema_names() -> None:
    """The bindings the gate compares are exactly the schema's languages."""
    assert set(BINDINGS) == set(schema()["envelope"]["languages"])


def test_the_committed_baseline_carries_a_bar_for_every_lane() -> None:
    """Every binding the gate reads has every throughput lane, each positive."""
    text = _BASELINE.read_text(encoding="utf-8")
    baseline = cast("dict[str, dict[str, float]]", json.loads(text))
    assert set(baseline) == set(BINDINGS)
    lanes = schema()["modes"]["throughput"]["lane_names"]
    for binding in BINDINGS:
        assert set(baseline[binding]) == set(lanes), binding
        for lane, fps in baseline[binding].items():
            assert fps > 0.0, f"{binding} / {lane}"


def test_a_lane_past_the_threshold_fails(tmp_path: Path) -> None:
    """A lane 31% slower than its bar fails a 30% gate."""
    _write_results(tmp_path / "results", "cpp", BASE_FPS * 0.69)
    _write_baseline(tmp_path / "baseline.json", {"cpp": {LANE: BASE_FPS}})
    assert _gate(tmp_path / "results", tmp_path / "baseline.json") == 1


def test_a_lane_inside_the_threshold_passes(tmp_path: Path) -> None:
    """A lane 29% slower than its bar passes a 30% gate."""
    _write_results(tmp_path / "results", "cpp", BASE_FPS * 0.71)
    _write_baseline(tmp_path / "baseline.json", {"cpp": {LANE: BASE_FPS}})
    assert _gate(tmp_path / "results", tmp_path / "baseline.json") == 0


def test_a_binding_the_run_lacks_is_skipped(tmp_path: Path) -> None:
    """A baseline binding with no result file is neither scored nor failed."""
    _write_results(tmp_path / "results", "cpp", BASE_FPS)
    _write_baseline(tmp_path / "baseline.json", {"cpp": {LANE: BASE_FPS}, "go": {LANE: BASE_FPS}})
    assert _gate(tmp_path / "results", tmp_path / "baseline.json") == 0


def test_a_present_binding_lacking_a_baseline_lane_fails(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A binding with a result file that lacks a baseline lane fails, the lane named."""
    other = "CAN 2.0B: Signal Extraction"
    _write_results(tmp_path / "results", "cpp", BASE_FPS)
    _write_baseline(tmp_path / "baseline.json", {"cpp": {LANE: BASE_FPS, other: BASE_FPS}})
    assert _gate(tmp_path / "results", tmp_path / "baseline.json") == 1
    assert f"cpp / {other}" in capsys.readouterr().err


def test_a_run_with_no_result_file_fails(tmp_path: Path) -> None:
    """An empty results directory is a failure, never a vacuous pass."""
    (tmp_path / "results").mkdir()
    _write_baseline(tmp_path / "baseline.json", {"cpp": {LANE: BASE_FPS}})
    assert _gate(tmp_path / "results", tmp_path / "baseline.json") == 1


def test_a_missing_baseline_reports_the_run_and_passes(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no baseline the gate prints the run in baseline shape and exits zero."""
    _write_results(tmp_path / "results", "cpp", BASE_FPS)
    assert _gate(tmp_path / "results", tmp_path / "absent.json") == 0
    out = capsys.readouterr().out
    printed = cast("dict[str, dict[str, float]]", json.loads(out[out.index("{") :]))
    assert printed == {"cpp": {LANE: BASE_FPS}}


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
