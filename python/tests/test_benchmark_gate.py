# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.benchmark_gate``: the throughput gate and its baseline, and the load scaling check.

Two layers. The committed runner baseline, ``benchmarks/gha_baseline.json``,
must carry a bar for every lane the runner measures: the bindings the gate
reads are the languages ``benchmarks/SCHEMA.yaml`` names, and each carries
every throughput lane the schema pins, with a positive number. A lane the
baseline lacks is one the gate skips without a word, so the shape is the gate's
teeth. And ``main`` itself, every polarity: a lane past the threshold fails,
one inside it passes, a binding the run lacks is skipped, a binding the run
has that lacks a baseline lane fails, a run with no result file fails, and a
missing baseline reports and passes.

The load scaling check, ``--bench scaling``, every polarity too: a load linear
in its messages passes and a quadratic one fails, growth at the bound passes
and past it fails, and a binding with no sweep, a sweep of one point or points
that do not double fail, since the check is required.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import TYPE_CHECKING, cast

import yaml

from tools.benchmark_gate import BINDINGS, MAX_DOUBLING, MessageCount, Seconds, main

if TYPE_CHECKING:
    import pytest

_REPO_ROOT = Path(__file__).resolve().parents[2]
_BASELINE = _REPO_ROOT / "benchmarks" / "gha_baseline.json"
_SCHEMA = _REPO_ROOT / "benchmarks" / "SCHEMA.yaml"

LANE = "CAN 2.0B: Frame Building"
BASE_FPS = 1000.0


def _schema() -> dict[str, object]:
    """Load the cross-binding benchmark schema."""
    return cast("dict[str, object]", yaml.safe_load(_SCHEMA.read_text(encoding="utf-8")))


def _schema_languages() -> set[str]:
    """Return the languages the schema's envelope names."""
    envelope = cast("dict[str, list[str]]", _schema()["envelope"])
    return set(envelope["languages"])


def _schema_throughput_lanes() -> list[str]:
    """Return the throughput lane names the schema pins, in order."""
    modes = cast("dict[str, dict[str, list[str]]]", _schema()["modes"])
    return modes["throughput"]["lane_names"]


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
    assert set(BINDINGS) == _schema_languages()


def test_the_committed_baseline_carries_a_bar_for_every_lane() -> None:
    """Every binding the gate reads has every throughput lane, each positive."""
    text = _BASELINE.read_text(encoding="utf-8")
    baseline = cast("dict[str, dict[str, float]]", json.loads(text))
    assert set(baseline) == set(BINDINGS)
    lanes = _schema_throughput_lanes()
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
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
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
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """With no baseline the gate prints the run in baseline shape and exits zero."""
    _write_results(tmp_path / "results", "cpp", BASE_FPS)
    assert _gate(tmp_path / "results", tmp_path / "absent.json") == 0
    out = capsys.readouterr().out
    printed = cast("dict[str, dict[str, float]]", json.loads(out[out.index("{") :]))
    assert printed == {"cpp": {LANE: BASE_FPS}}


# The quick sweep's sizes, each double the one before, and load times for them.
_SIZES = (MessageCount(2500), MessageCount(5000), MessageCount(10000))
_LINEAR = (Seconds(0.25), Seconds(0.5), Seconds(1.0))
_QUADRATIC = (Seconds(0.0625), Seconds(0.25), Seconds(1.0))


def _write_sweep(
    path: Path, seconds: tuple[Seconds, ...], messages: tuple[MessageCount, ...] = _SIZES
) -> None:
    """Write one binding's scaling result file holding only its ``dbc_size`` sweep."""
    path.parent.mkdir(parents=True, exist_ok=True)
    rows = [{"messages": n, "seconds": s} for n, s in zip(messages, seconds, strict=True)]
    _ = path.write_text(json.dumps({"results": {"dbc_size": rows}}), encoding="utf-8")


def _write_linear_sweeps(results_dir: Path) -> None:
    """Write every binding's scaling result file with a load time linear in its messages."""
    for binding in BINDINGS:
        _write_sweep(results_dir / f"{binding}_scaling.json", _LINEAR)


def test_the_factor_sits_between_a_linear_load_and_a_quadratic_one() -> None:
    """A doubling doubles a linear load's time and quadruples a quadratic one's."""
    assert 2.0 < MAX_DOUBLING < 4.0


def test_a_load_linear_in_its_messages_passes(tmp_path: Path) -> None:
    """Every binding doubling its time with its messages passes."""
    _write_linear_sweeps(tmp_path)
    assert main(["--bench", "scaling", "--results-dir", str(tmp_path)]) == 0


def test_a_load_quadratic_in_its_messages_fails(tmp_path: Path) -> None:
    """One binding quadrupling its time with each doubling fails the check."""
    _write_linear_sweeps(tmp_path)
    _write_sweep(tmp_path / "rust_scaling.json", _QUADRATIC)
    assert main(["--bench", "scaling", "--results-dir", str(tmp_path)]) == 1


def test_growth_at_the_bound_passes_and_past_it_fails(tmp_path: Path) -> None:
    """The bound is the factor to the power of the doublings, over the whole sweep, inclusive."""
    _write_linear_sweeps(tmp_path)
    at_bound = Seconds(MAX_DOUBLING ** (len(_SIZES) - 1))
    _write_sweep(tmp_path / "go_scaling.json", (Seconds(1.0), Seconds(1.0), at_bound))
    assert main(["--bench", "scaling", "--results-dir", str(tmp_path)]) == 0
    past_it = Seconds(at_bound * 1.01)
    _write_sweep(tmp_path / "go_scaling.json", (Seconds(1.0), Seconds(1.0), past_it))
    assert main(["--bench", "scaling", "--results-dir", str(tmp_path)]) == 1


def test_a_binding_without_a_sweep_fails(tmp_path: Path) -> None:
    """The check is required, so a binding that reported nothing fails it rather than passing."""
    _write_linear_sweeps(tmp_path)
    (tmp_path / "cpp_scaling.json").unlink()
    assert main(["--bench", "scaling", "--results-dir", str(tmp_path)]) == 1


def test_a_sweep_of_one_point_fails(tmp_path: Path) -> None:
    """One size measures no doubling."""
    _write_linear_sweeps(tmp_path)
    _write_sweep(tmp_path / "python_scaling.json", (Seconds(1.0),), (MessageCount(10000),))
    assert main(["--bench", "scaling", "--results-dir", str(tmp_path)]) == 1


def test_points_that_do_not_double_fail(tmp_path: Path) -> None:
    """The bound counts doublings, so a sweep whose sizes do not double cannot be judged by it."""
    _write_linear_sweeps(tmp_path)
    sizes = (MessageCount(2500), MessageCount(5000), MessageCount(9000))
    _write_sweep(tmp_path / "python_scaling.json", _LINEAR, sizes)
    assert main(["--bench", "scaling", "--results-dir", str(tmp_path)]) == 1
