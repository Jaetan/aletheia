# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The suite runs a C++ leg's mutants cost by file (``tools.mutation_cpp_runs``).

A mutant's run, from Mull's SQLite report, over the leg's unmutated run, from
Mull's log, summed by file: the figure the record weighs the files by.
Held here: the three shapes Mull prints a duration in and nothing else, the
baseline read rather than the warm-up run Mull prints before it, the runner's
speed divided out, a leg without a baseline refused, the legs summed to the
tenth the record keeps, and the leg writing its figures beside its
reports where the merge looks for them.
"""

from __future__ import annotations

import contextlib
import json
import sqlite3
from typing import TYPE_CHECKING, NewType
from unittest.mock import Mock

import pytest

from tools import mutation_cpp, mutation_cpp_config
from tools._common import RelPath
from tools.mutation_cpp_legs import CPP_STAGE_ENV, CppLeg
from tools.mutation_cpp_runs import (
    CPP_LEG_RUNS_SUFFIX,
    MullDuration,
    MullLog,
    RunSeconds,
    baseline_seconds,
    lane_runs,
    leg_runs,
    mull_seconds,
)
from tools.mutation_cpp_slices import SuiteRuns

if TYPE_CHECKING:
    from collections.abc import Sequence
    from pathlib import Path

    from tools.mutation_cpp_slices import FileRuns
    from tools.mutation_report import MutationReport

# How long one mutant's run took, in the milliseconds Mull's SQLite report keeps.
Millis = NewType("Millis", int)

# A mutant's site and its run, as Mull's SQLite report keeps them.
type MutantRow = tuple[Path, Millis]

_A = RelPath("cpp/src/a.cpp")
_B = RelPath("cpp/include/aletheia/b.hpp")


def _log(warm_up: MullDuration, baseline: MullDuration) -> MullLog:
    """Spell the part of mull-runner-23's log that times the unmutated runs."""
    done = "       [################################]"
    return MullLog(
        "\n".join(
            [
                "[info] Warm up run (threads: 1)",
                "",
                f"{done} 1/1. Finished in {warm_up}",
                "[info] Applying file path filter (threads: 4)",
                "",
                f"{done} 9/9. Finished in 6ms",
                "[info] Baseline run (threads: 1)",
                "",
                f"{done} 1/1. Finished in {baseline}",
                "[info] Running mutants (threads: 4)",
                "",
            ]
        )
    )


def _report(path: Path, rows: Sequence[MutantRow]) -> Path:
    """Write a SQLite report holding the mutants given, as Mull lays its table out."""
    # closing() closes the connection; sqlite3's own context manager only
    # commits, which would leave the file open until a collection.
    with contextlib.closing(sqlite3.connect(path)) as conn:
        _ = conn.execute("CREATE TABLE mutant (mutant_id TEXT, filename TEXT, duration INT)")
        _ = conn.executemany(
            "INSERT INTO mutant VALUES (?, ?, ?)",
            [(f"m{index}", str(site), ms) for index, (site, ms) in enumerate(rows)],
        )
        conn.commit()
    return path


@pytest.mark.parametrize(
    ("printed", "seconds"),
    [
        (MullDuration("6ms"), RunSeconds(0.006)),
        (MullDuration("10.71s"), RunSeconds(10.71)),
        (MullDuration("12m23.3s"), RunSeconds(743.3)),
        (MullDuration("1m5.0s"), RunSeconds(65.0)),
    ],
)
def test_mull_s_three_duration_shapes_read_as_seconds(
    printed: MullDuration, seconds: RunSeconds
) -> None:
    """Every shape Mull printed across the lane's logs: ms, seconds, minutes and seconds."""
    assert mull_seconds(printed) == pytest.approx(seconds)


@pytest.mark.parametrize(
    "printed", [MullDuration(text) for text in ("", "1h2m3s", "12m", "10.71", "s", "1.2.3s")]
)
def test_any_other_shape_is_no_duration(printed: MullDuration) -> None:
    """A shape Mull has not printed is refused rather than read as a guess."""
    assert mull_seconds(printed) is None


def test_the_baseline_is_read_and_not_the_warm_up_before_it() -> None:
    """Mull times the unmutated binary twice; the second run, the baseline, is the one."""
    assert baseline_seconds(_log(MullDuration("30.00s"), MullDuration("2.50s"))) == 2.5


def test_a_log_without_a_baseline_has_none() -> None:
    """A run Mull stopped before its baseline says nothing a weight could be counted in."""
    assert baseline_seconds(MullLog("[info] Warm up run (threads: 1)\n")) is None


def test_a_leg_s_mutants_cost_their_runs_over_its_baseline(tmp_path: Path) -> None:
    """Each mutant's run over the unmutated run, summed by file, its site repository-relative."""
    rows = [
        (tmp_path / _A, Millis(1000)),
        (tmp_path / _A, Millis(3000)),
        (tmp_path / _B, Millis(2000)),
    ]
    log = _log(MullDuration("9s"), MullDuration("2.00s"))
    assert leg_runs(_report(tmp_path / "leg.sqlite", rows), log) == {_A: 2.0, _B: 1.0}


def test_the_runner_s_speed_is_divided_out(tmp_path: Path) -> None:
    """A runner twice as slow takes twice as long on the baseline and on every mutant alike."""
    fast = [(tmp_path / _A, Millis(1000)), (tmp_path / _B, Millis(500))]
    slow = [(site, Millis(2 * ms)) for site, ms in fast]
    fast_log = _log(MullDuration("1s"), MullDuration("1.00s"))
    slow_log = _log(MullDuration("1s"), MullDuration("2.00s"))
    fast_runs = leg_runs(_report(tmp_path / "fast.sqlite", fast), fast_log)
    slow_runs = leg_runs(_report(tmp_path / "slow.sqlite", slow), slow_log)
    assert fast_runs == slow_runs == {_A: 1.0, _B: 0.5}


def test_a_leg_without_a_baseline_is_refused(tmp_path: Path) -> None:
    """Without the unmutated run there is no unit, and a weight in seconds would be the runner's."""
    report = _report(tmp_path / "leg.sqlite", [(tmp_path / _A, Millis(1000))])
    refusal = leg_runs(report, MullLog("[info] Warm up run (threads: 1)\n"))
    assert isinstance(refusal, str)
    assert "no baseline run" in refusal


def test_a_leg_without_its_sqlite_report_is_refused(tmp_path: Path) -> None:
    """A report Mull did not write is refused by name, and no empty one is left in its place."""
    missing = tmp_path / "leg.sqlite"
    refusal = leg_runs(missing, _log(MullDuration("9s"), MullDuration("2.00s")))
    assert isinstance(refusal, str)
    assert "wrote no leg.sqlite" in refusal
    assert not missing.exists()


def test_the_legs_sum_to_the_tenth_the_record_keeps(tmp_path: Path) -> None:
    """The slices add up file by file, rounded once at the end."""
    figures: dict[CppLeg, FileRuns] = {
        CppLeg(1): {_A: SuiteRuns(1.04), _B: SuiteRuns(0.5)},
        CppLeg(2): {_A: SuiteRuns(1.04)},
        CppLeg(3): {_B: SuiteRuns(3.0)},
    }
    for leg, runs in figures.items():
        _ = (tmp_path / f"{leg.report_name}{CPP_LEG_RUNS_SUFFIX}").write_text(json.dumps(runs))
    assert lane_runs(tmp_path, list(figures)) == {_A: 2.1, _B: 3.5}


def _no_files(_leg: CppLeg) -> tuple[list[RelPath], list[RelPath]]:
    """Stand in for the partition over the fake root, which tracks no file: nothing claimed."""
    return [], []


def _swept_leg(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, log: MullLog) -> MutationReport:
    """Run the first slice's leg through the lane over a faked root, its build and runner faked.

    The runner's reports are laid down first, as Mull would have left them,
    one mutant in a.cpp costing four seconds.
    """
    root = tmp_path / "repo"
    (root / "cpp").mkdir(parents=True)
    _ = (root / "cpp" / "mull.yml").write_text("mutators:\n  - cxx_add_to_sub\n", encoding="utf-8")
    for module in (mutation_cpp, mutation_cpp_config):
        monkeypatch.setattr(module, "REPO_ROOT", root)
    # The slice's files are partitioned over the tracked tree, which the fake
    # root is not; the leg claims nothing and holds nothing out.
    monkeypatch.setattr(mutation_cpp_config, "leg_files", _no_files)
    leg = CppLeg(1)
    artifact_dir = tmp_path / "out"
    artifact_dir.mkdir()
    _ = (artifact_dir / f"{leg.report_name}.json").write_text(json.dumps({"files": {}}))
    _ = _report(artifact_dir / f"{leg.report_name}.sqlite", [(tmp_path / _A, Millis(4000))])
    monkeypatch.setenv(CPP_STAGE_ENV, "1")
    monkeypatch.setattr(mutation_cpp, "_check_cpp_tools", lambda: ("cmake", "mull-runner-23"))
    monkeypatch.setattr(mutation_cpp, "build_cpp_mutation_tree", Mock(return_value=""))
    monkeypatch.setattr(mutation_cpp, "_run_cpp_lane", Mock(return_value=(log, (1, 0))))
    return mutation_cpp.run_cpp(artifact_dir)


def test_a_leg_writes_its_runs_beside_its_reports(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The leg is the one place its baseline is printed, so it is the one that counts its runs."""
    report = _swept_leg(monkeypatch, tmp_path, _log(MullDuration("9s"), MullDuration("2.00s")))
    assert report.error is None
    written = tmp_path / "out" / f"{CppLeg(1).report_name}{CPP_LEG_RUNS_SUFFIX}"
    assert json.loads(written.read_text(encoding="utf-8")) == {_A: 2.0}


def test_a_leg_whose_log_has_no_baseline_is_an_error(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A leg that cannot count its runs fails where it ran, not at a merge missing its file."""
    report = _swept_leg(monkeypatch, tmp_path, MullLog("no timing here\n"))
    leg = CppLeg(1)
    assert report.error is not None
    assert f"the {leg} leg: mull-runner-23 printed no baseline run" in report.error
    assert not (tmp_path / "out" / f"{leg.report_name}{CPP_LEG_RUNS_SUFFIX}").exists()
