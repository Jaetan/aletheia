# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the Go lane's reading of gremlins and the not-covered gate.

gremlins puts every mutant in one bucket, and the ones on lines no test
executes are a coverage gap the lane records rather than a survivor it
refuses.  What is held here: the summary is read whole, the not-covered
mutants are keyed on their source lines, and the verdict refuses a run with
more of them than the record or with one the ledger does not name, and a
record the run has outgrown: fewer of them, or a recorded row the run no
longer produces.  And the
sweep itself: gremlins runs in a copy of the tree as it stands, handed the
copy as the repository, the tree's own kernel, the copy's configuration file
by name and none of the caller's gremlins settings, and the doc-example harness
skipped.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Literal, cast

import pytest
from _scratch_copies import install as install_copies
from _stand_in import ScriptSource, ToolName, install_stand_in

from tools import mutation_run
from tools._common import EnvName, EnvValue
from tools.mutation_go import GO_CONFIG, GremlinsLog, without_gremlins_settings
from tools.mutation_report import MutantCount, MutationReport, Observed, load_spec

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

    from _processes import CommandWord

    from tools.mutation_report import BindingSpec, DriftStatus

_SUMMARY = """\
      NOT COVERED ARITHMETIC_BASE at limits.go:3:23
      NOT COVERED ARITHMETIC_BASE at limits.go:3:30
      NOT COVERED CONDITIONALS_NEGATION at renderer.go:2:16
      KILLED CONDITIONALS_NEGATION at yaml.go:313:9
       LIVED CONDITIONALS_BOUNDARY at renderer.go:2:16

Mutation testing completed in 2 minutes 11 seconds
Killed: 721, Lived: 1, Not covered: 3
Timed out: 2, Not viable: 0, Skipped: 0
Test efficacy: 100.00%
Mutator coverage: 94.87%
"""


def _tree(tmp_path: Path) -> Path:
    package = tmp_path / "go" / "aletheia"
    package.mkdir(parents=True)
    _ = (package / "limits.go").write_text(
        "package aletheia\n\n\tMaxJSONBytes = 64 * 1024 * 1024\n"
    )
    _ = (package / "renderer.go").write_text('package aletheia\n\tif registered != "" {\n')
    return tmp_path


def _spec(**baseline: object) -> dict[str, BindingSpec]:
    return {"go": cast("BindingSpec", {"baseline": {"survivors": 0, **baseline}})}


def _report() -> MutationReport:
    return MutationReport("go", "gremlins", 721, 0, _SUMMARY, observed=Observed(timeouts=2))


def _rows(count: int) -> dict[mutation_run.SurvivorKey, int]:
    return {("ARITHMETIC_BASE", "go/aletheia/limits.go", f"line {i}"): 1 for i in range(count)}


def test_the_summary_is_read_whole(tmp_path: Path) -> None:
    """Killed, lived and timed out are read from the tail; not covered from the mutant lines.

    Every mutant gremlins made is the sum of its six buckets, the not viable and
    the skipped included, which no other count reads.
    """
    rep = mutation_run.parse_gremlins_summary(GremlinsLog(_SUMMARY), Prose("here"))
    assert (rep.killed, rep.survived, rep.observed.timeouts) == (721, 1, 2)
    assert rep.observed.generated == 721 + 1 + 3 + 2
    odd = _SUMMARY.replace("Not viable: 0, Skipped: 0", "Not viable: 4, Skipped: 5")
    reread = mutation_run.parse_gremlins_summary(GremlinsLog(odd), Prose("here"))
    assert reread.observed.generated == 736
    assert sum(mutation_run.go_mutant_rows(_SUMMARY, "NOT COVERED", _tree(tmp_path)).values()) == 3


def test_not_covered_mutants_are_keyed_on_their_source_lines(tmp_path: Path) -> None:
    """A position becomes the text of the line it names, read from the tree."""
    rows = mutation_run.go_mutant_rows(_SUMMARY, "NOT COVERED", _tree(tmp_path))
    assert rows == {
        ("ARITHMETIC_BASE", "go/aletheia/limits.go", "MaxJSONBytes = 64 * 1024 * 1024"): 2,
        ("CONDITIONALS_NEGATION", "go/aletheia/renderer.go", 'if registered != "" {'): 1,
    }


def test_survivors_are_keyed_on_their_source_lines_apart_from_the_uncovered(
    tmp_path: Path,
) -> None:
    """A LIVED line is a survivor row; a not-covered line on the same source is not one."""
    rows = mutation_run.go_mutant_rows(_SUMMARY, "LIVED", _tree(tmp_path))
    assert rows == {
        ("CONDITIONALS_BOUNDARY", "go/aletheia/renderer.go", 'if registered != "" {'): 1
    }


def test_a_position_the_tree_cannot_name_keeps_the_position(tmp_path: Path) -> None:
    """A missing file or a line past the end still yields a row, one no ledger names."""
    rows = mutation_run.go_mutant_rows(
        "NOT COVERED X at gone.go:4:1\nNOT COVERED Y at limits.go:99:1\n",
        "NOT COVERED",
        _tree(tmp_path),
    )
    assert rows == {
        ("X", "go/aletheia/gone.go", "line 4"): 1,
        ("Y", "go/aletheia/limits.go", "line 99"): 1,
    }


def test_more_not_covered_than_recorded_is_a_regression() -> None:
    """A line that lost its test raises the count past the record."""
    entry = mutation_run.drift_for(_report(), _spec(not_covered=3), not_covered_rows=_rows(4))
    assert entry["status"] == "regression"
    assert (entry.get("observed_not_covered"), entry.get("baseline_not_covered")) == (4, 3)
    entry = mutation_run.drift_for(_report(), _spec(not_covered=3), not_covered_rows=_rows(3))
    assert entry["status"] == "ok"


def test_fewer_not_covered_than_recorded_is_a_stale_record() -> None:
    """A line that gained a test lowers the record in the change that wrote the test."""
    entry = mutation_run.drift_for(_report(), _spec(not_covered=3), not_covered_rows=_rows(2))
    assert entry["status"] == "stale"
    assert (entry.get("observed_not_covered"), entry.get("baseline_not_covered")) == (2, 3)


def test_a_record_without_the_count_holds_nothing() -> None:
    """A record that carries no count, or a tool that reports no rows, is not held."""
    assert mutation_run.drift_for(_report(), _spec(), not_covered_rows=_rows(9))["status"] == "ok"
    assert mutation_run.drift_for(_report(), _spec(not_covered=0))["status"] == "ok"


def test_a_not_covered_row_the_ledger_does_not_name_fails(tmp_path: Path) -> None:
    """At an unchanged count, a mutant traded for another is still a lost test."""
    rows = mutation_run.go_mutant_rows(_SUMMARY, "NOT COVERED", _tree(tmp_path))
    ledger = [
        {
            "mutator": "ARITHMETIC_BASE",
            "file": "go/aletheia/limits.go",
            "text": "MaxJSONBytes = 64 * 1024 * 1024",
            "count": 2,
        },
        {
            "mutator": "CONDITIONALS_NEGATION",
            "file": "go/aletheia/other.go",
            "text": "if x {",
            "count": 1,
        },
    ]
    entry = mutation_run.drift_for(
        _report(), _spec(not_covered=3, not_covered_ledger=ledger), not_covered_rows=rows
    )
    assert entry["status"] == "regression"
    assert entry.get("unrecorded_not_covered") == [
        {
            "mutator": "CONDITIONALS_NEGATION",
            "file": "go/aletheia/renderer.go",
            "text": 'if registered != "" {',
            "count": 1,
        }
    ]
    assert entry.get("stale_not_covered_ledger") == [ledger[1]]


def test_a_recorded_row_the_run_no_longer_produces_is_a_stale_record(tmp_path: Path) -> None:
    """A line that gained a test fails the lane until the change deletes its row."""
    rows = mutation_run.go_mutant_rows(_SUMMARY, "NOT COVERED", _tree(tmp_path))
    ledger = [
        *mutation_run.rows_to_ledger(rows),
        {"mutator": "Z", "file": "go/aletheia/limits.go", "text": "gone", "count": 1},
    ]
    entry = mutation_run.drift_for(
        _report(), _spec(not_covered=3, not_covered_ledger=ledger), not_covered_rows=rows
    )
    assert entry["status"] == "stale"
    assert entry.get("stale_not_covered_ledger") == [ledger[-1]]
    assert "unrecorded_not_covered" not in entry


def test_the_timeout_ceiling_is_read_before_the_count() -> None:
    """A run that timed out on nearly everything is refused whatever else it reports."""
    rep = MutationReport("go", "gremlins", 25, 0, "", observed=Observed(timeouts=632))
    entry = mutation_run.drift_for(
        rep, _spec(timeout_ceiling=50, not_covered=0), not_covered_rows={}
    )
    assert entry["status"] == "regression"
    assert entry.get("observed_timeouts") == 632


def test_the_recorded_timed_out_run_is_refused() -> None:
    """The run that showed the defect: 39 killed, 622 timed out, and no survivor reported.

    A mutant gremlins could not finish is neither killed nor lived, so the
    run reads as clean and fully efficacious on its counts alone.
    """
    tail = "Killed: 39, Lived: 0, Not covered: 102\nTimed out: 622, Not viable: 0, Skipped: 0\n"
    rep = mutation_run.parse_gremlins_summary(GremlinsLog(tail), Prose("recorded"))
    entry = mutation_run.drift_for(rep, _spec(timeout_ceiling=0, total_mutants=39))
    assert entry["status"] == "regression"
    assert entry.get("observed_timeouts") == 622


@pytest.mark.parametrize(
    ("timeouts", "status"), [(MutantCount(3), "regression"), (MutantCount(2), "ok")]
)
def test_the_ceiling_is_the_edge(timeouts: MutantCount, status: DriftStatus) -> None:
    """One timeout past the ceiling is refused; a run at it that matches the record is taken."""
    rep = MutationReport("go", "gremlins", 721, 0, _SUMMARY, observed=Observed(timeouts=timeouts))
    assert mutation_run.drift_for(rep, _spec(timeout_ceiling=2))["status"] == status


def test_the_record_s_own_figures_pass_the_gate_they_record() -> None:
    """The Go baseline, spelled as the tail gremlins prints, is a run the lane takes."""
    record = load_spec().get("bindings", {}).get("go", {}).get("baseline", {})
    tail = (
        f"Killed: {record.get('total_mutants', 0) - record.get('survivors', 0)}, "
        + f"Lived: {record.get('survivors', 0)}, Not covered: {record.get('not_covered', 0)}\n"
        + "Timed out: 0, Not viable: 0, Skipped: 0\n"
    )
    rep = mutation_run.parse_gremlins_summary(GremlinsLog(tail), Prose("the record"))
    assert mutation_run.drift_for(rep, load_spec().get("bindings", {}))["status"] == "ok"


# The variables the lane sets for gremlins.
type _LaneVariable = Literal["ALETHEIA_REPO_ROOT", "ALETHEIA_LIB", "GOFLAGS"]
_LANE_VARIABLES: tuple[_LaneVariable, ...] = ("ALETHEIA_REPO_ROOT", "ALETHEIA_LIB", "GOFLAGS")

# The summary a sweep ends with: one mutant, killed.
_SWEPT = GremlinsLog(
    "Killed: 1, Lived: 0, Not covered: 0\nTimed out: 0, Not viable: 0, Skipped: 0\n"
)

# What the search path finds as gremlins, so the lane's lookup succeeds; the
# sweep itself runs in-process (``_Gremlins``), and this fails if it is run.
_NEVER_RUNS = ScriptSource("raise SystemExit('the stand-in never runs')")


@dataclass(frozen=True)
class _Sweep:
    """What the lane handed gremlins: its command, directory and variables, and the source there."""

    argv: list[CommandWord]
    cwd: Path
    env: dict[_LaneVariable, Prose | None]
    names: frozenset[Prose]
    source: Prose


@dataclass
class _Gremlins:
    """A stand-in for the lane's ``run_streaming`` of gremlins: it records each sweep."""

    sweeps: list[_Sweep] = field(default_factory=list[_Sweep])

    def __call__(
        self, cmd: list[CommandWord], *, cwd: Path, env: dict[Prose, Prose]
    ) -> subprocess.CompletedProcess[GremlinsLog]:
        """Record the sweep, reading the source while the copy exists, and print its summary."""
        self.sweeps.append(
            _Sweep(
                cmd,
                cwd,
                {name: env.get(Prose(name)) for name in _LANE_VARIABLES},
                frozenset(env),
                Prose((cwd / "aletheia" / "client.go").read_text(encoding="utf-8")),
            )
        )
        return subprocess.CompletedProcess(cmd, 0, _SWEPT, GremlinsLog(""))


def _go_repo(root: Path) -> Path:
    """Plant a tree whose Go source reads as edited, with a built kernel."""
    source = root / "go" / "aletheia" / "client.go"
    source.parent.mkdir(parents=True)
    _ = source.write_text("uncommitted edit\n", encoding="utf-8")
    (root / "build").mkdir()
    _ = (root / "build" / "libaletheia-ffi.so").write_bytes(b"")
    return root.resolve()


def _fake_gremlins(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> _Gremlins:
    """Let the lane find gremlins on the search path and sweep through the in-process stand-in."""
    install_stand_in(tmp_path, monkeypatch, ToolName("gremlins"), _NEVER_RUNS)
    gremlins = _Gremlins()
    monkeypatch.setattr(mutation_run, "run_streaming", gremlins)
    return gremlins


def test_the_sweep_runs_in_a_copy_named_as_the_repository(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The tool runs in the copy's go/, the copy is the repository, the kernel is the tree's."""
    repo = _go_repo(tmp_path / "repo")
    gremlins = _fake_gremlins(tmp_path, monkeypatch)
    copies = install_copies(monkeypatch, tmp_path / "copies")
    monkeypatch.setenv("GOFLAGS", "-mod=mod")
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    report = mutation_run.run_go(tmp_path)
    assert report.error is None
    assert (report.killed, report.survived) == (1, 0)
    assert copies.asked == [repo]
    [copy] = copies.made
    [seen] = gremlins.sweeps
    ran_in = seen.cwd
    assert ran_in == copy / "go"
    assert ran_in.name == "go"
    assert not ran_in.is_relative_to(repo)
    assert not ran_in.exists()
    assert not copy.exists()
    assert seen.argv == [
        str(tmp_path / "bin" / "gremlins"),
        "unleash",
        "--config",
        str(copy / GO_CONFIG),
        "./aletheia",
    ]
    assert seen.source == "uncommitted edit\n"
    assert seen.env == {
        "ALETHEIA_REPO_ROOT": str(copy),
        "ALETHEIA_LIB": str(repo / "build" / "libaletheia-ffi.so"),
        "GOFLAGS": "-mod=mod -count=1 -skip=^TestDocExamples$",
    }


def test_no_variable_gremlins_reads_a_setting_from_reaches_the_sweep(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The caller's ``GREMLINS_`` variables are dropped, and every other variable is kept.

    gremlins reads a setting from ``GREMLINS_<KEY>`` ahead of the configuration
    file, and any non-empty value of a mutator's ``ENABLED`` key, ``true``
    included, turns that kind off; the tests gremlins runs read the rest of
    the environment as the caller set it.
    """
    repo = _go_repo(tmp_path / "repo")
    gremlins = _fake_gremlins(tmp_path, monkeypatch)
    _ = install_copies(monkeypatch, tmp_path / "copies")
    monkeypatch.setenv("GREMLINS_MUTANTS_INVERT_LOGICAL_ENABLED", "true")
    monkeypatch.setenv("GREMLINS_UNLEASH_TIMEOUT_COEFFICIENT", "3")
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    report = mutation_run.run_go(tmp_path)
    assert report.error is None
    [seen] = gremlins.sweeps
    assert not {name for name in seen.names if name.startswith("GREMLINS_")}
    assert "PATH" in seen.names


def test_a_variable_is_dropped_only_where_it_names_a_gremlins_setting() -> None:
    """A setting's variable is ``GREMLINS_`` and the key; a name only beginning alike is kept."""
    caller = {
        EnvName(name): EnvValue(value)
        for name, value in (
            ("GREMLINS_MUTANTS_INVERT_LOGICAL_ENABLED", "true"),
            ("GREMLINS_SILENT", "1"),
            ("GREMLINS", "kept"),
            ("GREMLINSNOT_A_SETTING", "kept"),
            ("PATH", "/usr/bin"),
        )
    }
    assert without_gremlins_settings(caller) == {
        "GREMLINS": "kept",
        "GREMLINSNOT_A_SETTING": "kept",
        "PATH": "/usr/bin",
    }


def test_the_sweep_s_flags_are_the_whole_goflags_when_none_was_set() -> None:
    """With no GOFLAGS of the caller's, caching off and the harness's skip are all there is."""
    assert (
        mutation_run.go_sweep_goflags(mutation_run.GoFlags(""))
        == "-count=1 -skip=^TestDocExamples$"
    )


def test_no_go_test_run_of_the_sweep_is_served_from_the_test_cache() -> None:
    """The coverage run gremlins sets every mutant's limit from is measured, not served.

    A cached coverage run times the cache, not the tests, so a limit set at a
    multiple of it bears no relation to how long a mutant's tests take.
    """
    flags = str(mutation_run.go_sweep_goflags(mutation_run.GoFlags("-mod=mod"))).split()
    assert "-count=1" in flags


def test_a_tree_without_a_kernel_is_a_refusal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """With no built library there is no sweep: the report says why, and the tool never ran."""
    repo = _go_repo(tmp_path / "repo")
    lib = repo / "build" / "libaletheia-ffi.so"
    lib.unlink()
    gremlins = _fake_gremlins(tmp_path, monkeypatch)
    copies = install_copies(monkeypatch, tmp_path / "copies")
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    report = mutation_run.run_go(tmp_path)
    assert report.error is not None
    assert report.error.startswith("libaletheia-ffi.so not found")
    assert report.error == (
        f"libaletheia-ffi.so not found at {lib}; run `cabal run shake -- build` first"
    )
    assert not gremlins.sweeps
    assert not copies.asked
