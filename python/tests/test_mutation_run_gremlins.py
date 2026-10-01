# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the Go lane's reading of gremlins and the not-covered gate.

gremlins puts every mutant in one bucket, and the ones on lines no test
executes are a coverage gap the lane records rather than a survivor it
refuses.  What is held here: the summary is read whole, the not-covered
mutants are keyed on their source lines, and the verdict refuses a run with
more of them than the record or with one the ledger does not name, while a
recorded row the run no longer produces is reported and passes.  And the
sweep itself: gremlins runs in a copy of the tree as it stands, handed the
copy as the repository, the tree's own kernel, and the doc-example harness
skipped.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import TYPE_CHECKING, cast

from _git_repo import repo_with_an_uncommitted_edit

from tools import mutation_run
from tools.mutation_report import MutationReport

if TYPE_CHECKING:
    import pytest

    from tools.mutation_report import BindingSpec

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
    return MutationReport("go", "gremlins", 721, 0, _SUMMARY, timeouts=2)


def _rows(count: int) -> dict[mutation_run.SurvivorKey, int]:
    return {("ARITHMETIC_BASE", "go/aletheia/limits.go", f"line {i}"): 1 for i in range(count)}


def test_the_summary_is_read_whole(tmp_path: Path) -> None:
    """Killed, lived and timed out are read from the tail; not covered from the mutant lines."""
    rep = mutation_run.parse_gremlins_summary(_SUMMARY, "here")
    assert (rep.killed, rep.survived, rep.timeouts) == (721, 1, 2)
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
    for count in (3, 2):
        entry = mutation_run.drift_for(
            _report(), _spec(not_covered=3), not_covered_rows=_rows(count)
        )
        assert entry["status"] == "ok"


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


def test_a_recorded_row_the_run_no_longer_produces_is_stale_and_passes(tmp_path: Path) -> None:
    """A line that gained a test lowers the record, which the change makes."""
    rows = mutation_run.go_mutant_rows(_SUMMARY, "NOT COVERED", _tree(tmp_path))
    ledger = [
        *mutation_run.rows_to_ledger(rows),
        {"mutator": "Z", "file": "go/aletheia/limits.go", "text": "gone", "count": 1},
    ]
    entry = mutation_run.drift_for(
        _report(), _spec(not_covered=4, not_covered_ledger=ledger), not_covered_rows=rows
    )
    assert entry["status"] == "ok"
    assert entry.get("stale_not_covered_ledger") == [ledger[-1]]
    assert "unrecorded_not_covered" not in entry


def test_the_timeout_ceiling_is_read_before_the_count() -> None:
    """A run that timed out on nearly everything is refused whatever else it reports."""
    rep = MutationReport("go", "gremlins", 25, 0, "", timeouts=632)
    entry = mutation_run.drift_for(
        rep, _spec(timeout_ceiling=50, not_covered=0), not_covered_rows={}
    )
    assert entry["status"] == "regression"
    assert entry.get("observed_timeouts") == 632


# A stand-in for gremlins: it records the directory it ran in, its arguments,
# the variables the lane sets and the source it found there, then prints the
# summary a sweep ends with.
_FAKE_GREMLINS = """\
import json
import os
import sys
from pathlib import Path

names = ("ALETHEIA_REPO_ROOT", "ALETHEIA_LIB", "GOFLAGS")
seen = {
    "cwd": str(Path.cwd()),
    "argv": sys.argv[1:],
    "env": {name: os.environ.get(name) for name in names},
    "source": (Path.cwd() / "aletheia" / "client.go").read_text(encoding="utf-8"),
}
_ = Path(os.environ["GREMLINS_RECORD"]).write_text(json.dumps(seen), encoding="utf-8")
print("Killed: 1, Lived: 0, Not covered: 0")
print("Timed out: 0, Not viable: 0, Skipped: 0")
"""


def _go_repo(root: Path) -> Path:
    """Build a repository with a committed Go source, edited and not committed, and a kernel."""
    repo = repo_with_an_uncommitted_edit(root, Path("go/aletheia/client.go"))
    (repo / "build").mkdir()
    _ = (repo / "build" / "libaletheia-ffi.so").write_bytes(b"")
    return repo


def _fake_gremlins(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Put the stand-in first on the search path and return the file it records to."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    gremlins = bin_dir / "gremlins"
    _ = gremlins.write_text(f"#!{sys.executable}\n{_FAKE_GREMLINS}", encoding="utf-8")
    gremlins.chmod(0o755)
    record = tmp_path / "gremlins.json"
    monkeypatch.setenv("PATH", f"{bin_dir}:{os.environ['PATH']}")
    monkeypatch.setenv("GREMLINS_RECORD", str(record))
    return record


def test_the_sweep_runs_in_a_copy_named_as_the_repository(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The tool runs in the copy's go/, the copy is the repository, the kernel is the tree's."""
    repo = _go_repo(tmp_path / "repo")
    record = _fake_gremlins(tmp_path, monkeypatch)
    monkeypatch.setenv("GOFLAGS", "-mod=mod")
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    report = mutation_run.run_go(tmp_path)
    assert report.error is None
    assert (report.killed, report.survived) == (1, 0)
    seen = json.loads(record.read_text(encoding="utf-8"))
    ran_in = Path(seen["cwd"])
    assert ran_in.name == "go"
    assert not ran_in.is_relative_to(repo)
    assert not ran_in.exists()
    assert seen["argv"] == ["unleash", "./aletheia"]
    assert seen["source"] == "uncommitted edit\n"
    assert seen["env"] == {
        "ALETHEIA_REPO_ROOT": str(ran_in.parent),
        "ALETHEIA_LIB": str(repo / "build" / "libaletheia-ffi.so"),
        "GOFLAGS": "-mod=mod -skip=^TestDocExamples$",
    }


def test_the_skip_is_the_whole_goflags_when_none_was_set() -> None:
    """With no GOFLAGS of the caller's, the harness's skip is all there is."""
    assert mutation_run.go_sweep_goflags(mutation_run.GoFlags("")) == "-skip=^TestDocExamples$"


def test_a_tree_without_a_kernel_is_a_refusal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """With no built library there is no sweep: the report says why, and the tool never ran."""
    repo = _go_repo(tmp_path / "repo")
    (repo / "build" / "libaletheia-ffi.so").unlink()
    record = _fake_gremlins(tmp_path, monkeypatch)
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    report = mutation_run.run_go(tmp_path)
    assert report.error is not None
    assert report.error.startswith("libaletheia-ffi.so not found")
    assert not record.exists()
