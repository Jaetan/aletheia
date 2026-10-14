# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Agda interface-reuse gate passes a checker judging by hashes and refuses one judging by date.

``tools/check_agda_interface_reuse.py`` checks a module three times in a copy
of the project's sources when the Agda release moves.  Agda is replaced here by
a stand-in written in the test, which checks a module whose interface is
missing and, in its wrong mode, one whose interface is older than its source,
writing the interface back as Agda does.  Each of the gate's refusals and each
way it cannot reach the fact is shown on the stand-in, without starting Agda.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from typing import TYPE_CHECKING, NewType

import pytest
from _processes import CommandWord

from tools import check_agda_interface_reuse
from tools._common import RelPath
from tools.check_agda_interface_reuse import (
    IMPORTED,
    MODULE,
    AgdaVersion,
    CheckerLog,
    ModuleCount,
    interface_of,
    rechecked,
    reuse_refusals,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path

    from tools.pin_scope import PinGate

# Which of the gate's three runs of the checker, counted from 1.
RunOrdinal = NewType("RunOrdinal", int)

_AGDA = CommandWord("/opt/agda/bin/agda")
_VERSION = AgdaVersion("2.8.0")
# The tracked files the gate copies: the library file, the module, the one it
# imports, and a sibling, so a directory receives two files.
_SOURCES = (
    RelPath("aletheia.agda-lib"),
    RelPath("src/Aletheia/Data/Dec0.agda"),
    RelPath("src/Aletheia/Data/Dec0/Nat.agda"),
    RelPath("src/Aletheia/Data/Other.agda"),
)
# What a failing run prints, longer than the part of it the gate shows.
_FAILURE_TEXT = "x" * 3000 + "the checker's last words"
_LONG_FAILURE = Prose(_FAILURE_TEXT)


@dataclass(kw_only=True)
class _Checker:
    """Answers the gate's calls as Agda does, judging an interface by hash or, wrongly, by date."""

    by_date: bool = False
    failing: RunOrdinal | None = None
    writing_nothing: RunOrdinal | None = None
    runs: RunOrdinal = RunOrdinal(0)

    def answer(
        self, cmd: list[CommandWord], *, cwd: Path | None = None, check: bool = False
    ) -> subprocess.CompletedProcess[Prose]:
        """Answer one call: the release asked for, or a check of the module."""
        if cmd == [_AGDA, "--numeric-version"]:
            assert check
            return subprocess.CompletedProcess(cmd, 0, Prose(f"{_VERSION}\n"), Prose(""))
        assert cmd == [_AGDA, "+RTS", "-M16G", "-RTS", MODULE]
        assert cwd is not None
        self.runs = RunOrdinal(self.runs + 1)
        if self.runs == self.failing:
            return subprocess.CompletedProcess(cmd, 1, _LONG_FAILURE, Prose(""))
        printed: list[Prose] = []
        for source in (IMPORTED, MODULE):
            interface = cwd / interface_of(source, _VERSION)
            stale = not interface.exists() or (
                self.by_date and interface.stat().st_mtime < (cwd / source).stat().st_mtime
            )
            if stale:
                printed.append(Prose(f" Checking {source} ({cwd / source})."))
                if self.runs != self.writing_nothing:
                    interface.parent.mkdir(parents=True, exist_ok=True)
                    _ = interface.write_text("interface", encoding="utf-8")
        return subprocess.CompletedProcess(cmd, 0, Prose("\n".join(printed)), Prose(""))


def _tree(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, checker: _Checker) -> Path:
    """Return a repository holding the gate's sources, with ``checker`` standing in for Agda."""
    repo = tmp_path / "repo"
    for relative in _SOURCES:
        (repo / relative).parent.mkdir(parents=True, exist_ok=True)
        _ = (repo / relative).write_text(f"-- {relative}\n", encoding="utf-8")

    def tracked(root: Path, *patterns: RelPath) -> list[RelPath]:
        assert root == repo
        assert patterns == ("src", "aletheia.agda-lib")
        return list(_SOURCES)

    def agda(name: CommandWord) -> CommandWord:
        assert name == "agda"
        return _AGDA

    monkeypatch.setattr(check_agda_interface_reuse, "git_ls_files", tracked)
    monkeypatch.setattr(check_agda_interface_reuse, "find_executable", agda)
    monkeypatch.setattr(check_agda_interface_reuse, "run_capture", checker.answer)
    return repo


def _said(capsys: pytest.CaptureFixture[Prose]) -> list[Prose]:
    """Return the lines the gate printed."""
    return [Prose(line) for line in capsys.readouterr().out.splitlines()]


def test_a_checker_judging_by_hashes_passes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Interfaces reused whatever their date and only the deleted one rebuilt is the fact."""
    checker = _Checker()
    repo = _tree(tmp_path, monkeypatch, checker)
    assert check_agda_interface_reuse.check(repo) == ExitStatus(0)
    assert checker.runs == 3
    assert _said(capsys) == []
    assert not (repo / "_build").exists()


def test_a_checker_judging_by_date_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Interfaces older than their sources re-checked is the defect the gate is for."""
    repo = _tree(tmp_path, monkeypatch, _Checker(by_date=True))
    assert check_agda_interface_reuse.check(repo) == ExitStatus(1)
    assert _said(capsys) == [
        Prose(
            "check-agda-interface-reuse: every interface older than its source,"
            + " 2 modules re-checked"
        )
    ]


def test_a_deleted_interface_not_written_back_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The re-check of the module whose interface went writes it again."""
    repo = _tree(tmp_path, monkeypatch, _Checker(writing_nothing=RunOrdinal(3)))
    assert check_agda_interface_reuse.check(repo) == ExitStatus(1)
    assert _said(capsys) == [
        Prose(f"check-agda-interface-reuse: the check wrote no interface back for {IMPORTED}")
    ]


def test_a_first_check_writing_no_interface_cannot_reach_the_fact(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no interface to redate or delete, the gate exits 2 and runs no further."""
    checker = _Checker(writing_nothing=RunOrdinal(1))
    repo = _tree(tmp_path, monkeypatch, checker)
    assert check_agda_interface_reuse.check(repo) == ExitStatus(2)
    assert checker.runs == 1
    assert _said(capsys) == [
        Prose(f"check-agda-interface-reuse: checking {MODULE} wrote no Dec0.agdai")
    ]


@pytest.mark.parametrize("failing", [RunOrdinal(1), RunOrdinal(2), RunOrdinal(3)])
def test_a_failing_run_cannot_reach_the_fact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    failing: RunOrdinal,
) -> None:
    """Any of the three runs failing exits 2 with the end of what it printed, and stops there."""
    checker = _Checker(failing=failing)
    repo = _tree(tmp_path, monkeypatch, checker)
    assert check_agda_interface_reuse.check(repo) == ExitStatus(2)
    assert checker.runs == failing
    assert capsys.readouterr().out == (
        f"check-agda-interface-reuse: agda exited 1:\n{_FAILURE_TEXT[-2000:]}\n"
    )


def test_only_a_checking_line_counts_as_a_re_check() -> None:
    """A module loaded from its interface prints no ``Checking`` line."""
    log = CheckerLog(
        " Checking Aletheia.Data.Dec0 (/p/src/Aletheia/Data/Dec0.agda).\n"
        + "  Checking Aletheia.Data.Dec0.Nat (/p/src/Aletheia/Data/Dec0/Nat.agda).\n"
        + "Loading Aletheia.Prelude\nFinished Checking.\n"
    )
    assert rechecked(log) == ModuleCount(2)
    assert rechecked(CheckerLog("")) == ModuleCount(0)


def test_more_or_fewer_than_the_deleted_one_is_refused() -> None:
    """Deleting one interface re-checks exactly that one, neither its importers nor none."""
    for count in (ModuleCount(0), ModuleCount(2)):
        assert reuse_refusals(ModuleCount(0), count, written_back=True) == [
            Prose(f"one imported interface deleted, {count} modules re-checked, not 1")
        ]


def test_an_interface_lives_under_the_release_s_directory() -> None:
    """Agda keeps a source's interface beside the project, under its own release."""
    assert interface_of(RelPath("src/A/B.agda"), AgdaVersion("2.8.0")) == RelPath(
        "_build/2.8.0/agda/src/A/B.agdai"
    )


def test_without_agda_the_gate_cannot_reach_its_fact(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """No agda on the search path exits 2 rather than passing."""
    monkeypatch.setenv("PATH", str(tmp_path))
    assert check_agda_interface_reuse.check(tmp_path) == ExitStatus(2)
    assert _said(capsys) == [
        Prose("check-agda-interface-reuse: required executable not found on PATH: agda")
    ]


def _in_scope(*, answer: bool) -> Callable[[PinGate, Path], bool]:
    """Return a stand-in for the scope question answering ``answer``."""

    def gate_runs(_gate: PinGate, _root: Path) -> bool:
        return answer

    return gate_runs


@pytest.mark.parametrize("in_scope", [True, False])
def test_the_gate_checks_only_when_the_fact_s_pin_moved(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, *, in_scope: bool
) -> None:
    """In scope the gate's verdict is the check's; out of scope it passes without Agda."""
    checked: list[Path] = []

    def the_tree() -> Path:
        return tmp_path

    def refusing(root: Path) -> ExitStatus:
        checked.append(root)
        return ExitStatus(1)

    monkeypatch.setattr(check_agda_interface_reuse, "git_toplevel", the_tree)
    monkeypatch.setattr(check_agda_interface_reuse, "gate_runs", _in_scope(answer=in_scope))
    monkeypatch.setattr(check_agda_interface_reuse, "check", refusing)
    monkeypatch.setattr("sys.argv", ["check_agda_interface_reuse"])
    assert check_agda_interface_reuse.main() == ExitStatus(1 if in_scope else 0)
    assert checked == ([tmp_path] if in_scope else [])


def test_the_gate_refuses_an_argument_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An argument the gate does not take stops it before it reads anything."""
    monkeypatch.setattr("sys.argv", ["check_agda_interface_reuse", "--unknown"])
    with pytest.raises(SystemExit) as stopped:
        _ = check_agda_interface_reuse.main()
    assert stopped.value.code == 2
