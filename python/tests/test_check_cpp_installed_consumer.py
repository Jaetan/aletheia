# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The installed-consumer gate: when it runs, and that it runs every program it builds."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType

from tools import check_cpp_installed_consumer as gate
from tools._common import CommandWord, RelPath
from tools.check_cpp_installed_consumer import CONSUMER, PROGRAMS, in_scope, steps

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    import pytest


def test_no_diff_to_read_is_in_scope() -> None:
    """Where git cannot say what changed, the gate runs."""
    assert in_scope(None)


def test_an_empty_diff_is_in_scope() -> None:
    """A push to main has no diff against main, and the gate runs there."""
    assert in_scope([])


def test_a_change_to_what_the_package_installs_is_in_scope() -> None:
    """An installed header, the package config or the build moves the package."""
    for path in ("cpp/include/aletheia/yaml.hpp", "cpp/cmake/x.cmake.in", "cpp/CMakeLists.txt"):
        assert in_scope([RelPath("docs/INDEX.md"), RelPath(path)]), path


def test_a_change_elsewhere_is_out_of_scope() -> None:
    """A source the install does not ship and a document leave the gate idle."""
    assert not in_scope([RelPath("docs/INDEX.md"), RelPath("cpp/src/client.cpp")])


def test_every_program_the_consumer_builds_is_run() -> None:
    """The consumer project builds each program the gate runs, and each has its source."""
    project = (CONSUMER / "CMakeLists.txt").read_text(encoding="utf-8")
    listed = " ".join([*PROGRAMS])
    assert f"foreach(program {listed})" in project
    assert all((CONSUMER / f"{program}.cpp").is_file() for program in PROGRAMS)
    work = Path("/scratch")
    ran = [step.argv for step in steps(work, CommandWord("cmake"))[-len(PROGRAMS) :]]
    assert ran == [[CommandWord(str(work / "consumer" / program))] for program in PROGRAMS]


# Where a stood-in CMake step fails, counted from the first step.
_StepAt = NewType("_StepAt", int)


class _Gated(NamedTuple):
    """What the gate returned, the reports each step had heard as it started, and those after."""

    status: ExitStatus
    heard: list[list[Prose]]
    left: list[Prose]


def _reports(err: Prose) -> list[Prose]:
    """Return the lines of ``err`` that begin with ``progress``."""
    return [Prose(line) for line in err.splitlines() if line.startswith("progress")]


def _gated(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    failing: _StepAt | None,
) -> _Gated:
    """Run the gate with each CMake step stood in, the step at ``failing`` exiting 1."""
    (tmp_path / "cpp" / "build" / "_deps" / "x-src").mkdir(parents=True)
    heard: list[list[Prose]] = []

    def run(argv: list[CommandWord], *, cwd: Path) -> subprocess.CompletedProcess[Prose]:
        del cwd
        heard.append(_reports(Prose(capsys.readouterr().err)))
        status = 1 if len(heard) - 1 == failing else 0
        return subprocess.CompletedProcess(argv, status, Prose(""), Prose(""))

    def unknown(_root: Path) -> list[RelPath] | None:
        return None

    def found(name: CommandWord) -> CommandWord:
        return name

    monkeypatch.setattr(sys, "argv", ["check_cpp_installed_consumer"])
    monkeypatch.setattr(gate, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(gate, "branch_changes", unknown)
    monkeypatch.setattr(gate, "find_executable", found)
    monkeypatch.setattr(gate, "run_capture", run)
    status = gate.main()
    return _Gated(status, heard, _reports(Prose(capsys.readouterr().err)))


def test_each_cmake_step_is_reported_as_it_passes(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The gate reports on stderr before its first CMake step and as each one passes."""
    gated = _gated(monkeypatch, tmp_path, capsys, None)
    assert gated.status == 0
    total = len(gated.heard)
    assert gated.heard == [[f"progress: {done}/{total} CMake steps"] for done in range(total)]
    assert gated.left == [f"progress: {total}/{total} CMake steps"]


def test_a_failing_cmake_step_ends_the_gate_without_its_report(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The gate stops at a CMake step that fails, before reporting it."""
    total = len(steps(Path("/scratch"), CommandWord("cmake")))
    gated = _gated(monkeypatch, tmp_path, capsys, _StepAt(1))
    assert gated.status == 1
    assert gated.heard == [[f"progress: {done}/{total} CMake steps"] for done in range(2)]
    assert not gated.left
