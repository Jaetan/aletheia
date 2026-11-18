# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The installed-consumer gate: when it runs, and that it runs every program it builds."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING

from tools import check_cpp_installed_consumer as gate
from tools._common import CommandWord, RelPath
from tools.check_cpp_installed_consumer import CONSUMER, PROGRAMS, in_scope, steps

from aletheia.common_types import Prose

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


def test_each_cmake_step_is_reported_as_it_runs(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The gate reports on stderr before its first CMake step and as each one passes."""
    (tmp_path / "cpp" / "build" / "_deps" / "x-src").mkdir(parents=True)
    ran: list[list[CommandWord]] = []

    def run(argv: list[CommandWord], *, cwd: Path) -> subprocess.CompletedProcess[Prose]:
        del cwd
        ran.append(argv)
        return subprocess.CompletedProcess(argv, 0, Prose(""), Prose(""))

    def unknown(_root: Path) -> list[RelPath] | None:
        return None

    def found(name: CommandWord) -> CommandWord:
        return name

    monkeypatch.setattr(sys, "argv", ["check_cpp_installed_consumer"])
    monkeypatch.setattr(gate, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(gate, "branch_changes", unknown)
    monkeypatch.setattr(gate, "find_executable", found)
    monkeypatch.setattr(gate, "run_capture", run)
    assert gate.main() == 0
    total = len(ran)
    printed = [line for line in capsys.readouterr().err.splitlines() if line.startswith("progress")]
    assert printed == [f"progress: {done}/{total} CMake steps" for done in range(total + 1)]
