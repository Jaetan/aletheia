# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The installed-consumer gate: when it runs, and that it runs every program it builds."""

from __future__ import annotations

from pathlib import Path

from tools._common import CommandWord, RelPath
from tools.check_cpp_installed_consumer import CONSUMER, PROGRAMS, in_scope, steps


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
