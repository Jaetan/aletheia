# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every Catch2 suite ctest runs takes its cases in an order of its own each run.

``cpp/CMakeLists.txt`` registers a Catch2 suite through ``aletheia_add_catch_test``,
which runs it with ``--order rand``: Catch2 draws a seed each run and prints it, so
a case that leans on another having run first fails on some run, not on none.  The
tests read the CMake files the build reads, so no configured tree is needed.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import NewType

# A CMake target's name, and the text of the CMake files that declare the tests.
TargetName = NewType("TargetName", str)
CMakeText = NewType("CMakeText", str)

_CPP = Path(__file__).resolve().parents[2] / "cpp"
_FILES = (
    _CPP / "CMakeLists.txt",
    _CPP / "tests" / "record_parity.cmake",
    _CPP / "tests" / "benchmark_programs.cmake",
)
_LINKS_CATCH = re.compile(
    r"target_link_libraries\(\s*(\w+)\b[^)]*Catch2::Catch2WithMain", re.DOTALL
)
_PLAIN_TEST = re.compile(r"add_test\(\s*NAME\s+(\w+)")
_CATCH_TEST = re.compile(r"aletheia_add_catch_test\((\w+)\)")
_FUNCTION = re.compile(r"function\(aletheia_add_catch_test name\)(.*?)endfunction\(\)", re.DOTALL)


def _text() -> CMakeText:
    return CMakeText("\n".join(path.read_text(encoding="utf-8") for path in _FILES))


def _catch_targets(text: CMakeText) -> set[TargetName]:
    """Return the targets that link Catch2's main, which take Catch2's options."""
    return {TargetName(name) for name in _LINKS_CATCH.findall(text)}


def test_the_registration_runs_a_suite_in_random_order() -> None:
    """The one function ctest registers a Catch2 suite through passes ``--order rand``."""
    (body,) = _FUNCTION.findall(_text())
    assert "add_test(NAME ${name} COMMAND ${name} --order rand)" in body


def test_no_catch2_suite_is_registered_past_the_function() -> None:
    """A Catch2 target registered by a plain ``add_test`` would run in declaration order."""
    text = _text()
    catch = _catch_targets(text)
    assert catch
    assert not catch & {TargetName(name) for name in _PLAIN_TEST.findall(text)}


def test_the_function_registers_catch2_suites_alone() -> None:
    """``--order rand`` is a Catch2 option, so every target the function registers links Catch2."""
    text = _text()
    registered = {TargetName(name) for name in _CATCH_TEST.findall(text)}
    assert registered
    assert registered <= _catch_targets(text)
