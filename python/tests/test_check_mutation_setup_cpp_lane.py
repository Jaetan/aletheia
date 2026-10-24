# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the C++ lane's checks of ``tools.check_mutation_setup_lanes``: both read the listfile.

The swept binary compiles no doc-example harness, and the mutation build links
the library statically.  The listfile is read as CMake reads it, so each check
is pointed at one the test plants, written with the comments, quoted and
bracket arguments and nested parentheses CMake allows, and its diagnostics
compared whole.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, Literal

import pytest
from _gate_exit import stderr_of_exit_2
from _planted_tree import plant

from tools import check_mutation_setup_lanes
from tools._common import RelPath
from tools.check_mutation_setup_lanes import CPP_DOC_HARNESS
from tools.mutation_cpp import CPP_TEST_TARGET

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path


# The C++ lane's swept binary compiles no doc-example harness.

_CPP_TARGETS: Final = Prose(
    f"add_executable({CPP_TEST_TARGET} tests/client_tests.cpp)\n"
    + f"add_executable(doc_example_tests {CPP_DOC_HARNESS})\n"
)
_CPP_FOLDED: Final = Prose(
    f"[cpp/doc-harness] {CPP_TEST_TARGET}, the binary the Mull runner runs once "
    + f"per mutant, compiles {CPP_DOC_HARNESS}"
)
_CPP_MOVED: Final = Prose(
    "[cpp/doc-harness] no target of cpp/CMakeLists.txt compiles "
    + f"{CPP_DOC_HARNESS}: the harness moved, and this check would name nothing"
)
_CMAKE: Final = RelPath("cpp/CMakeLists.txt")


def _plant_cmake(root: Path, monkeypatch: pytest.MonkeyPatch, text: Prose) -> None:
    """Plant ``cpp/CMakeLists.txt`` reading ``text``, and point the gate there."""
    monkeypatch.setattr(
        check_mutation_setup_lanes, "CMAKE_PATH", plant(root, {_CMAKE: text}) / _CMAKE
    )


@pytest.mark.parametrize(
    ("cmake", "diagnostics"),
    [
        pytest.param(_CPP_TARGETS, [], id="the harness its own binary"),
        pytest.param(
            Prose(f"{_CPP_TARGETS}# target_sources({CPP_TEST_TARGET} PRIVATE {CPP_DOC_HARNESS})\n"),
            [],
            id="a fold in a comment",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}#[[\ntarget_sources({CPP_TEST_TARGET} PRIVATE\n"
                + f"    {CPP_DOC_HARNESS})\n]]\n"
            ),
            [],
            id="a fold in a bracket comment",
        ),
        pytest.param(
            Prose(f"{_CPP_TARGETS}target_sources({CPP_TEST_TARGET} PRIVATE {CPP_DOC_HARNESS})\n"),
            [_CPP_FOLDED],
            id="the harness folded into the swept binary",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}target_sources(# the swept binary\n"
                + f"    {CPP_TEST_TARGET} PRIVATE {CPP_DOC_HARNESS})\n"
            ),
            [_CPP_FOLDED],
            id="a line comment before the target",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}target_sources(#[[ the swept binary ]] {CPP_TEST_TARGET} "
                + f"PRIVATE {CPP_DOC_HARNESS})\n"
            ),
            [_CPP_FOLDED],
            id="a bracket comment before the target",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}target_sources({CPP_TEST_TARGET} PRIVATE [[{CPP_DOC_HARNESS}]])\n"
            ),
            [_CPP_FOLDED],
            id="folded as a bracket argument",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}target_sources({CPP_TEST_TARGET} PRIVATE (grouped) "
                + f"{CPP_DOC_HARNESS})\n"
            ),
            [_CPP_FOLDED],
            id="a parenthesised argument before the harness",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}if(ALETHEIA_MUTATION)\n"
                + f"    target_sources({CPP_TEST_TARGET} PRIVATE\n"
                + f"        tests/integration_tests.cpp\n        {CPP_DOC_HARNESS}\n    )\n"
                + "endif()\n"
            ),
            [_CPP_FOLDED],
            id="folded across lines under the mutation build",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}if(ALETHEIA_MUTATION)\n"
                + f"    target_sources({CPP_TEST_TARGET} PRIVATE {CPP_DOC_HARNESS})\n"
                + f"    target_sources({CPP_TEST_TARGET} PRIVATE tests/integration_tests.cpp)\n"
                + "endif()\n"
            ),
            [_CPP_FOLDED],
            id="folded by the first of two target_sources commands",
        ),
        pytest.param(
            Prose(f"{_CPP_TARGETS}TARGET_SOURCES({CPP_TEST_TARGET} PRIVATE {CPP_DOC_HARNESS})\n"),
            [_CPP_FOLDED],
            id="folded by a command spelled in capitals",
        ),
        pytest.param(
            Prose(
                f'{_CPP_TARGETS}target_sources({CPP_TEST_TARGET} PRIVATE "tests/doc_\\\n'
                + 'example_tests.cpp")\n'
            ),
            [_CPP_FOLDED],
            id="folded as a quoted argument continued across a line",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}cmake_language(CALL target_sources {CPP_TEST_TARGET} PRIVATE "
                + f"{CPP_DOC_HARNESS})\n"
            ),
            [_CPP_FOLDED],
            id="folded through cmake_language(CALL)",
        ),
        pytest.param(
            Prose(f'{_CPP_TARGETS}target_sources({CPP_TEST_TARGET} PRIVATE "{CPP_DOC_HARNESS}")\n'),
            [_CPP_FOLDED],
            id="folded as a quoted argument",
        ),
        pytest.param(
            Prose(
                'target_sources(other PRIVATE "a#)")\n'
                + f"add_executable({CPP_TEST_TARGET} tests/client_tests.cpp {CPP_DOC_HARNESS})\n"
            ),
            [_CPP_FOLDED],
            id="a hash in a quoted argument opens no comment",
        ),
        pytest.param(
            Prose(
                f"add_executable({CPP_TEST_TARGET} tests/client_tests.cpp)\n"
                + "add_executable(doc_example_tests tests/doc_fences.cpp)\n"
            ),
            [_CPP_MOVED],
            id="the harness moved",
        ),
        pytest.param(
            Prose(
                f"add_executable({CPP_TEST_TARGET} tests/client_tests.cpp)\n"
                + f"#[[\nadd_executable(doc_example_tests {CPP_DOC_HARNESS})\n]]\n"
            ),
            [_CPP_MOVED],
            id="the harness kept in a bracket comment alone",
        ),
    ],
)
def test_the_cpp_harness_in_the_swept_binary_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, cmake: Prose, diagnostics: list[Prose]
) -> None:
    """The harness's source compiled into the binary the Mull runner runs, or nowhere, is named."""
    _plant_cmake(tmp_path, monkeypatch, cmake)
    assert check_mutation_setup_lanes.cpp_lane_runs_no_doc_harness() == diagnostics


def _unread_source(word: Prose) -> Prose:
    """Return the diagnostic for a source of the swept binary the gate reads as written."""
    return Prose(
        f"[cpp/doc-harness] {CPP_TEST_TARGET} takes {word}, a source this gate reads as written "
        + "and CMake evaluates: name its files"
    )


def _unread_target(target: Prose) -> Prose:
    """Return the diagnostic for a target compiling the harness that the gate reads as written."""
    return Prose(
        f"[cpp/doc-harness] {target}, a target this gate reads as written and CMake evaluates, "
        + f"compiles {CPP_DOC_HARNESS}: name the target"
    )


@pytest.mark.parametrize(
    ("cmake", "diagnostics"),
    [
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}set(UT {CPP_DOC_HARNESS})\n"
                + "target_sources("
                + CPP_TEST_TARGET
                + " PRIVATE ${UT})\n"
            ),
            [_unread_source(Prose("${UT}"))],
            id="a source through a variable",
        ),
        pytest.param(
            Prose(
                "file(GLOB SRCS tests/doc_*.cpp)\n"
                + "add_executable("
                + CPP_TEST_TARGET
                + " tests/client_tests.cpp ${SRCS})\n"
                + f"add_executable(doc_example_tests {CPP_DOC_HARNESS})\n"
            ),
            [_unread_source(Prose("${SRCS}"))],
            id="a source through a glob's variable",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}target_sources({CPP_TEST_TARGET} PRIVATE "
                + "$<$<BOOL:${DOCS}>:"
                + CPP_DOC_HARNESS
                + ">)\n"
            ),
            [_unread_source(Prose("$<$<BOOL:${DOCS}>:" + CPP_DOC_HARNESS + ">"))],
            id="a source through a generator expression",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}set(T {CPP_TEST_TARGET})\n"
                + "target_sources(${T} PRIVATE "
                + CPP_DOC_HARNESS
                + ")\n"
            ),
            [_unread_target(Prose("${T}"))],
            id="the harness under a target through a variable",
        ),
        pytest.param(
            Prose(
                f"{_CPP_TARGETS}foreach(suite one two)\n"
                + "    add_executable(${suite} tests/${suite}.cpp)\nendforeach()\n"
            ),
            [],
            id="a target through a variable compiling no harness",
        ),
    ],
)
def test_a_reference_the_cpp_check_cannot_read_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, cmake: Prose, diagnostics: list[Prose]
) -> None:
    """A source of the swept binary, or a target compiling the harness, through CMake is named.

    A target spelled through a variable whose sources hold no harness is not,
    as the real listfile builds its suites that way.
    """
    _plant_cmake(tmp_path, monkeypatch, cmake)
    assert check_mutation_setup_lanes.cpp_lane_runs_no_doc_harness() == diagnostics


@pytest.mark.parametrize(
    ("cmake", "reason"),
    [
        pytest.param(
            Prose(f"{_CPP_TARGETS}set(A (b\n"),
            "set( is missing its closing parenthesis",
            id="a command left open",
        ),
        pytest.param(
            Prose(f'{_CPP_TARGETS}set(A "abc)\n'),
            "'\"abc' opens what never closes",
            id="a quote left open",
        ),
        pytest.param(
            Prose(f"{_CPP_TARGETS}set(A [=[abc)\n"),
            "'[=[abc' opens what never closes",
            id="a bracket argument left open",
        ),
        pytest.param(
            Prose(f"{_CPP_TARGETS}#[[ abc\n"),
            "'#[[ abc' opens what never closes",
            id="a bracket comment left open",
        ),
    ],
)
def test_a_cmake_file_cmake_refuses_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    cmake: Prose,
    reason: Prose,
) -> None:
    """A listfile CMake stops on, read anyway by the lexer, stops the gate naming the opening."""
    _plant_cmake(tmp_path, monkeypatch, cmake)
    assert stderr_of_exit_2(capsys, check_mutation_setup_lanes.cpp_lane_runs_no_doc_harness) == (
        f"ERROR: cannot read {tmp_path / _CMAKE}: {reason}\n"
    )


@pytest.mark.parametrize(
    "check",
    [
        pytest.param(check_mutation_setup_lanes.cpp_lane_runs_no_doc_harness, id="the doc harness"),
        pytest.param(
            check_mutation_setup_lanes.cpp_lane_links_the_library_statically, id="the linkage"
        ),
    ],
)
def test_a_cmake_file_that_is_missing_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    check: Callable[[], list[Prose]],
) -> None:
    """Without ``cpp/CMakeLists.txt`` either check of it stops the gate, naming the file."""
    monkeypatch.setattr(check_mutation_setup_lanes, "CMAKE_PATH", tmp_path / _CMAKE)
    assert stderr_of_exit_2(capsys, check) == (
        f"ERROR: cannot read {tmp_path / _CMAKE}: No such file or directory\n"
    )


# The mutation build links the C++ library statically.

_LINKAGE: Final = (
    "if(ALETHEIA_MUTATION)\n    set(ALETHEIA_CPP_LINKAGE STATIC)\n"
    + "else()\n    set(ALETHEIA_CPP_LINKAGE SHARED)\nendif()\n\n"
    + "add_library(aletheia-cpp ${ALETHEIA_CPP_LINKAGE}\n    src/client.cpp\n)\n"
)
_NOT_STATIC: Final = Prose(
    "[cpp/linkage] cpp/CMakeLists.txt does not open if(ALETHEIA_MUTATION) with "
    + "set(ALETHEIA_CPP_LINKAGE STATIC), so the Mull runner sees the library's "
    + "mutants through a shared library, which hides most of them"
)
_NOT_TAKEN: Final = Prose(
    "[cpp/linkage] cpp/CMakeLists.txt does not build aletheia-cpp as "
    + "${ALETHEIA_CPP_LINKAGE}, so the mutation build's link form does not reach it"
)


def _written_beside(count: Literal[1, 2]) -> Prose:
    """Return the diagnostic for ``count`` writes of the variable past the branch's two."""
    return Prose(
        f"[cpp/linkage] cpp/CMakeLists.txt writes ALETHEIA_CPP_LINKAGE in {count} command(s) "
        + "beside the if(ALETHEIA_MUTATION) branch's first and the else() that follows it, "
        + "so the mutation build can end on another form"
    )


@pytest.mark.parametrize(
    ("cmake", "diagnostics"),
    [
        pytest.param(Prose(_LINKAGE), [], id="static under the mutation build"),
        pytest.param(
            Prose(f"{_LINKAGE}cmake_language(CALL set ALETHEIA_CPP_LINKAGE SHARED)\n"),
            [_written_beside(1)],
            id="written again through cmake_language(CALL)",
        ),
        pytest.param(
            Prose(
                _LINKAGE.replace("if(ALETHEIA_MUTATION)", "if ( ALETHEIA_MUTATION )").replace(
                    "set(ALETHEIA_CPP_LINKAGE STATIC)", "set( ALETHEIA_CPP_LINKAGE  STATIC )"
                )
            ),
            [],
            id="spaced as CMake allows",
        ),
        pytest.param(
            Prose(
                _LINKAGE.replace("if(", "IF(")
                .replace("set(", "SET(")
                .replace("else()", "ELSE()")
                .replace("add_library(", "ADD_LIBRARY(")
            ),
            [],
            id="commands spelled in capitals",
        ),
        pytest.param(
            Prose(_LINKAGE.replace("LINKAGE STATIC)", 'LINKAGE "STATIC")')),
            [],
            id="the form quoted",
        ),
        pytest.param(
            Prose(_LINKAGE.replace("LINKAGE STATIC)", "LINKAGE # the mutation build's\n STATIC)")),
            [],
            id="a line comment among the arguments",
        ),
        pytest.param(
            Prose(
                _LINKAGE.replace("LINKAGE STATIC)", "LINKAGE #[[ the mutation build's ]] STATIC)")
            ),
            [],
            id="a bracket comment among the arguments",
        ),
        pytest.param(
            Prose(
                "if(ALETHEIA_MUTATION)\n    set(ALETHEIA_CPP_LINKAGE STATIC)\nendif()\n"
                + "add_library(aletheia-cpp ${ALETHEIA_CPP_LINKAGE}\n    src/client.cpp\n)\n"
            ),
            [],
            id="no else branch",
        ),
        pytest.param(
            Prose("#[[ the mutation build ]] " + _LINKAGE),
            [],
            id="a bracket comment before the branch on its line",
        ),
        pytest.param(
            Prose(
                _LINKAGE.replace("STATIC", "PLACEHOLDER")
                .replace("SHARED", "STATIC")
                .replace("PLACEHOLDER", "SHARED")
            ),
            [_NOT_STATIC],
            id="static only outside the mutation build",
        ),
        pytest.param(
            Prose(
                "# if(ALETHEIA_MUTATION) set(ALETHEIA_CPP_LINKAGE STATIC) endif()\n"
                + "# add_library(aletheia-cpp ${ALETHEIA_CPP_LINKAGE}\n"
                + "add_library(aletheia-cpp SHARED\n    src/client.cpp\n)\n"
            ),
            [_NOT_STATIC, _NOT_TAKEN],
            id="the static form in comments alone",
        ),
        pytest.param(
            Prose(
                "#[[\nif(ALETHEIA_MUTATION)\n    set(ALETHEIA_CPP_LINKAGE STATIC)\nendif()\n]]\n"
                + "set(ALETHEIA_CPP_LINKAGE SHARED)\n"
                + "add_library(aletheia-cpp ${ALETHEIA_CPP_LINKAGE}\n    src/client.cpp\n)\n"
            ),
            [_NOT_STATIC],
            id="the static form in a bracket comment alone",
        ),
        pytest.param(
            Prose(_LINKAGE.replace("endif()\n", "endif()\nset(ALETHEIA_CPP_LINKAGE SHARED)\n")),
            [_written_beside(1)],
            id="shared after the branch",
        ),
        pytest.param(
            Prose(_LINKAGE.replace("endif()\n", "endif()\nunset(ALETHEIA_CPP_LINKAGE)\n")),
            [_written_beside(1)],
            id="unset after the branch",
        ),
        pytest.param(
            Prose(
                _LINKAGE.replace(
                    "    set(ALETHEIA_CPP_LINKAGE STATIC)\n",
                    "    set(ALETHEIA_CPP_LINKAGE STATIC)\n    set(ALETHEIA_CPP_LINKAGE SHARED)\n",
                )
            ),
            [_written_beside(2)],
            id="a second set in the branch",
        ),
        pytest.param(
            Prose(_LINKAGE.replace("aletheia-cpp ${ALETHEIA_CPP_LINKAGE}", "aletheia-cpp SHARED")),
            [_NOT_TAKEN],
            id="the library shared whatever the build",
        ),
    ],
)
def test_a_mutation_build_that_does_not_link_statically_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, cmake: Prose, diagnostics: list[Prose]
) -> None:
    """The static form set first under the mutation build, alone, and taken by the library."""
    _plant_cmake(tmp_path, monkeypatch, cmake)
    assert check_mutation_setup_lanes.cpp_lane_links_the_library_statically() == diagnostics
