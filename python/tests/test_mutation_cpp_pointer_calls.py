# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the C++ lane's pointer-call rule (``tools.mutation_cpp_pointer_calls``).

``cpp/mull.yml`` makes the pointer-call replacement only where null is an
answer the caller reads.  The lane refuses a census that carries no such
mutant, the rule narrowed to nothing, and one carrying a mutant on a line that
reads an exception's message, the rule widened to a call that never answers
null.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NamedTuple

from tools._common import RelPath
from tools.mutation_cpp_elements import (
    ColumnNumber,
    ElementsFile,
    LineNumber,
    MullPath,
    MutantId,
    MutatorName,
    SourceLine,
)
from tools.mutation_cpp_pointer_calls import POINTER_CALL_MUTATOR, pointer_call_refusal

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence

    from tools.mutation_cpp_elements import ElementsFiles

_BACKEND = RelPath("cpp/src/backend.cpp")
_CLIENT = RelPath("cpp/src/client.cpp")
_SCALAR = MutatorName("cxx_replace_scalar_call")

# Source lines by repository-relative file and line number, standing in for the tree.
_SOURCE: Mapping[tuple[RelPath, LineNumber], SourceLine] = {
    (_BACKEND, LineNumber(10)): SourceLine("    return process_fn_(state.get(), &text);"),
    (_BACKEND, LineNumber(20)): SourceLine(
        "    if (auto const* m = std::get_if<Multiplexed>(&s)) {"
    ),
    (_BACKEND, LineNumber(30)): SourceLine("    return somewhat(state_fn_());"),
    (_BACKEND, LineNumber(100)): SourceLine("        return Error{e.what()};"),
    (_CLIENT, LineNumber(30)): SourceLine('        log(std::string{"refused: "} + exc.what());'),
    (_CLIENT, LineNumber(40)): SourceLine("        return Error{e.what()};"),
    (_CLIENT, LineNumber(50)): SourceLine("        throw Error{failure->what()};"),
}


class _Mutant(NamedTuple):
    """One mutant: its mutator, the repository-relative file and the line it starts on."""

    mutator: MutatorName
    file: RelPath
    line: LineNumber


def _files(mutants: Sequence[_Mutant]) -> ElementsFiles:
    """Build an Elements report's files holding the mutants given, under absolute paths.

    Each mutant starts at column 1 and is named as Mull names it, its ordinal
    its place in the list, so two on one line are two mutants.
    """
    files: dict[MullPath, ElementsFile] = {}
    for ordinal, mutant in enumerate(mutants):
        path = MullPath(f"/home/user/tree/{mutant.file}")
        entry = files.setdefault(path, {"mutants": []})
        entry["mutants"].append(
            {
                "id": MutantId(
                    f"{mutant.mutator}:{path}:{mutant.line}:1:{mutant.line}:1:0.{ordinal}"
                ),
                "mutatorName": mutant.mutator,
                "location": {"start": {"line": mutant.line, "column": ColumnNumber(1)}},
            }
        )
    return files


def _read(file: RelPath, line: LineNumber) -> SourceLine:
    return _SOURCE[file, line]


def test_pointer_calls_off_every_message_line_pass() -> None:
    """A census whose pointer-call mutants all sit on calls that can answer null is the rule."""
    files = _files(
        [
            _Mutant(POINTER_CALL_MUTATOR, _BACKEND, LineNumber(10)),
            _Mutant(POINTER_CALL_MUTATOR, _BACKEND, LineNumber(20)),
        ]
    )
    assert pointer_call_refusal(files, _read) is None


def test_a_census_with_no_pointer_call_is_refused() -> None:
    """The rule narrowed to nothing: the plugin makes the replacement nowhere."""
    refused = pointer_call_refusal(_files([_Mutant(_SCALAR, _BACKEND, LineNumber(10))]), _read)
    assert refused == (
        f"the census carries no {POINTER_CALL_MUTATOR} mutant: the plugin makes the "
        + "pointer-call replacement cpp/mull.yml sweeps nowhere"
    )


def test_an_empty_census_is_refused() -> None:
    """A report with no files carries no pointer-call mutant either."""
    refused = pointer_call_refusal({}, _read)
    assert refused is not None
    assert f"the census carries no {POINTER_CALL_MUTATOR} mutant" in refused


def test_a_pointer_call_on_a_message_line_is_refused_by_its_site() -> None:
    """Each message line that carries one is named once, by file and line, in order.

    The instantiations of one template share a line, so two mutants there are
    one site; lines are ordered as numbers, so line 100 follows line 30.
    """
    files = _files(
        [
            _Mutant(POINTER_CALL_MUTATOR, _CLIENT, LineNumber(40)),
            _Mutant(POINTER_CALL_MUTATOR, _BACKEND, LineNumber(100)),
            _Mutant(POINTER_CALL_MUTATOR, _BACKEND, LineNumber(10)),
            _Mutant(POINTER_CALL_MUTATOR, _CLIENT, LineNumber(30)),
            _Mutant(POINTER_CALL_MUTATOR, _CLIENT, LineNumber(40)),
        ]
    )
    refused = pointer_call_refusal(files, _read)
    assert refused == (
        f"{POINTER_CALL_MUTATOR} mutants on lines reading an exception's message, which "
        + "never answers null: cpp/src/backend.cpp:100, cpp/src/client.cpp:30, "
        + "cpp/src/client.cpp:40"
    )


def test_a_message_read_through_a_pointer_is_a_message_line() -> None:
    """``->what()`` reads a message as ``.what()`` does; a name ending in ``what()`` does not."""
    files = _files(
        [
            _Mutant(POINTER_CALL_MUTATOR, _CLIENT, LineNumber(50)),
            _Mutant(POINTER_CALL_MUTATOR, _BACKEND, LineNumber(30)),
        ]
    )
    assert pointer_call_refusal(files, _read) == (
        f"{POINTER_CALL_MUTATOR} mutants on lines reading an exception's message, which "
        + "never answers null: cpp/src/client.cpp:50"
    )


def test_another_mutator_on_a_message_line_is_not_the_rule() -> None:
    """Only the pointer-call replacement is held off a message line; others may sit there."""
    files = _files(
        [
            _Mutant(_SCALAR, _CLIENT, LineNumber(30)),
            _Mutant(MutatorName("cxx_remove_void_call"), _CLIENT, LineNumber(40)),
            _Mutant(POINTER_CALL_MUTATOR, _BACKEND, LineNumber(10)),
        ]
    )
    assert pointer_call_refusal(files, _read) is None


def test_the_line_is_read_from_the_repository_relative_file() -> None:
    """A path Mull names absolutely is read at its ``cpp/`` component, and only a pointer call's."""
    asked: list[tuple[RelPath, LineNumber]] = []

    def read(file: RelPath, line: LineNumber) -> SourceLine:
        asked.append((file, line))
        return _SOURCE[file, line]

    files = _files(
        [
            _Mutant(POINTER_CALL_MUTATOR, _BACKEND, LineNumber(20)),
            _Mutant(_SCALAR, _CLIENT, LineNumber(30)),
        ]
    )
    assert pointer_call_refusal(files, read) is None
    assert asked == [(_BACKEND, LineNumber(20))]
