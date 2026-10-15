# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the C++ lane's census rules (``tools.mutation_cpp_census``).

The bool-call twin: every ``cxx_replace_bool_call_true`` site also starts a
``cxx_replace_scalar_call`` mutant, and the census carries at least one such
site.  The identifier: every mutant is named as the plugin's unique-identifier
build names it, under its own mutator and file.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

import yaml

from tools._common import RelPath
from tools.mutation_cpp import REPO_ROOT
from tools.mutation_cpp_census import (
    BOOL_CALL_MUTATOR,
    NAMED_OFFENDERS,
    SCALAR_CALL_MUTATOR,
    bool_call_refusal,
    identifier_refusal,
)
from tools.mutation_cpp_elements import (
    ColumnNumber,
    ElementsFile,
    LineNumber,
    MullPath,
    MutantId,
    MutatorName,
)
from tools.mutation_cpp_pointer_calls import POINTER_CALL_MUTATOR

if TYPE_CHECKING:
    from collections.abc import Sequence

    from tools.mutation_cpp_elements import ElementsFiles

_TREE = "/home/user/tree"
_BACKEND = RelPath("cpp/src/backend.cpp")
_CLIENT = RelPath("cpp/src/client.cpp")
_VOID = MutatorName("cxx_remove_void_call")
# An identifier a plugin without its unique identifiers wrote: six parts, no hash and ordinal.
_SIX_PART_ID = MutantId(
    f"{SCALAR_CALL_MUTATOR}:{_TREE}/cpp/include/aletheia/backend.hpp:79:52:79:56"
)
_NO_BOOL_CALL = (
    f"the census carries no {BOOL_CALL_MUTATOR} mutant: the plugin makes the "
    + "bool-call replacement cpp/mull.yml sweeps nowhere"
)
# A mutant's place among the clones of its span, the last part of its identifier.
_Ordinal = NewType("_Ordinal", int)


class _MullConfig(TypedDict):
    """The part of ``cpp/mull.yml`` the census rules depend on: the mutators it sweeps."""

    mutators: list[MutatorName]


class _Mutant(NamedTuple):
    """One mutant: its repository-relative file, where it starts, its mutator, and its name.

    An unnamed mutant is named as the plugin names it, its ordinal its place
    in the list.
    """

    file: RelPath
    line: LineNumber
    column: ColumnNumber
    mutator: MutatorName
    ident: MutantId | None = None


def _ident(mutant: _Mutant, path: MullPath, ordinal: _Ordinal) -> MutantId:
    """Name a mutant as the plugin's unique-identifier build does."""
    span = f"{mutant.line}:{mutant.column}:{mutant.line}:{mutant.column}"
    return MutantId(f"{mutant.mutator}:{path}:{span}:ab12.{ordinal}")


def _files(mutants: Sequence[_Mutant]) -> ElementsFiles:
    """Build an Elements report's files holding the mutants given, under absolute paths."""
    files: dict[MullPath, ElementsFile] = {}
    for ordinal, mutant in enumerate(mutants):
        path = MullPath(f"{_TREE}/{mutant.file}")
        files.setdefault(path, {"mutants": []})["mutants"].append(
            {
                "id": mutant.ident or _ident(mutant, path, _Ordinal(ordinal)),
                "mutatorName": mutant.mutator,
                "location": {"start": {"line": mutant.line, "column": mutant.column}},
            }
        )
    return files


def _pair(file: RelPath, line: LineNumber, column: ColumnNumber) -> tuple[_Mutant, _Mutant]:
    """Plant a bool-call site with its scalar twin."""
    return (
        _Mutant(file, line, column, BOOL_CALL_MUTATOR),
        _Mutant(file, line, column, SCALAR_CALL_MUTATOR),
    )


def _orphan(file: RelPath, line: LineNumber, column: ColumnNumber) -> _Mutant:
    """Plant a bool-call site with no scalar twin."""
    return _Mutant(file, line, column, BOOL_CALL_MUTATOR)


def test_a_census_whose_bool_calls_all_have_a_twin_passes_both_rules() -> None:
    """Every bool-call site starts a scalar mutant too, and every name is the plugin's."""
    files = _files(
        [
            *_pair(_BACKEND, LineNumber(10), ColumnNumber(12)),
            *_pair(_CLIENT, LineNumber(30), ColumnNumber(5)),
            _Mutant(_CLIENT, LineNumber(31), ColumnNumber(9), SCALAR_CALL_MUTATOR),
            _Mutant(_BACKEND, LineNumber(11), ColumnNumber(5), _VOID),
        ]
    )
    assert bool_call_refusal(files) is None
    assert identifier_refusal(files) is None


def test_a_bool_call_without_its_twin_is_refused_by_its_site() -> None:
    """Each orphan site is named by file, line and column, in file and line order."""
    files = _files(
        [
            _orphan(_CLIENT, LineNumber(40), ColumnNumber(7)),
            *_pair(_CLIENT, LineNumber(30), ColumnNumber(5)),
            _orphan(_BACKEND, LineNumber(100), ColumnNumber(3)),
            _orphan(_BACKEND, LineNumber(20), ColumnNumber(15)),
        ]
    )
    assert bool_call_refusal(files) == (
        f"3 {BOOL_CALL_MUTATOR} sites with no {SCALAR_CALL_MUTATOR} twin, each a bool-returning "
        + "call tested for one answer only: cpp/src/backend.cpp:20:15, "
        + "cpp/src/backend.cpp:100:3, cpp/src/client.cpp:40:7"
    )


def test_a_twin_on_the_same_line_at_another_column_is_no_twin() -> None:
    """The twin shares the start, column included: two calls on one line are two sites."""
    files = _files(
        [
            _orphan(_BACKEND, LineNumber(10), ColumnNumber(12)),
            _Mutant(_BACKEND, LineNumber(10), ColumnNumber(30), SCALAR_CALL_MUTATOR),
        ]
    )
    assert bool_call_refusal(files) == (
        f"1 {BOOL_CALL_MUTATOR} sites with no {SCALAR_CALL_MUTATOR} twin, each a bool-returning "
        + "call tested for one answer only: cpp/src/backend.cpp:10:12"
    )


def test_a_census_with_no_bool_call_is_refused() -> None:
    """The replacement made nowhere: a census of scalar calls alone, and an empty one."""
    scalar_only = _files([_Mutant(_BACKEND, LineNumber(10), ColumnNumber(1), SCALAR_CALL_MUTATOR)])
    assert bool_call_refusal(scalar_only) == _NO_BOOL_CALL
    assert bool_call_refusal({}) == _NO_BOOL_CALL


def test_orphan_sites_past_the_cap_are_counted_not_named() -> None:
    """A refusal names the first sites and counts the rest."""
    orphans = [
        _orphan(_BACKEND, LineNumber(line), ColumnNumber(1))
        for line in range(1, NAMED_OFFENDERS + 3)
    ]
    named = ", ".join(f"cpp/src/backend.cpp:{line}:1" for line in range(1, NAMED_OFFENDERS + 1))
    assert bool_call_refusal(_files(orphans)) == (
        f"{NAMED_OFFENDERS + 2} {BOOL_CALL_MUTATOR} sites with no {SCALAR_CALL_MUTATOR} twin, "
        + f"each a bool-returning call tested for one answer only: {named} and 2 more"
    )


def test_an_identifier_without_its_seventh_part_is_refused() -> None:
    """A six-part name is the plugin built without its unique identifiers.

    The planted name is one such a build wrote, cut at the tree in the refusal.
    """
    files = _files(
        [
            _Mutant(
                RelPath("cpp/include/aletheia/backend.hpp"),
                LineNumber(79),
                ColumnNumber(52),
                SCALAR_CALL_MUTATOR,
                _SIX_PART_ID,
            ),
            *_pair(_BACKEND, LineNumber(10), ColumnNumber(12)),
        ]
    )
    assert identifier_refusal(files) == (
        "1 identifiers with no seventh part, the plugin built without its unique identifiers: "
        + f"{SCALAR_CALL_MUTATOR}:cpp/include/aletheia/backend.hpp:79:52:79:56"
    )


def test_an_identifier_under_another_mutator_is_refused() -> None:
    """A name that starts with another mutator is not this mutant's."""
    misnamed = _Mutant(_BACKEND, LineNumber(10), ColumnNumber(12), SCALAR_CALL_MUTATOR)
    under_void = _ident(
        misnamed._replace(mutator=_VOID), MullPath(f"{_TREE}/{_BACKEND}"), _Ordinal(0)
    )
    files = _files(
        [misnamed._replace(ident=under_void), *_pair(_CLIENT, LineNumber(30), ColumnNumber(5))]
    )
    assert identifier_refusal(files) == (
        "1 identifiers not under their mutator and file: "
        + f"{_VOID}:cpp/src/backend.cpp:10:12:10:12:ab12.0"
    )


def test_an_identifier_under_another_file_is_refused() -> None:
    """A name that carries another file's path is not a mutant of the file it is listed in."""
    in_backend = _Mutant(_BACKEND, LineNumber(10), ColumnNumber(12), _VOID)
    under_client = _ident(in_backend, MullPath(f"{_TREE}/{_CLIENT}"), _Ordinal(0))
    files = _files(
        [in_backend._replace(ident=under_client), *_pair(_CLIENT, LineNumber(30), ColumnNumber(5))]
    )
    assert identifier_refusal(files) == (
        "1 identifiers not under their mutator and file: "
        + f"{_VOID}:cpp/src/client.cpp:10:12:10:12:ab12.0"
    )


def test_both_identifier_halves_are_named_in_one_refusal() -> None:
    """A census failing on shape and on prefix says so for each half."""
    shapeless = _Mutant(_BACKEND, LineNumber(1), ColumnNumber(1), SCALAR_CALL_MUTATOR, _SIX_PART_ID)
    misplaced = _Mutant(_BACKEND, LineNumber(2), ColumnNumber(1), _VOID)
    elsewhere = _ident(misplaced, MullPath(f"{_TREE}/{_CLIENT}"), _Ordinal(1))
    assert identifier_refusal(_files([shapeless, misplaced._replace(ident=elsewhere)])) == (
        "1 identifiers with no seventh part, the plugin built without its unique identifiers: "
        + f"{SCALAR_CALL_MUTATOR}:cpp/include/aletheia/backend.hpp:79:52:79:56; "
        + "1 identifiers not under their mutator and file: "
        + f"{_VOID}:cpp/src/client.cpp:2:1:2:1:ab12.1"
    )


def test_identifiers_past_the_cap_are_counted_not_named() -> None:
    """A refusal names the first identifiers and counts the rest."""
    files = _files(
        [
            _Mutant(_BACKEND, LineNumber(line), ColumnNumber(1), SCALAR_CALL_MUTATOR, _SIX_PART_ID)
            for line in range(NAMED_OFFENDERS + 1)
        ]
    )
    short = f"{SCALAR_CALL_MUTATOR}:cpp/include/aletheia/backend.hpp:79:52:79:56"
    assert identifier_refusal(files) == (
        f"{NAMED_OFFENDERS + 1} identifiers with no seventh part, the plugin built without its "
        + f"unique identifiers: {', '.join([short] * NAMED_OFFENDERS)} and 1 more"
    )


def test_the_mutators_are_ones_cpp_mull_yml_sweeps() -> None:
    """The census rules name mutators the configuration sweeps, spelled as Mull spells them."""
    config = cast("_MullConfig", yaml.safe_load((REPO_ROOT / "cpp/mull.yml").read_text("utf-8")))
    assert {BOOL_CALL_MUTATOR, SCALAR_CALL_MUTATOR, POINTER_CALL_MUTATOR} <= set(config["mutators"])
