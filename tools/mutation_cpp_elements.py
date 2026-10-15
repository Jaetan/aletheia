# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The shape of Mull's Elements report, as the C++ lane reads it.

Mull writes one ``mutation-testing-elements`` JSON per sweep.  Its ``files``
maps each mutated file, named by its absolute path under the tree the sweep
ran over, to the mutants made in it, and each mutant carries its identifier,
its mutator and the span it covers.  The identifier reads
``<mutator>:<path>:<line>:<column>:<line>:<column>:<hash>.<ordinal>``, the
hash and the ordinal telling the clones of one span apart.  The rules the lane
holds on the census (``tools/mutation_cpp_census.py`` and
``tools/mutation_cpp_pointer_calls.py``) and its ledgers read the report
through the types here.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NewType, TypedDict

from tools._common import RelPath

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

MutatorName = NewType("MutatorName", str)
# A path as Mull names it: absolute, under the tree it swept.
MullPath = NewType("MullPath", str)
# A line's number in a source file, counted from 1, a column's number on that
# line, counted from 1, and the text of that line.
LineNumber = NewType("LineNumber", int)
ColumnNumber = NewType("ColumnNumber", int)
SourceLine = NewType("SourceLine", str)
# A mutant's identifier as Mull writes it.
MutantId = NewType("MutantId", str)
# Reads a line of a repository-relative file.
type LineReader = Callable[[RelPath, LineNumber], SourceLine]


class MutantStart(TypedDict):
    """Where a mutant starts in its file."""

    line: LineNumber
    column: ColumnNumber


class MutantLocation(TypedDict):
    """The span a mutant covers in its file, of which the rules read the start."""

    start: MutantStart


class ElementsMutant(TypedDict):
    """The fields of a mutant in Mull's Elements report that the rules read."""

    id: MutantId
    mutatorName: MutatorName
    location: MutantLocation


class ElementsFile(TypedDict):
    """One file's entry in the Elements report: the mutants made in it."""

    mutants: list[ElementsMutant]


# The Elements report's ``files``: each mutated file, as Mull names it, with its mutants.
type ElementsFiles = Mapping[MullPath, ElementsFile]


def repo_relative(path: MullPath) -> RelPath:
    """Cut a path Mull names at its first ``/cpp/``, keeping a path that has none as it is."""
    return RelPath("cpp/" + path.split("/cpp/", 1)[1] if "/cpp/" in path else path)
