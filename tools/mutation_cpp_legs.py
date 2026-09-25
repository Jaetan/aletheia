# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ mutation lane's trees and legs, and which of them a process runs.

A ``CppTree`` is one build the C++ surface is read with; a ``CppLeg`` is one
process that builds a tree and sweeps it, whole or one slice of it.  The
stage variables name the leg a CI job runs, or the merge that reads the legs'
reports; ``tools/mutation_cpp.py`` drives the lane over them.
"""

from __future__ import annotations

import os
from enum import StrEnum
from pathlib import Path
from typing import Literal, NamedTuple

from tools.mutation_cpp_slices import CPP_SLICES

# The Elements report the C++ runner asks Mull for, beside ``cpp.json``.
CPP_ELEMENTS_REPORT = "cpp-mull.json"


class CppTree(StrEnum):
    """One of the builds the C++ surface is read with, each reading a class the others cannot.

    Under LeakSanitizer a mutant that removes a destructor leaks the object
    and the run fails, where a plain build cannot tell it from the original.
    Under AddressSanitizer a mutant that leaves a value read after the object
    or the frame holding it is gone fails there, where libstdc++'s debug mode,
    which every tree compiles under, checks a container's own preconditions
    and not a reference's lifetime.  The plain tree carries the
    allocation-fault sweeps, which replace the program's allocation functions
    to reach the cleanup a container runs while it throws; a sanitizer runtime
    defines those same functions, so a sanitizer tree cannot carry them.  A
    mutant survives the sweep only where it survived every tree.
    """

    LEAK = "leak"
    PLAIN = "plain"
    ADDRESS = "address"

    @property
    def sanitizer(self) -> str:
        """The sanitizer the tree is built with; the plain tree carries none."""
        return "" if self is CppTree.PLAIN else self.value

    @property
    def directory(self) -> str:
        """Where the tree is configured, under ``cpp/``."""
        return _CPP_TREE_DIRECTORIES[self]

    @property
    def dropped_mutators(self) -> tuple[str, ...]:
        """The mutators this tree cannot read, dropped from the configuration it builds under.

        AddressSanitizer instruments the program by inserting its own calls
        and stores, each at the source location of the statement it guards,
        so a mutator over calls or over constant stores mutates those rather
        than the program's own: measured with the call mutators on, the tree
        carried more mutants than the other trees and every extra one
        survived, each the removal of a check; with the constant-store
        mutators on, it carried three identifiers the other trees do not,
        two of them surviving, each a store the sanitizer wrote. Without
        them the tree carries the mutants the other trees carry under the
        same identifiers, and it keeps what it is for: a flipped comparison
        that then reads memory the program does not own is what it alone
        reads, 22 kills on the recorded sweep.
        """
        return _CPP_CALL_MUTATORS + _CPP_STORE_MUTATORS if self is CppTree.ADDRESS else ()


# The mutators over calls, and the two over constant stores. Named here rather
# than inside the property that drops them, so the set a tree cannot read is
# one list a reader can find.
_CPP_CALL_MUTATORS: tuple[str, ...] = (
    "cxx_remove_void_call",
    "cxx_replace_scalar_call",
    "cxx_replace_bool_call_true",
    "cxx_replace_pointer_call_null",
)
_CPP_STORE_MUTATORS: tuple[str, ...] = ("cxx_const_assignment",)

# Where each tree is configured. The names are the ones the documented recipes
# and the build-tree ignore rules already carry, so a tree a reader configures
# by hand is the tree the lane sweeps.
_CPP_TREE_DIRECTORIES: dict[CppTree, str] = {
    CppTree.LEAK: "build-mutation",
    CppTree.PLAIN: "build-mutation-plain",
    CppTree.ADDRESS: "build-mutation-asan",
}


class CppLeg(NamedTuple):
    """One process that builds and sweeps: a tree, and the slice of the surface it carries.

    A slice's build carries the mutants of its own files alone, so a tree's
    slices are disjoint and union to the tree's census.  ``slice_no`` unset is
    the whole tree, which is what a local sweep runs.
    """

    tree: CppTree
    slice_no: int | None = None

    def __str__(self) -> str:
        """Name the leg by its tree, and by its slice where the lane is sliced."""
        whole = self.tree.value
        return whole if self.slice_no is None else f"{whole}-{self.slice_no}"

    @property
    def binding(self) -> str:
        """The binding the leg reports as.

        A leg is its own binding so its census lands in its own
        ``cpp-leak-1.json`` and never reads as the lane's ``cpp.json``; the
        drift gate records a leg and judges only the merge.
        """
        return f"cpp-{self}"

    @property
    def report_name(self) -> str:
        """The stem Mull writes the leg's reports under, beside the merged Elements report."""
        return f"{Path(CPP_ELEMENTS_REPORT).stem}-{self}"

    @property
    def directory(self) -> str:
        """The build tree the leg configures, one per tree and slice so their objects never mix."""
        whole = self.tree.directory
        return whole if self.slice_no is None else f"{whole}-{self.slice_no}"


def sliced_legs() -> tuple[CppLeg, ...]:
    """Every leg a sliced run is made of: each tree, each slice of it."""
    return tuple(CppLeg(tree, number) for tree in CppTree for number in range(1, CPP_SLICES + 1))


CPP_STAGE_ENV = "ALETHEIA_MUTATION_CPP_STAGE"
CPP_SLICE_ENV = "ALETHEIA_MUTATION_CPP_SLICE"
CPP_LEGS_ENV = "ALETHEIA_MUTATION_CPP_LEGS"

# What the stage reads as where the process merges the legs rather than sweeping.
CPP_MERGE_STAGE = "merge"


def leg_of_binding(binding: str) -> CppLeg | None:
    """Name the leg a binding is that of, or None where the binding names no leg."""
    name = binding.removeprefix("cpp-")
    if name == binding:
        return None
    tree_name, _, number = name.partition("-")
    try:
        tree = CppTree(tree_name)
    except ValueError:
        return None
    if not number:
        return CppLeg(tree)
    if not number.isdigit() or not 1 <= int(number) <= CPP_SLICES:
        return None
    return CppLeg(tree, int(number))


def is_cpp_leg(binding: str) -> bool:
    """Whether a report's binding name is one leg of the C++ lane."""
    return leg_of_binding(binding) is not None


def cpp_stage() -> CppLeg | Literal["merge"] | None:
    """Read what this process does from the environment; unset is the whole lane.

    Raises ``ValueError`` naming the variable on a value that is no tree or no
    slice, so a misspelt one in a CI job fails that job rather than sweeping
    nothing, or sweeping a tree whole where the run wanted a slice of it.
    """
    stage = os.environ.get(CPP_STAGE_ENV, "")
    wanted = os.environ.get(CPP_SLICE_ENV, "")
    if not stage:
        if wanted:
            msg = f"{CPP_SLICE_ENV}={wanted!r} names a slice of no tree: {CPP_STAGE_ENV} is unset"
            raise ValueError(msg)
        return None
    if stage == CPP_MERGE_STAGE:
        return CPP_MERGE_STAGE
    try:
        tree = CppTree(stage)
    except ValueError:
        names = ", ".join([*(tree.value for tree in CppTree), CPP_MERGE_STAGE])
        msg = f"{CPP_STAGE_ENV}={stage!r} is not one of {names}"
        raise ValueError(msg) from None
    return CppLeg(tree, _wanted_slice(wanted))


def _wanted_slice(value: str) -> int | None:
    """Read which slice a leg carries; empty is the tree whole."""
    if not value:
        return None
    if not value.isdigit() or not 1 <= int(value) <= CPP_SLICES:
        msg = f"{CPP_SLICE_ENV}={value!r} is not a slice of 1 to {CPP_SLICES}"
        raise ValueError(msg)
    return int(value)
