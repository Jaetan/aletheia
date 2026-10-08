# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ mutation lane's legs, and which of them a process runs.

A ``CppLeg`` is one process that builds the mutation tree and sweeps it, whole
or one slice of it.  The stage variable names the leg a CI job runs, or the
merge that reads the legs' reports; ``tools/mutation_cpp.py`` drives the lane
over them.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Literal, NamedTuple

from tools.mutation_cpp_slices import CPP_SLICES

# The Elements report the C++ runner asks Mull for, beside ``cpp.json``.
CPP_ELEMENTS_REPORT = "cpp-mull.json"

# Where the tree is configured, under ``cpp/``.  The name is the one the
# documented recipe and the build-tree ignore rules already carry, so a tree a
# reader configures by hand is the tree the lane sweeps.
CPP_TREE_DIRECTORY = "build-mutation"


class CppLeg(NamedTuple):
    """One process that builds and sweeps: the whole tree, or one slice of the surface.

    A slice's build carries the mutants of its own files alone, so the slices
    are disjoint and union to the census.  ``slice_no`` unset is the whole
    tree, which is what a local sweep runs.
    """

    slice_no: int | None = None

    def __str__(self) -> str:
        """Name the leg as it reports, by its slice where the lane is sliced."""
        return self.binding

    @property
    def binding(self) -> str:
        """The binding the leg reports as.

        A sliced leg is its own binding so its census lands in its own
        ``cpp-1.json`` and never reads as the lane's ``cpp.json``; the drift
        gate records a leg and judges only the merge.
        """
        return "cpp" if self.slice_no is None else f"cpp-{self.slice_no}"

    @property
    def report_name(self) -> str:
        """The stem Mull writes the leg's reports under, beside the merged Elements report."""
        stem = Path(CPP_ELEMENTS_REPORT).stem
        return stem if self.slice_no is None else f"{stem}-{self.slice_no}"

    @property
    def directory(self) -> str:
        """The build tree the leg configures, one per slice so their objects never mix."""
        whole = CPP_TREE_DIRECTORY
        return whole if self.slice_no is None else f"{whole}-{self.slice_no}"


def sliced_legs() -> tuple[CppLeg, ...]:
    """Every leg a sliced run is made of: each slice of the surface."""
    return tuple(CppLeg(number) for number in range(1, CPP_SLICES + 1))


CPP_STAGE_ENV = "ALETHEIA_MUTATION_CPP_STAGE"
CPP_LEGS_ENV = "ALETHEIA_MUTATION_CPP_LEGS"
# What the stage reads as where the process merges the legs rather than sweeping.
CPP_MERGE_STAGE = "merge"


def leg_of_binding(binding: str) -> CppLeg | None:
    """Name the sliced leg a binding is that of, or None where the binding names no leg.

    The whole lane reports as ``cpp`` and is judged; only a slice's report
    is a leg's, recorded and left for the merge to judge.
    """
    number = binding.removeprefix("cpp-")
    if number == binding or not number.isdigit() or not 1 <= int(number) <= CPP_SLICES:
        return None
    return CppLeg(int(number))


def is_cpp_leg(binding: str) -> bool:
    """Whether a report's binding name is one leg of the C++ lane."""
    return leg_of_binding(binding) is not None


def cpp_stage() -> CppLeg | Literal["merge"] | None:
    """Read what this process does from the environment; unset is the whole lane.

    Raises ``ValueError`` naming the variable on a value that is no slice, so
    a misspelt one in a CI job fails that job rather than sweeping the tree
    whole or sweeping nothing.
    """
    stage = os.environ.get(CPP_STAGE_ENV, "")
    if not stage:
        return None
    if stage == CPP_MERGE_STAGE:
        return CPP_MERGE_STAGE
    if not stage.isdigit() or not 1 <= int(stage) <= CPP_SLICES:
        msg = f"{CPP_STAGE_ENV}={stage!r} is not a slice of 1 to {CPP_SLICES}"
        msg += f" or {CPP_MERGE_STAGE!r}"
        raise ValueError(msg)
    return CppLeg(int(stage))
