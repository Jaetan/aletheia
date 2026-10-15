# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold that the pinned mutmut has no operator for the constructs the Python lane calls refusals.

mutmut's operator table is fixed in the package and takes no configuration,
so what it cannot mutate is a refusal the Python lane's record carries whole:
a ``for`` loop, a ``with`` block, a condition that is a bare name, a ``raise``,
a ``return``, an f-string, and a function under a decorator other than
``staticmethod`` or ``classmethod``, which it skips entire.  A defect in one of
those is one the lane cannot see, and the record has to say so rather than
count it as swept.  That is a fact about the mutmut release rather than the
tree, so the gate runs when the pin in the ``[mutation]`` extra of
``python/pyproject.toml`` moves, or the gate itself (``tools/pin_scope.py``).

The fact is shown by handing mutmut's own operator table a function written
from those constructs alone, which must yield no mutation, and a comparison,
which must yield at least one, so that the table read is the one the lane
sweeps with.

Exits 0 when the fact holds or nothing it rests on moved, 1 when mutmut now
mutates one of the constructs, named by its source, or the comparison yields
nothing, and 2 when the venv has no mutmut to ask.
"""

from __future__ import annotations

import argparse
import sys
from importlib import import_module
from typing import TYPE_CHECKING, NewType, cast

from tools._common import emit, git_toplevel
from tools.pin_scope import PinGate, gate_runs

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Sequence

    import libcst as cst
    from libcst.metadata import MetadataWrapper
    from mutmut.mutation.file_mutation import MutationVisitor
    from mutmut.mutation.mutators import OPERATORS_TYPE
    from mutmut.mutation.pragma_handling import IgnoredCode

# Python source text, as mutmut parses it.
PythonSource = NewType("PythonSource", str)

# The source of the node a mutation rewrites, as mutmut read it.
MutantNodeText = NewType("MutantNodeText", str)

# The constructs the lane's record calls refusals, and nothing else.
REFUSED_SOURCE = PythonSource("""
def f(items, flag, error):
    for item in items:
        with error:
            if flag:
                raise error
    return f"bad {item}"

@property
def g(self):
    return self.x < self.y
""")

# A comparison, which the operator table the lane runs mutates.
CONTROL_SOURCE = PythonSource("""
def h(a, b):
    return a < b
""")

# How much of a mutated node's source a refusal names.
NAMED_CHARACTERS = 60

INSTALL_HINT = Prose("mutmut is not installed in the venv; pip install -e 'python/.[mutation]'")


def mutations_of(source: PythonSource) -> list[MutantNodeText]:
    """Return the source of every node mutmut's operator table mutates in ``source``.

    Raises ``ImportError`` where the venv has no mutmut: the package is an
    opt-in extra, imported where it is asked for so the gate can say so.
    """
    libcst = import_module("libcst")
    metadata = import_module("libcst.metadata")
    file_mutation = import_module("mutmut.mutation.file_mutation")
    mutators = import_module("mutmut.mutation.mutators")
    pragma_handling = import_module("mutmut.mutation.pragma_handling")
    parse_module = cast("Callable[[PythonSource], cst.Module]", libcst.parse_module)
    module_of = cast("type[cst.Module]", libcst.Module)
    wrap = cast("type[MetadataWrapper]", metadata.MetadataWrapper)
    visitor_of = cast("type[MutationVisitor]", file_mutation.MutationVisitor)
    operators = cast("OPERATORS_TYPE", mutators.mutation_operators)
    ignored_code_of = cast("type[IgnoredCode]", pragma_handling.IgnoredCode)

    visitor = visitor_of(operators, ignored_code_of(set(), set(), set()))
    _ = wrap(parse_module(source)).visit(visitor)
    printer = module_of([])
    return [
        MutantNodeText(printer.code_for_node(mutation.original_node).strip())
        for mutation in visitor.mutations
    ]


def operator_refusal(
    refused_made: Sequence[MutantNodeText], control_made: Sequence[MutantNodeText]
) -> Prose | None:
    """Return why the fact no longer holds, or None where it does.

    ``refused_made`` is what mutmut mutated in the refused constructs, each of
    which re-opens the record's row; ``control_made`` is what it mutated in the
    comparison, which is empty only when the table read is not the lane's.
    """
    lines = [f"mutmut now mutates: {text[:NAMED_CHARACTERS]}" for text in refused_made]
    if not control_made:
        lines.append(
            "the control comparison yields no mutation, so the table is not the one the lane runs"
        )
    if not lines:
        return None
    return Prose("\n".join(lines))


def _missing_package(exc: ImportError) -> bool:
    """Say whether ``exc`` is the absence of mutmut, or of libcst, which it installs."""
    return (exc.name or "").split(".", 1)[0] in {"mutmut", "libcst"}


def check() -> ExitStatus:
    """Ask the venv's mutmut about both sources and judge its answers."""
    try:
        refused_made = mutations_of(REFUSED_SOURCE)
        control_made = mutations_of(CONTROL_SOURCE)
    except ImportError as exc:
        if not _missing_package(exc):
            raise
        emit(f"check-mutmut-operators: {INSTALL_HINT}")
        return ExitStatus(2)
    refusal = operator_refusal(refused_made, control_made)
    if refusal is None:
        return ExitStatus(0)
    emit(f"check-mutmut-operators: {refusal}")
    return ExitStatus(1)


def main() -> ExitStatus:
    """Show the operator fact when the branch moves the mutmut pin it rests on."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.MUTMUT_OPERATORS, repo_root):
        return ExitStatus(0)
    return check()


if __name__ == "__main__":
    sys.exit(main())
