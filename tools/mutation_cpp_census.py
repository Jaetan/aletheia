# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Two rules the C++ lane holds on the census of every sweep over the whole tree.

The bool-call twin.  ``cpp/mull.yml`` sweeps ``cxx_replace_bool_call_true``,
which answers a bool-returning call with true, beside
``cxx_replace_scalar_call``, whose constant truncates to false on a boolean,
so a bool-returning call is tested for answering yes and for answering no.
The two are made at one start, and a bool-call site with no scalar twin
there is a call tested for one answer only; a census with no bool-call site
is the replacement made nowhere.

The identifier.  The plugin carries its unique-identifier build, which gives
every clone of a span a name of its own, the hash and the ordinal that end
``<mutator>:<path>:<line>:<column>:<line>:<column>:<hash>.<ordinal>``.  An
identifier without that seventh part is a plugin built without it, under
which two clones share one name and the merge of the slices cannot tell them
apart; one not under its own mutator and file is a report the lane did not
write.

Both read off the census every sweep already writes, so they cost the lane
nothing; ``tools/mutation_cpp.py`` applies them beside the pointer-call rule
once the reports are written.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NewType

from tools.mutation_cpp_elements import MullPath, MutatorName, repo_relative

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Sequence

    from tools._common import RelPath
    from tools.mutation_cpp_elements import ColumnNumber, ElementsFiles, LineNumber, MutantId

BOOL_CALL_MUTATOR = MutatorName("cxx_replace_bool_call_true")
SCALAR_CALL_MUTATOR = MutatorName("cxx_replace_scalar_call")
# How many offenders a refusal names before it counts the rest.
NAMED_OFFENDERS = 10
# The shape of an identifier the unique-identifier build writes.
_IDENTIFIER = re.compile(r"^[a-z_]+:.+:\d+:\d+:\d+:\d+:[0-9a-f]{1,8}\.\d+$")

# Where a mutant starts: its repository-relative file, line and column.
type Site = tuple[RelPath, LineNumber, ColumnNumber]
# How a refusal names one offender: a site, or an identifier with its path made repository-relative.
Offender = NewType("Offender", str)


def _sites(files: ElementsFiles, mutator: MutatorName) -> set[Site]:
    """Collect where a mutator's mutants start."""
    return {
        (
            repo_relative(path),
            mutant["location"]["start"]["line"],
            mutant["location"]["start"]["column"],
        )
        for path, entry in files.items()
        for mutant in entry["mutants"]
        if mutant["mutatorName"] == mutator
    }


def _named(offenders: Sequence[Offender]) -> Prose:
    """Name the first offenders and count the rest."""
    rest = len(offenders) - NAMED_OFFENDERS
    return Prose(", ".join(offenders[:NAMED_OFFENDERS]) + (f" and {rest} more" if rest > 0 else ""))


def bool_call_refusal(files: ElementsFiles) -> Prose | None:
    """Refuse a census that breaks the bool-call twin rule, or return None where it holds.

    ``files`` is an Elements report's ``files``.  A refusal names the orphan
    sites, in file and line order, by repository-relative file, line and column.
    """
    bool_sites = _sites(files, BOOL_CALL_MUTATOR)
    if not bool_sites:
        return Prose(
            f"the census carries no {BOOL_CALL_MUTATOR} mutant: the plugin makes the "
            + "bool-call replacement cpp/mull.yml sweeps nowhere"
        )
    orphans = sorted(bool_sites - _sites(files, SCALAR_CALL_MUTATOR))
    if not orphans:
        return None
    named = _named([Offender(f"{file}:{line}:{column}") for file, line, column in orphans])
    return Prose(
        f"{len(orphans)} {BOOL_CALL_MUTATOR} sites with no {SCALAR_CALL_MUTATOR} twin, each a "
        + f"bool-returning call tested for one answer only: {named}"
    )


def _short(ident: MutantId) -> Offender:
    """Cut the path inside an identifier at its first ``/cpp/``, as ``repo_relative`` does."""
    mutator, colon, rest = ident.partition(":")
    return Offender(f"{mutator}{colon}{repo_relative(MullPath(rest))}")


def identifier_refusal(files: ElementsFiles) -> Prose | None:
    """Refuse a census whose identifiers are not the plugin's, or return None where they are.

    ``files`` is an Elements report's ``files``.  An identifier fails on its
    shape, which lacks the seventh part, or on its prefix, which is not its
    mutator and its file; the refusal names each half's offenders in report
    order.
    """
    shapeless: list[MutantId] = []
    misplaced: list[MutantId] = []
    for path, entry in files.items():
        for mutant in entry["mutants"]:
            ident = mutant["id"]
            if _IDENTIFIER.match(ident) is None:
                shapeless.append(ident)
            elif not ident.startswith(f"{mutant['mutatorName']}:{path}:"):
                misplaced.append(ident)
    halves: list[Prose] = []
    if shapeless:
        halves.append(
            Prose(
                f"{len(shapeless)} identifiers with no seventh part, the plugin built without "
                + f"its unique identifiers: {_named([_short(i) for i in shapeless])}"
            )
        )
    if misplaced:
        halves.append(
            Prose(
                f"{len(misplaced)} identifiers not under their mutator and file: "
                + _named([_short(i) for i in misplaced])
            )
        )
    return Prose("; ".join(halves)) if halves else None
