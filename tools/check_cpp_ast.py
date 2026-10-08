# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Refuse what AGENTS/cpp.md rules out on the C++ AST, parsing each unit once.

Two rules match on the AST: a declaration restating a type its initializer
already fixes (cat 34, ``tools/check_cpp_restated_types.py``) and a read of a
state a check has ruled out made other than in its checked form (cat 24,
``tools/check_cpp_checked_reads.py``).  Each rule is a query fragment, opening
with the traversal it reads, and a judge of what clang-query printed.  The
query here is every fragment in turn, so clang-query parses a unit once for
all the rules, the parse being most of the time a rule takes; every unit's
output then goes to every judge, each printing what it refuses, and the run
fails when any judge does.

Run: ``python -m tools.check_cpp_ast`` (exit 0 = clean, 1 = findings).
"""

from __future__ import annotations

import argparse
import sys
from typing import TYPE_CHECKING, NamedTuple

from tools import check_cpp_checked_reads, check_cpp_restated_types
from tools._clang_query import Query, query_units, translation_units
from tools._common import emit, git_toplevel

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path

    from tools._clang_query import QueryOutput


class AstRule(NamedTuple):
    """One rule: its query fragment, and the judge of every unit's output."""

    query: Query
    judge: Callable[[Path, list[QueryOutput]], ExitStatus]


RULES = (
    AstRule(check_cpp_restated_types.QUERY, check_cpp_restated_types.judge),
    AstRule(check_cpp_checked_reads.QUERY, check_cpp_checked_reads.judge),
)

# clang-query prints each match as a diagnostic naming what it binds, and each
# rule reads only the names its own matchers bind.
QUERY = Query("".join(rule.query for rule in RULES))


def verdict(repo: Path, outputs: list[QueryOutput], rules: tuple[AstRule, ...]) -> ExitStatus:
    """Hand every unit's output to every rule's judge; 1 when any of them refuses."""
    return max(rule.judge(repo, outputs) for rule in rules)


def main() -> ExitStatus:
    """Parse every unit once and judge it by every rule; 0 when all are clean, 1 otherwise."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    repo = git_toplevel()
    units = translation_units(repo)
    if isinstance(units, str):
        emit(units)
        return ExitStatus(1)
    outputs = query_units(repo, units, QUERY)
    if isinstance(outputs, str):
        emit(outputs)
        return ExitStatus(1)
    return verdict(repo, outputs, RULES)


if __name__ == "__main__":
    sys.exit(main())
