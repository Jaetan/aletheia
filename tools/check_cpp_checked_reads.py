# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Refuse a read of a state a check has ruled out, unless the read is checked.

AGENTS/cpp.md cat 24: the library reads every value of an optional or an
expected through ``value()``, every subscript, front and back of a vector, an
array or a string through ``at()``, every error of an expected through
``detail::error_of``, every slice of a span through ``detail::subspan_at`` and
every narrowing of a string view through ``substr()``, so a check that stops
firing throws on every build instead of reading memory the program does not
own.  A span's front and back have no checked form in C++23 and are not held.

The only unchecked reads are the two helpers' own, in
``cpp/include/aletheia/detail/checked.hpp``; the test double,
``cpp/src/detail/mock_backend.hpp``, is held out with them.  A read counts
where clang-query reports it in ``cpp/src`` or ``cpp/include``, and every unit
the build compiles is read, the tests included, since a template a public
header defines is instantiated there.  The matching is clang-query's, over the AST
as compiled: the traversal visits the instantiations, which hold the concrete
types a template's own text does not.  This rule is a query fragment and a
judge of what it prints, run by ``tools/check_cpp_ast.py`` in the one parse of
each unit it makes for every rule.

Run: ``python -m tools.check_cpp_ast`` (exit 0 = clean, 1 = findings).
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType

from tools._clang_query import CPP_ROOT, Query
from tools._common import RelPath, emit

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from tools._clang_query import QueryOutput

# The name a matcher binds its read to, which is what clang-query prints.
BindName = NewType("BindName", str)

# An AST matcher of statements, in clang-query's syntax.
Matcher = NewType("Matcher", str)

# A line of a source file, counted from 1.
LineNumber = NewType("LineNumber", int)

# How many translation units a run read.
UnitCount = NewType("UnitCount", int)


class Rule(NamedTuple):
    """One unchecked read: the name it binds, the checked form to write, its matcher."""

    bind: BindName
    checked: Prose
    matcher: Matcher


class Read(NamedTuple):
    """One unchecked read the query bound: where it is, and which rule it breaks."""

    file: RelPath
    line: LineNumber
    bind: BindName


RULES = (
    Rule(
        BindName("unchecked value"),
        Prose("read it through value()"),
        Matcher("""cxxOperatorCallExpr(
  anyOf(hasOverloadedOperatorName("*"), hasOverloadedOperatorName("->")),
  hasArgument(0, expr(hasType(hasUnqualifiedDesugaredType(recordType(hasDeclaration(
    classTemplateSpecializationDecl(anyOf(
      hasName("::std::optional"), hasName("::std::expected"))))))))))"""),
    ),
    Rule(
        BindName("unchecked error"),
        Prose("read it through detail::error_of"),
        Matcher("""cxxMemberCallExpr(callee(cxxMethodDecl(
  hasName("error"),
  ofClass(classTemplateSpecializationDecl(hasName("::std::expected"))))))"""),
    ),
    Rule(
        BindName("unchecked subscript"),
        Prose("read it through at()"),
        Matcher("""cxxOperatorCallExpr(
  hasOverloadedOperatorName("[]"),
  hasArgument(0, expr(hasType(hasUnqualifiedDesugaredType(recordType(hasDeclaration(
    classTemplateSpecializationDecl(anyOf(
      hasName("::std::vector"), hasName("::std::array"),
      hasName("::std::basic_string"), hasName("::std::basic_string_view"))))))))))"""),
    ),
    Rule(
        BindName("unchecked slice"),
        Prose("slice it through detail::subspan_at"),
        Matcher("""cxxMemberCallExpr(callee(cxxMethodDecl(
  anyOf(hasName("subspan"), hasName("first"), hasName("last")),
  ofClass(classTemplateSpecializationDecl(hasName("::std::span"))))))"""),
    ),
    Rule(
        BindName("unchecked narrowing"),
        Prose("narrow it through substr()"),
        Matcher("""cxxMemberCallExpr(callee(cxxMethodDecl(
  anyOf(hasName("remove_prefix"), hasName("remove_suffix")),
  ofClass(classTemplateSpecializationDecl(hasName("::std::basic_string_view"))))))"""),
    ),
    Rule(
        BindName("unchecked end"),
        Prose("read it through at()"),
        Matcher("""cxxMemberCallExpr(callee(cxxMethodDecl(
  anyOf(hasName("front"), hasName("back")),
  ofClass(classTemplateSpecializationDecl(anyOf(
    hasName("::std::vector"), hasName("::std::array"),
    hasName("::std::basic_string"), hasName("::std::basic_string_view")))))))"""),
    ),
)

# The library's own sources, under cpp/.  The query binds every read in the
# unit, the standard library's and the tests' included, and only these count.
SCOPED = ("src", "include")

# The checked helpers' own reads, and the test double.
EXEMPT = frozenset(
    {
        RelPath("cpp/include/aletheia/detail/checked.hpp"),
        RelPath("cpp/src/detail/mock_backend.hpp"),
    }
)

# The rule's part of the query: the traversal that visits instantiations, then
# every read bound to its own name, which keeps the diagnostics apart from
# another rule's in the output of the one parse.
QUERY = Query(
    "set traversal AsIs\n"
    + "".join(f'match {rule.matcher}.bind("{rule.bind}")\n' for rule in RULES)
)

# The checked form each bind name is read through instead.
_CHECKED = {rule.bind: rule.checked for rule in RULES}

_LOCATION = re.compile(r'^(/[^\s:]+):(\d+):\d+: note: "([a-z ]+)" binds here$', re.MULTILINE)


def reads_in(repo: Path, output: QueryOutput) -> list[Read]:
    """Read every unchecked read clang-query bound out of its diagnostics."""
    reads: list[Read] = []
    for location in _LOCATION.finditer(output):
        path, bind = Path(location.group(1)), BindName(location.group(3))
        if bind not in _CHECKED:
            continue
        if not any(path.is_relative_to(repo / CPP_ROOT / scoped) for scoped in SCOPED):
            continue
        file = RelPath(str(path.relative_to(repo)))
        if file not in EXEMPT:
            reads.append(Read(file, LineNumber(int(location.group(2))), bind))
    return reads


def report(reads: set[Read], units: UnitCount) -> ExitStatus:
    """Print every unchecked read and the checked form it takes; return the exit status."""
    for read in sorted(reads):
        emit(f"{read.file}:{read.line}: {read.bind}: {_CHECKED[read.bind]}")
    if reads:
        emit(f"{len(reads)} unchecked reads of a ruled-out state (AGENTS/cpp.md cat 24)")
        return ExitStatus(1)
    emit(f"every read of a ruled-out state is checked over {units} units")
    return ExitStatus(0)


def judge(repo: Path, outputs: list[QueryOutput]) -> ExitStatus:
    """Read every unit's output for an unchecked read; 0 when there is none, 1 otherwise."""
    reads = {read for output in outputs for read in reads_in(repo, output)}
    return report(reads, UnitCount(len(outputs)))
