# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Refuse a C++ declaration that restates a type its initializer already fixes.

AGENTS/cpp.md cat 34, "deduce the type, do not restate it": a type written
beside an initializer that already determines it states one fact twice, and the
two halves drift.  When the initializer's type changes the declaration goes on
compiling, converting or narrowing at a line nobody edited, which is the same
quiet failure cat 27 records for a hand-written loop bound.

``modernize-use-auto`` does not cover the class.  It fires on a ``new``
expression, an explicit cast and an iterator declaration, which are the
declarations whose written type cannot disagree with anything, and says nothing
about one initialised from a call.  Probed on a declaration initialised from a
call and on a loop counter that names its own type, it emits nothing.

The instrument is ``clang-query``: this rule is a query fragment and a judge
of what it prints, run by ``tools/check_cpp_ast.py`` in the one parse of each
translation unit it makes for every rule.

What it reports is narrower than the rule, deliberately: a declaration where
``auto`` would deduce the written type *exactly*.  The matcher compares the
declaration's unqualified desugared type against the initializer's own, with
implicit conversions and elidable constructors stripped, so substituting
``auto`` at a reported site cannot change a type.  That is what makes the pass
mechanical: every judgement left is whether the written type carries a decision.

Three shapes are outside the class rather than exceptions to it:

* an initializer built from literals alone.  ``constexpr int k_json_indent = 2``
  fixes the type by writing it, the literal's own type following its spelling,
  so deducing there would move the decision into a suffix;
* a braced or list initializer, a lambda, and a constructor call the
  declaration itself drives, where the initializer's type is the declared one
  because the declaration said so, not the other way round;
* a declaration a macro expands to.  Catch2's test registrars are declarations
  no one wrote, and the record cannot name a line that is not in the source.

It is a ratchet, not a ban: the YAML records the declarations that keep their
written type because the type is a decision deduction would erase, and both
directions are enforced, because a row whose declaration is gone is standing
permission to write it again:

* a restating declaration the YAML does not name fails the gate, which prints
  the row that would allow it.  Adding that row needs user approval, on the
  same footing as a ``NOLINT`` suppression;
* a row naming more declarations than the tree holds fails the gate, which
  prints the row to delete.  The change that deduces a type deletes its row.

Rows are keyed by file and by the declaration's source text rather than by a
line number, so an edit elsewhere in the file does not churn the YAML; where
one file holds several identical declarations the row carries how many, as the
index-loop record and the mutation lane's survivor ledger do.

Run: ``python -m tools.check_cpp_ast`` (exit 0 = clean, 1 = findings).
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

from tools._clang_query import CPP_ROOT, Query
from tools._common import emit
from tools._ratchet import CanonicalText, RatchetRows, RelPath, RowKey, as_row, read_ratchet_rows

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from tools._clang_query import QueryOutput


class Hit(NamedTuple):
    """One declaration the matcher bound: where it is, and its text."""

    file: RelPath
    line: int
    text: CanonicalText


# The ratchet's record, repo-root-relative.
ALLOWLIST = Path("docs") / "CPP_RESTATED_TYPES.yaml"

# The directories AGENTS/cpp.md scopes the C++ standards to.  The matcher names
# them too, as a regex over the expansion file, and a hit is checked against
# this set as well: a regex matches a substring wherever it occurs, and a
# vendored path is only a directory name away from reading as one of ours.
SCOPED = ("src", "include", "tests", "benchmarks")

# The initializer is read as it is written, not as the compiler rebuilt it.  In
# the default traversal the implicit nodes are there to be stripped, and
# stripping them walks straight through a user-defined conversion: OpenXLSX's
# cell accessor hands back a proxy, and the conversion operator the declaration
# calls has the declared type, so the two would compare equal while `auto` would
# deduce the proxy and dangle.  Spelled-in-source leaves the written expression,
# which is the one `auto` sees.
TRAVERSAL = "set traversal IgnoreUnlessSpelledInSource"

# The class, as an AST matcher.  Each clause is load-bearing:
#   isExpansionInFileMatching  our own four directories, not the toolchain's
#                              headers, which the compile database drags in;
#   unless(parmVarDecl)        a parameter's type is its function's interface;
#   unless(isImplicit)         a declaration the compiler made has no source;
#   the four autoType clauses  one already deduced is not a finding, and a
#                              declaration is `auto*` or `auto const*` as often
#                              as it is plain `auto`, where the deduced type
#                              sits under the pointer rather than at the top;
#   the initializer clauses    refuse the shapes whose type the declaration
#                              fixes, and require at least one name or call,
#                              which is what tells a deduced type from one a
#                              literal's spelling fixes;
#   the two canonical-type clauses  equate the written type with the
#                              initializer's own, through typedefs and past
#                              top-level qualifiers, which is exactly the
#                              comparison `auto` would make.  Canonical is
#                              load-bearing: on a sugared type `equalsBoundNode`
#                              compares two spellings of one type as different
#                              nodes and the match silently disappears, which is
#                              a gate that under-reports rather than one that
#                              fails.  The declaration binds and the initializer
#                              compares, so the bind is in hand before the
#                              comparison runs.
MATCHER = """
varDecl(
  isExpansionInFileMatching("/cpp/(src|include|tests|benchmarks)/"),
  unless(parmVarDecl()),
  unless(isImplicit()),
  unless(hasType(autoType())),
  unless(hasType(pointsTo(autoType()))),
  unless(hasType(pointsTo(pointsTo(autoType())))),
  unless(hasType(references(autoType()))),
  hasType(qualType(hasCanonicalType(hasUnqualifiedDesugaredType(type().bind("t"))))),
  hasInitializer(
    expr(
      unless(anyOf(initListExpr(), cxxStdInitializerListExpr(), lambdaExpr(),
                   allOf(cxxConstructExpr(), unless(cxxTemporaryObjectExpr())))),
      anyOf(declRefExpr(), callExpr(), memberExpr(),
            hasDescendant(expr(anyOf(declRefExpr(), callExpr(), memberExpr())))),
      hasType(qualType(hasCanonicalType(hasUnqualifiedDesugaredType(
        type(equalsBoundNode("t"))))))
    )
  )
)
"""

# The name the declaration is bound to, which keeps this rule's diagnostics
# apart from another rule's in the output of the one parse.
BIND = "restated declaration"

# The rule's part of the query, opening with the traversal it reads.
QUERY = Query(f'{TRAVERSAL}\nmatch {MATCHER.strip()}.bind("{BIND}")\n')

# clang-query's diagnostic block: the location, the source line, then the caret
# run spanning the bound node.  The caret line is what gives the declaration's
# extent; nothing else in the output does.
_LOCATION = re.compile(rf'^(/[^\s:]+):(\d+):(\d+): note: "{BIND}" binds here$')
_NUMBERED = re.compile(r"^\s*\d+ \| (.*)$")
_CARET = re.compile(r"^\s*\| (\s*)(\^~*)\s*$")

# A macro invocation, which is what stands at the expansion location of a
# declaration a macro wrote.  No declaration begins this way.
_MACRO_CALL = re.compile(r"^[A-Z][A-Z0-9_]{2,}\s*\(")


def parse_hits(repo: Path, output: QueryOutput) -> list[Hit]:
    """Read every declaration clang-query bound out of its diagnostics."""
    hits: list[Hit] = []
    lines = output.splitlines()
    for index, line in enumerate(lines):
        location = _LOCATION.match(line)
        if location is None or index + 2 >= len(lines):
            continue
        source = _NUMBERED.match(lines[index + 1])
        caret = _CARET.match(lines[index + 2])
        if source is None or caret is None:
            continue
        start = len(caret.group(1))
        text = collapse(source.group(1)[start : start + len(caret.group(2))])
        if not text or _MACRO_CALL.match(text):
            continue
        path = Path(location.group(1))
        if not any(path.is_relative_to(repo / CPP_ROOT / scoped) for scoped in SCOPED):
            continue
        hits.append(Hit(RelPath(str(path.relative_to(repo))), int(location.group(2)), text))
    return hits


def collapse(text: str) -> CanonicalText:
    """Collapse a declaration's whitespace within the line the caret marks.

    A reflow that keeps the declaration on one line does not move its row; one
    that wraps it does, because the caret run spans a single source line and
    the text is read from that line alone.
    """
    return CanonicalText(" ".join(text.split()))


def observed_rows(repo: Path, outputs: list[QueryOutput]) -> RatchetRows:
    """Count the tree's restating declarations, keyed by file and source text."""
    seen = {hit for output in outputs for hit in parse_hits(repo, output)}
    rows: RatchetRows = {}
    for hit in seen:
        key = RowKey(hit.file, hit.text)
        rows[key] = rows.get(key, 0) + 1
    return rows


def report(observed: RatchetRows, recorded: RatchetRows) -> ExitStatus:
    """Print every unrecorded declaration and every stale row; return the exit status."""
    unrecorded = sorted(key for key, n in observed.items() if n > recorded.get(key, 0))
    stale = sorted(key for key, n in recorded.items() if n > observed.get(key, 0))
    for file, text in unrecorded:
        emit(f"{file}: a declaration restates a type its initializer already fixes")
        emit(f"    {text}")
        emit("  Write it auto (AGENTS/cpp.md cat 34, in the spelling cat 5 fixes), or,")
        emit(f"  with user approval, add this row to {ALLOWLIST}:")
        emit(as_row(file, text, observed[RowKey(file, text)]))
    for file, text in stale:
        emit(f"{file}: a recorded row names more declarations than the file holds")
        emit(f"    {text}")
        emit(f"  Its type is deduced now: drop the row from {ALLOWLIST}, or lower its")
        emit(f"  count to {observed.get(RowKey(file, text), 0)}, in the change that deduced it.")
    if unrecorded or stale:
        emit(f"{len(unrecorded)} unrecorded, {len(stale)} stale")
        return ExitStatus(1)
    emit(f"C++ declarations restating their type: {sum(observed.values())}, every one recorded")
    return ExitStatus(0)


def judge(repo: Path, outputs: list[QueryOutput]) -> ExitStatus:
    """Compare the tree's restating declarations against the record; 0 clean, 1 not."""
    recorded = read_ratchet_rows(repo, ALLOWLIST, "declarations")
    if isinstance(recorded, str):
        emit(recorded)
        return ExitStatus(1)
    return report(observed_rows(repo, outputs), recorded)
