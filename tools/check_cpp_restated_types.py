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

The instrument is ``clang-query``, which ships with ``clang-tidy`` (the
``clang-tidy-23`` package Depends on ``clang-tools-23``), so wherever the lint
gate runs this one can.  It reads the same compile database, so it runs in the
cpp lane after the build that writes it, beside ``check_clang_tidy_coverage``.

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

Run: ``python -m tools.check_cpp_restated_types`` (exit 0 = clean, 1 = findings).
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import NamedTuple, NewType, cast

from tools._common import emit, git_toplevel
from tools._ratchet import CanonicalText, RatchetRows, RelPath, RowKey, as_row, read_ratchet_rows

# A translation unit as the compile database names it, relative to `cpp/`;
# `translation_units` is what mints one, from that database.
UnitPath = NewType("UnitPath", str)


class Hit(NamedTuple):
    """One declaration the matcher bound: where it is, and its text."""

    file: RelPath
    line: int
    text: CanonicalText


# The ratchet's record, repo-root-relative.
ALLOWLIST = Path("docs") / "CPP_RESTATED_TYPES.yaml"

# The compile database the binding's own build writes, and the directory
# clang-query resolves it from.
CPP_ROOT = Path("cpp")
BUILD_DIR = "build"
COMPILE_DB = CPP_ROOT / BUILD_DIR / "compile_commands.json"

# The lint gate names the same version, and clang-query comes with it.
CLANG_QUERY = "clang-query-23"

# Third-party sources the build fetches; the standards cover cpp/ itself.
VENDORED = "/build/_deps/"

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

# clang-query's diagnostic block: the location, the source line, then the caret
# run spanning the bound node.  The caret line is what gives the declaration's
# extent; nothing else in the output does.
_LOCATION = re.compile(r"^(/[^\s:]+):(\d+):(\d+): note: \"root\" binds here$")
_NUMBERED = re.compile(r"^\s*\d+ \| (.*)$")
_CARET = re.compile(r"^\s*\| (\s*)(\^~*)\s*$")
# A diagnostic clang-query prints for a unit it could not parse; its exit code
# does not carry it.
_ERROR = re.compile(r"^.*\berror: .*$", re.MULTILINE)

# A macro invocation, which is what stands at the expansion location of a
# declaration a macro wrote.  No declaration begins this way.
_MACRO_CALL = re.compile(r"^[A-Z][A-Z0-9_]{2,}\s*\(")


def translation_units(repo: Path) -> list[UnitPath] | str:
    """Return the binding's own translation units, or why they cannot be read."""
    database = repo / COMPILE_DB
    if not database.is_file():
        return (
            f"{COMPILE_DB} is missing, so the gate cannot run.  Configure the"
            f" binding first: cd {CPP_ROOT} && cmake -B {BUILD_DIR}"
            " -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23"
        )
    entries: object = json.loads(database.read_text(encoding="utf-8"))
    if not isinstance(entries, list):
        return f"{COMPILE_DB} is not a list of compile commands"
    units = {
        str(cast("dict[str, object]", entry).get("file", ""))
        for entry in cast("list[object]", entries)
        if isinstance(entry, dict)
    }
    return sorted(UnitPath(unit) for unit in units if unit and VENDORED not in unit)


def run_matcher(repo: Path, script: Path, unit: UnitPath) -> list[Hit] | str:
    """Match one translation unit, returning its hits or why the run failed."""
    try:
        finished = subprocess.run(
            [CLANG_QUERY, "-p", BUILD_DIR, "-f", str(script), unit],
            cwd=repo / CPP_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as failure:
        return f"{CLANG_QUERY} could not be run ({failure}); it ships with clang-tidy-23"
    if finished.returncode != 0:
        detail = (finished.stderr or finished.stdout).strip().splitlines()
        return f"{CLANG_QUERY} failed on {unit}: {detail[0] if detail else 'no output'}"
    # clang-query exits zero after a fatal diagnostic, a header it could not
    # find included, and matches nothing in the unit it could not parse; read
    # as clean, that unit's declarations would vanish from the gate.
    diagnostic = _ERROR.search(finished.stderr)
    if diagnostic is not None:
        return f"{CLANG_QUERY} could not parse {unit}: {diagnostic.group(0).strip()}"
    return parse_hits(repo, finished.stdout)


def parse_hits(repo: Path, output: str) -> list[Hit]:
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


def observed_rows(repo: Path, units: list[UnitPath]) -> RatchetRows | str:
    """Count the tree's restating declarations, keyed by file and source text."""
    with TemporaryDirectory() as scratch:
        script = Path(scratch) / "restated.query"
        script.write_text(f"{TRAVERSAL}\nset output diag\nmatch {MATCHER}\n", encoding="utf-8")

        def match(unit: UnitPath) -> list[Hit] | str:
            return run_matcher(repo, script, unit)

        with ThreadPoolExecutor() as pool:
            results = list(pool.map(match, units))
    seen: set[Hit] = set()
    for result in results:
        if isinstance(result, str):
            return result
        seen.update(result)
    rows: RatchetRows = {}
    for hit in seen:
        key = RowKey(hit.file, hit.text)
        rows[key] = rows.get(key, 0) + 1
    return rows


def report(observed: RatchetRows, recorded: RatchetRows) -> int:
    """Print every unrecorded declaration and every stale row; return the exit code."""
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
        return 1
    emit(f"C++ declarations restating their type: {sum(observed.values())}, every one recorded")
    return 0


def main() -> int:
    """Compare the tree's restating declarations against the record; 0 clean, 1 not."""
    repo = git_toplevel()
    recorded = read_ratchet_rows(repo, ALLOWLIST, "declarations")
    if isinstance(recorded, str):
        emit(recorded)
        return 1
    units = translation_units(repo)
    if isinstance(units, str):
        emit(units)
        return 1
    observed = observed_rows(repo, units)
    if isinstance(observed, str):
        emit(observed)
        return 1
    return report(observed, recorded)


if __name__ == "__main__":
    sys.exit(main())
