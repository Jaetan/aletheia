# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Refuse a C++ local that is never written and is not declared const.

AGENTS/cpp.md cat 5 asks for const wherever it can stand.  The lint gate's
``misc-const-correctness`` does not hold that on this tree: it passes over a
local whose type is named through a using-declaration (the type's declaration
is then a UsingShadowDecl, which the check's allowed-type matcher accepts), a
local a lambda captures by reference, and a local handed to a library template
that binds it to a non-const reference, ``std::format`` and Catch2's assertion
macros among them.  A clean clang-tidy run therefore says nothing about such
locals, so this gate asks the compiler.

clang-query lists every candidate the lint tree's units declare: a local of
automatic or static storage that is not const (a constexpr one is), not a parameter,
a reference or a pointer (the lint check leaves a pointer's own constness
alone, and so does this gate), and not one the compiler declares itself.  A
declaration that spells no type before its name, an init-capture or a macro's
expansion, takes no const word and is skipped; one declaration declares one
local, which readability-isolate-declaration holds.  Each file's candidates are
declared const in a copy of the file that a VFS overlay puts in the original's
place, and one unit that includes the file is syntax-checked; a candidate the
compiler accepts is a finding.  The tree itself is never written.

Some locals compile as const and must not be const, and the query excludes
them before anything is compiled:

* a local an argument of ``std::move`` mentions, or one a range-``for``
  iterates while moving from its element: const turns the move into a copy;
* a local a return or a throw names, parenthesized or not, and moves from
  implicitly: const turns that move into a copy;
* a JSON document (nlohmann's ``basic_json``) read through ``operator[]``: its
  const ``operator[]`` reads past the end on a missing key where the non-const
  one inserts a null, so const changes what a missing key does.

The last is the second rule here: ``operator[]`` on a const JSON document is
refused outright, since a missing key is undefined behaviour; read it with
``at()``.

The compile is the cost, so a file is compiled with every candidate const at
once, and each failure settles what it can: a declaration the compiler names as
declared const; the object of a member call or an operator the compiler says is
const; or the one pending local an error line, or an instantiation's "requested
here" line, names.  A name is read as the nearest pending declaration of it
above the line, since a test file declares one name in case after case.  The
settled candidates are written and the rest compile again; a round that settles
none splits what is left in two, down to single candidates.  A misreading can
only settle a candidate that was const-able as written, which under-reports and
never refuses a local wrongly.  Candidates are assumed independent, which a
declaration that only fails beside another breaks; the bisection still ends, at
the single candidates.

The fuzz harnesses build in a tree of their own, with the fuzzer's
instrumentation, and are outside the lint tree's database and so outside this
gate.

An exemption is a row of ``docs/CPP_CONST_LOCALS.yaml``, keyed by file and by
the declaration's text, enforced both ways as the other C++ ratchets are; a row
needs user approval, on the same footing as a ``NOLINT`` suppression.

Run: ``python -m tools.check_cpp_const_locals`` (exit 0 = clean, 1 = findings, or
the lint tree or the record could not be read, 2 = a refused option).
"""

from __future__ import annotations

import argparse
import functools
import json
import os
import re
import shlex
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, NotRequired, TypedDict, cast

from tools._clang_query import (
    COMPILE_DB,
    CPP_ROOT,
    PrintedPath,
    Query,
    printed_file,
    query_tree,
)
from tools._common import RelPath, WorkerCount, emit
from tools._ratchet import CanonicalText, RatchetRows, RowKey, as_row, read_ratchet_rows

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable

    from tools._clang_query import QueryOutput, UnitPath
    from tools._common import ExecutorFactory

# The ratchet's record, repo-root-relative.
ALLOWLIST = Path("docs") / "CPP_CONST_LOCALS.yaml"

# The directories AGENTS/cpp.md scopes the C++ standards to, as in the sibling
# AST gates: the matcher names them as a regex and a hit is held to the set.
SCOPED = ("src", "include", "tests", "benchmarks")

# A binding the query prints, and a fragment of an AST matcher.
BindName = NewType("BindName", str)
Matcher = NewType("Matcher", str)

# The bindings, one per kind of node the query reports.
CANDIDATE = BindName("candidate")
EXCLUDED = (BindName("moved"), BindName("returned"), BindName("thrown"), BindName("json_indexed"))
CONST_JSON_READ = BindName("const_json_read")
# The function a candidate is declared in, a lambda's body counting as its enclosing function's.
SCOPE = BindName("scope")

_OWN = Matcher('isExpansionInFileMatching("/cpp/(src|include|tests|benchmarks)/")')
_MOVE = Matcher('callee(functionDecl(hasName("::std::move")))')
_JSON = Matcher(
    'hasUnqualifiedDesugaredType(recordType(hasDeclaration(namedDecl(matchesName("basic_json")))))'
)


def _named(bind: BindName) -> Matcher:
    """Match a reference to a variable as ``bind``, a structured binding as its declaration."""
    return Matcher(
        f'declRefExpr(to(anyOf(varDecl().bind("{bind}"),'
        + f' bindingDecl(forDecomposition(varDecl().bind("{bind}"))))))'
    )


def _moved_out(bind: BindName) -> Matcher:
    """Match an operand a return or a throw moves from implicitly.

    The move is a constructor taking the variable, parenthesized or not: the
    result's own, or the one making the argument of the implicit conversion
    that makes the result.  A variable copied into an aggregate, passed to a
    call, named in an explicit construction, or of a type built by no
    constructor is not moved from, and is not matched.
    """
    implicit = (
        "cxxConstructExpr(unless(cxxTemporaryObjectExpr()), unless(isListInitialization()),"
        + " hasArgument(0, ignoringImplicit({})))"
    )
    once = implicit.format(_named(bind))
    return Matcher(f"expr(anyOf({once}, {implicit.format(once)}))")


# The matchers, one per kind of node the query reports.
MATCHERS = (
    f"varDecl({_OWN}, anyOf(hasLocalStorage(), isStaticLocal()), unless(parmVarDecl()),"
    + " unless(isImplicit()),"
    + " unless(hasType(isConstQualified())),"
    + " unless(hasType(hasUnqualifiedDesugaredType(referenceType()))),"
    + " unless(hasType(hasUnqualifiedDesugaredType(pointerType()))),"
    + " optionally(hasAncestor(functionDecl("
    + "unless(cxxMethodDecl(ofClass(cxxRecordDecl(isLambda())))))"
    + f'.bind("{SCOPE}")))).bind("{CANDIDATE}")',
    f"callExpr({_OWN}, {_MOVE}, hasArgument(0, expr(anyOf("
    + f"ignoringParenImpCasts({_named(EXCLUDED[0])}), hasDescendant({_named(EXCLUDED[0])})))))",
    f"cxxForRangeStmt({_OWN}, hasRangeInit(ignoringParenImpCasts({_named(EXCLUDED[0])})),"
    + ' hasLoopVariable(varDecl().bind("loop")), hasBody(hasDescendant(declRefExpr('
    + f'to(varDecl(equalsBoundNode("loop"))), hasAncestor(callExpr({_MOVE}))))))',
    f"returnStmt({_OWN}, hasReturnValue(ignoringImplicit({_moved_out(EXCLUDED[1])})))",
    # A throw's operand is its direct child: clang-query matches nothing through
    # ignoringImplicit there.
    f"cxxThrowExpr({_OWN}, has({_moved_out(EXCLUDED[2])}))",
    f'cxxOperatorCallExpr({_OWN}, hasOverloadedOperatorName("[]"), hasArgument(0,'
    + " ignoringParenImpCasts(declRefExpr(to(varDecl(hasType(qualType("
    + f'{_JSON}))).bind("{EXCLUDED[3]}"))))))',
    f'cxxOperatorCallExpr({_OWN}, hasOverloadedOperatorName("[]"), hasArgument(0,'
    + f' expr(hasType(qualType(isConstQualified(), {_JSON}))))).bind("{CONST_JSON_READ}")',
)

# The implicit casts and constructions the exclusions read are visible only to
# the traversal that keeps them.
QUERY = Query("set traversal AsIs\n" + "".join(f"match {m}\n" for m in MATCHERS))

# One binding as clang-query prints it, and the header that opens each match.
_BINDS = re.compile(r'^(/[^\s:]+):(\d+):(\d+): note: "([a-z_]+)" binds here$')
_MATCH = re.compile(r"^Match #\d+:$")

# The storage words a declaration may open with before its type.
_STORAGE = re.compile(r"^((?:(?:static|thread_local)\s+)*)")

# A structured binding's names, between its brackets.
_STRUCTURED = re.compile(r"^auto\s*&{0,2}\s*\[([^\]]*)\]")

# A compiler diagnostic, and the note that names a declaration made const.
_DIAGNOSTIC = re.compile(r"^(/[^\s:]+):(\d+):(\d+): (error|note): (.*)$")
_DECLARED_CONST = re.compile(r"^variable '(\w+)' declared const here$")

# Up to this many candidates, a round that settles none tries each alone.
SINGLES = 4

# A declaration spells a type and then its name, so it holds at least two words;
# an init-capture or a macro call, Catch2's assertion locals among them, holds one.
_TYPE_AND_NAME = 2

# A local's name; a line of a C++ source; a line and a column in one, from 1.
Name = NewType("Name", str)
SourceLine = NewType("SourceLine", str)
# A whole C++ file's text.
SourceText = NewType("SourceText", str)
LineNo = NewType("LineNo", int)
Column = NewType("Column", int)
# What a compiler printed on its error stream; one argument of a compile
# command, and a whole one as one string; the directory a command runs from.
Diagnostics = NewType("Diagnostics", str)
CompileArg = NewType("CompileArg", str)
CommandLine = NewType("CommandLine", str)
DirectoryName = NewType("DirectoryName", str)


# One line of a compiler's diagnostics, its kind and its message, and an error with
# the notes after it.
DiagnosticLine = NewType("DiagnosticLine", str)
DiagnosticKind = Literal["error", "note"]
Message = NewType("Message", str)
Report = list[DiagnosticLine]


class Position(NamedTuple):
    """A line and a column of one file."""

    line: LineNo
    column: Column


class Said(NamedTuple):
    """One diagnostic line in the candidates' file: its kind, its message, where it stands."""

    kind: DiagnosticKind
    message: Message
    at: Position


class Site(NamedTuple):
    """Where a declaration begins: the repo-relative file, its line and column."""

    file: RelPath
    line: LineNo
    column: Column


class Candidate(NamedTuple):
    """One local the query reports: its names, a unit reaching it, where its function opens."""

    site: Site
    names: tuple[Name, ...]
    text: CanonicalText
    unit: UnitPath
    scope: LineNo


class Bound(NamedTuple):
    """One binding of a match: the file it is in, and where it begins."""

    path: Path
    site: Site


# One match's bindings, by name.
Block = dict[BindName, Bound]


class FileView(NamedTuple):
    """What attribution reads of one file: its lines, pending candidates and function openings."""

    lines: list[SourceLine]
    pending: frozenset[Candidate]
    scopes: tuple[LineNo, ...]


class Scan(NamedTuple):
    """What the query found: the candidates left after the exclusions, and the const JSON reads."""

    candidates: list[Candidate]
    const_json_reads: list[Site]


class Compiled(NamedTuple):
    """One syntax check: whether it passed, and what the compiler printed."""

    ok: bool
    diagnostics: Diagnostics


class DatabaseEntry(TypedDict):
    """One compile database entry, as CMake writes it."""

    file: UnitPath
    directory: DirectoryName
    arguments: NotRequired[list[CompileArg]]
    command: NotRequired[CommandLine]


class CompileCommand(NamedTuple):
    """How the compile database builds one unit: its arguments, from its directory."""

    arguments: list[CompileArg]
    directory: Path


def declared_names(text: SourceLine) -> tuple[Name, ...]:
    """Read the names a declaration starting ``text`` declares; empty when it is no declaration.

    The name is the last identifier before the declarator's initializer, a
    structured binding's names are the ones its brackets list, a range-``for``
    declaration ends at its colon, and a ``decltype`` names a type rather than
    opening a declarator's arguments.
    """
    storage = _STORAGE.match(text)
    rest = text[storage.end() if storage else 0 :]
    structured = _STRUCTURED.match(rest)
    if structured is not None:
        return tuple(Name(part.strip()) for part in structured.group(1).split(","))
    depth = 0
    end = len(rest)
    for index, char in enumerate(rest):
        if char in "<([":
            if depth == 0 and char in "([" and not rest[:index].rstrip().endswith("decltype"):
                end = index
                break
            depth += 1
        elif char in ">)]":
            depth -= 1
        elif depth == 0 and (
            char in "={;" or (char == ":" and rest[index - 1 : index + 2].count(":") == 1)
        ):
            end = index
            break
    words = re.findall(r"[A-Za-z_]\w*", rest[:end])
    return (Name(words[-1]),) if len(words) >= _TYPE_AND_NAME else ()


def constify(text: SourceLine) -> SourceLine:
    """Make the declaration starting ``text`` const: `auto const`, or `const T` for a named type."""
    storage = _STORAGE.match(text)
    words = storage.group(1) if storage else ""
    rest = text[len(words) :]
    if re.match(r"auto\b", rest):
        return SourceLine(f"{words}auto const{rest[len('auto') :]}")
    return SourceLine(f"{words}const {rest}")


def collapse(text: SourceLine) -> CanonicalText:
    """Collapse a declaration's whitespace, the spelling the record keys it by."""
    return CanonicalText(" ".join(text.split()))


def _in_scope(repo: Path, path: Path) -> bool:
    """Whether a reported file is one of the project's own."""
    return any(path.is_relative_to(repo / CPP_ROOT / scoped) for scoped in SCOPED)


def scan(repo: Path, units: list[UnitPath], outputs: list[QueryOutput]) -> Scan:
    """Read the candidates and the const JSON reads out of every unit's query output.

    clang-query prints each match as a block opening on a ``Match #`` header, its
    bindings one note each; a candidate's function is the ``scope`` binding of
    its own block.
    """
    found: dict[Site, Candidate] = {}
    excluded: set[Site] = set()
    reads: set[Site] = set()
    for unit, output in zip(units, outputs, strict=True):
        for block in _blocks(output):
            for kind, (path, where) in block.items():
                if not _in_scope(repo, path):
                    continue
                site = Site(RelPath(str(path.relative_to(repo))), where.line, where.column)
                if kind == CONST_JSON_READ:
                    reads.add(site)
                elif kind in EXCLUDED:
                    excluded.add(site)
                elif kind == CANDIDATE and site not in found:
                    candidate = _candidate_at(site, _lines_of(path), unit, block.get(SCOPE))
                    if candidate is not None:
                        found[site] = candidate
    candidates = [candidate for site, candidate in sorted(found.items()) if site not in excluded]
    return Scan(candidates, sorted(reads))


@functools.cache
def _lines_of(path: Path) -> tuple[SourceLine, ...]:
    """Return a file's lines, read once however many units report it."""
    return tuple(SourceLine(text) for text in path.read_text(encoding="utf-8").split("\n"))


def _candidate_at(
    site: Site, lines: tuple[SourceLine, ...], unit: UnitPath, scope: Bound | None
) -> Candidate | None:
    """Build the candidate a binding names, or None where its text spells no type and name."""
    start = SourceLine(lines[site.line - 1][site.column - 1 :])
    names = declared_names(start)
    if not names:
        return None
    opens = scope.site.line if scope is not None else LineNo(0)
    return Candidate(site, names, collapse(start), unit, opens)


def _blocks(output: QueryOutput) -> list[Block]:
    """Each match's bindings, by name: the file each is in and where it begins."""
    blocks: list[Block] = []
    for line in output.splitlines():
        if _MATCH.match(line):
            blocks.append({})
            continue
        bound = _BINDS.match(line)
        if bound is None:
            continue
        path = printed_file(PrintedPath(bound.group(1)))
        site = Site(RelPath(str(path)), LineNo(int(bound.group(2))), Column(int(bound.group(3))))
        blocks[-1][BindName(bound.group(4))] = Bound(path, site)
    return blocks


def settled(
    compiled: Compiled,
    file: Path,
    lines: list[SourceLine],
    pending: frozenset[Candidate],
    scopes: tuple[LineNo, ...],
) -> frozenset[Candidate]:
    """Return the pending candidates a failed compile shows to be written.

    Read per error with its notes, at each line of the candidates' file the
    error or an instantiation it requested stands on: a declaration the compiler
    names as declared const; the object the column points at when the error says
    a member's or an operator's object is const; else the one pending local the
    line names.
    """
    view = FileView(lines, pending, scopes)
    written: set[Candidate] = set()
    for entry in _reports(compiled.diagnostics):
        blames_object = any(
            "'this' argument" in line or "no viable overloaded" in line for line in entry
        )
        for line in entry:
            diagnostic = _DIAGNOSTIC.match(line)
            if diagnostic is None or printed_file(PrintedPath(diagnostic.group(1))) != file:
                continue
            said = Said(
                cast("DiagnosticKind", diagnostic.group(4)),
                Message(diagnostic.group(5)),
                Position(LineNo(int(diagnostic.group(2))), Column(int(diagnostic.group(3)))),
            )
            written.update(_written_by(said, view, blames_object=blames_object))
    return frozenset(written)


def _written_by(said: Said, view: FileView, *, blames_object: bool) -> set[Candidate]:
    """Return the pending candidates one diagnostic line of the candidates' file shows written."""
    declared = _DECLARED_CONST.match(said.message)
    if declared is not None:
        name = Name(declared.group(1))
        return {c for c in view.pending if c.site.line == said.at.line and name in c.names}
    if said.kind == "note" and not said.message.endswith("requested here"):
        return set()
    if not 0 < said.at.line <= len(view.lines):
        return set()
    text = view.lines[said.at.line - 1]
    blamed = _object_at(text, said.at.column) if blames_object else None
    meant = _declaration_of(view.pending, blamed, said.at.line, view.scopes) if blamed else None
    if meant is None:
        named = {
            n for c in view.pending for n in c.names if re.search(rf"\b{re.escape(n)}\b", text)
        }
        found = {_declaration_of(view.pending, n, said.at.line, view.scopes) for n in named}
        found.discard(None)
        meant = found.pop() if len(found) == 1 else None
    return {meant} if meant is not None else set()


def _declaration_of(
    pending: frozenset[Candidate], name: Name, line: LineNo, scopes: tuple[LineNo, ...]
) -> Candidate | None:
    """Return the pending declaration a use of ``name`` on ``line`` refers to.

    A test file declares the same name in case after case, so a name alone does
    not pick a declaration; the closest one above the use, in the function the
    use is in, does.  The function is the last of the file's candidates'
    functions to open at or above the line, which is right wherever an error can
    stand, since only a candidate made const makes one.
    """
    opens = max((start for start in scopes if start <= line), default=LineNo(0))
    above = [c for c in pending if name in c.names and c.scope == opens and c.site.line <= line]
    return max(above, key=lambda c: (c.site.line, c.site.column)) if above else None


def _reports(diagnostics: Diagnostics) -> list[Report]:
    """Group the diagnostics one error, with the notes that follow it, per report."""
    reports: list[Report] = []
    for line in diagnostics.splitlines():
        diagnostic = _DIAGNOSTIC.match(line)
        if diagnostic is None:
            continue
        if diagnostic.group(4) == "error" or not reports:
            reports.append([])
        reports[-1].append(DiagnosticLine(line))
    return reports


def _object_at(text: SourceLine, column: Column) -> Name | None:
    """Return the object an error at ``column`` points at.

    clang points a member call on a const object at the object itself, or at the
    member after the object's ``.`` or ``->``, and a failed operator just past
    its object; so the object is the name a member access ends in before the
    column, or else the name at the column, or else the name right before it.
    """
    head = text[: column - 1].rstrip()
    member = re.search(r"([A-Za-z_]\w*)\s*(?:\.|->)$", head)
    if member is not None:
        return Name(member.group(1))
    at = re.match(r"[A-Za-z_]\w*", text[column - 1 :])
    if at is not None:
        return Name(at.group(0))
    before = re.search(r"([A-Za-z_]\w*)$", head)
    return Name(before.group(1)) if before else None


def resolve(
    pending: frozenset[Candidate],
    compile_with: Callable[[frozenset[Candidate]], Compiled],
    settle: Callable[[Compiled, frozenset[Candidate]], frozenset[Candidate]],
) -> frozenset[Candidate]:
    """Return the candidates that compile as const, compiling with ``compile_with``."""
    while pending:
        compiled = compile_with(pending)
        if compiled.ok:
            return pending
        written = settle(compiled, pending)
        if not written:
            break
        pending -= written
    if len(pending) <= SINGLES:
        return frozenset(c for c in sorted(pending) if compile_with(frozenset({c})).ok)
    ordered = sorted(pending)
    half = len(ordered) // 2
    return resolve(frozenset(ordered[:half]), compile_with, settle) | resolve(
        frozenset(ordered[half:]), compile_with, settle
    )


def compile_commands(repo: Path) -> dict[UnitPath, CompileCommand]:
    """Read every unit's compile command, its output file dropped and a syntax check asked for."""
    entries = cast(
        "list[DatabaseEntry]", json.loads((repo / COMPILE_DB).read_text(encoding="utf-8"))
    )
    commands: dict[UnitPath, CompileCommand] = {}
    for entry in entries:
        argv = entry.get("arguments") or [
            CompileArg(arg) for arg in shlex.split(entry.get("command", CommandLine("")))
        ]
        kept = [
            arg
            for index, arg in enumerate(argv)
            if arg != "-o" and (index == 0 or argv[index - 1] != "-o")
        ]
        extra = [CompileArg("-fsyntax-only"), CompileArg("-ferror-limit=0"), CompileArg("-w")]
        commands[entry["file"]] = CompileCommand([*kept, *extra], Path(entry["directory"]))
    return commands


def syntax_check(
    repo: Path, command: CompileCommand, scratch: Path, made_const: frozenset[Candidate]
) -> Compiled:
    """Syntax-check a unit with ``made_const`` declared const, their file overlaid by a copy."""
    file = repo / next(iter(made_const)).site.file
    lines = file.read_text(encoding="utf-8").split("\n")
    for candidate in made_const:
        index, start = candidate.site.line - 1, candidate.site.column - 1
        lines[index] = lines[index][:start] + constify(SourceLine(lines[index][start:]))
    with TemporaryDirectory(dir=scratch) as private:
        overlay = _overlay(file, SourceText("\n".join(lines)), Path(private))
        finished = subprocess.run(
            [*command.arguments, "-ivfsoverlay", str(overlay)],
            cwd=command.directory,
            capture_output=True,
            text=True,
            check=False,
        )
    return Compiled(finished.returncode == 0, Diagnostics(finished.stderr))


def _overlay(file: Path, text: SourceText, private: Path) -> Path:
    """Write ``text`` as a copy of ``file``, and the overlay putting it in the original's place."""
    copy = private / file.name
    _ = copy.write_text(text, encoding="utf-8")
    contents = [{"name": file.name, "type": "file", "external-contents": str(copy)}]
    roots = [{"name": str(file.parent), "type": "directory", "contents": contents}]
    overlay = private / "overlay.yaml"
    _ = overlay.write_text(
        json.dumps({"version": 0, "use-external-names": False, "roots": roots}), encoding="utf-8"
    )
    return overlay


def const_able(
    repo: Path,
    candidates: list[Candidate],
    workers: WorkerCount,
    *,
    executor: ExecutorFactory = ThreadPoolExecutor,
) -> list[Candidate]:
    """Every candidate that compiles as const, each file resolved on a worker of its own.

    ``executor`` builds what the files are resolved on: a thread pool by default,
    and in a test an executor that runs each file on the test's own thread.
    """
    commands = compile_commands(repo)
    by_file: dict[RelPath, list[Candidate]] = {}
    for candidate in candidates:
        by_file.setdefault(candidate.site.file, []).append(candidate)
    with TemporaryDirectory(prefix="const-locals-") as scratch, executor(workers) as pool:

        def one_file(group: list[Candidate]) -> frozenset[Candidate]:
            file = repo / group[0].site.file
            lines = [SourceLine(text) for text in file.read_text(encoding="utf-8").split("\n")]
            command = commands[group[0].unit]
            scopes = tuple(sorted({c.scope for c in group}))
            return resolve(
                frozenset(group),
                lambda made: syntax_check(repo, command, Path(scratch), made),
                lambda compiled, pending: settled(compiled, file, lines, pending, scopes),
            )

        return sorted(c for found in pool.map(one_file, by_file.values()) for c in found)


def observed_rows(found: Iterable[Candidate]) -> RatchetRows:
    """Count the findings by file and declaration text, the record's key."""
    rows: RatchetRows = {}
    for candidate in found:
        key = RowKey(candidate.site.file, candidate.text)
        rows[key] = rows.get(key, 0) + 1
    return rows


def report(found: list[Candidate], reads: list[Site], recorded: RatchetRows) -> ExitStatus:
    """Print each unrecorded finding, stale row and const JSON read; return the exit status."""
    observed = observed_rows(found)
    unrecorded = sorted(key for key, n in observed.items() if n > recorded.get(key, 0))
    stale = sorted(key for key, n in recorded.items() if n > observed.get(key, 0))
    for file, text in unrecorded:
        lines = ",".join(str(c.site.line) for c in found if c.site.file == file and c.text == text)
        emit(f"{file}:{lines}: a local is never written and is not const")
        emit(f"    {text}")
        emit("  Declare it const (AGENTS/cpp.md cat 5: `auto const`, `const T`), or, with")
        emit(f"  user approval, add this row to {ALLOWLIST}:")
        emit(as_row(file, text, observed[RowKey(file, text)]))
    for file, text in stale:
        emit(f"{file}: a recorded row names more locals than the gate finds")
        emit(f"    {text}")
        count = observed.get(RowKey(file, text), 0)
        emit(f"  Drop the row from {ALLOWLIST}, or lower its count to {count}.")
    for site in reads:
        emit(f"{site.file}:{site.line}: a const JSON document is read through operator[], which is")
        emit("  undefined on a missing key; read it with at()")
    if unrecorded or stale or reads:
        emit(f"{len(unrecorded)} unrecorded, {len(stale)} stale, {len(reads)} const JSON reads")
        return ExitStatus(1)
    total = sum(observed.values())
    emit(f"C++ locals that compile as const and are not: {total}, every one recorded")
    return ExitStatus(0)


def main() -> ExitStatus:
    """List the candidates, compile them as const, and judge; 0 when clean, 1 otherwise."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--jobs",
        type=int,
        default=os.process_cpu_count() or 1,
        help="files compiled at once (default: the CPUs this process may use)",
    )
    jobs = cast("WorkerCount", parser.parse_args().jobs)
    if jobs < 1:
        parser.error("--jobs takes a positive count")
    queried = query_tree(QUERY)
    if queried is None:
        return ExitStatus(1)
    recorded = read_ratchet_rows(queried.repo, ALLOWLIST, "locals")
    if isinstance(recorded, str):
        emit(recorded)
        return ExitStatus(1)
    found = scan(queried.repo, queried.units, queried.outputs)
    return report(
        const_able(queried.repo, found.candidates, jobs), found.const_json_reads, recorded
    )


if __name__ == "__main__":
    sys.exit(main())
