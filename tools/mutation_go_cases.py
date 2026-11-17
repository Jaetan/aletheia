# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Go lane's plants of the mutants gremlins leaves untried in a function body.

gremlins counts a mutant covered only when its token's column lies inside a
block the coverage profile counts, and Go's cover tool opens a case clause's
block after its colon, so every mutant of a case clause's expression is
reported NOT COVERED and never tried, whatever the tests do; gremlins reports
other mutants in function bodies so besides.  After each sweep, of the whole
package or of one shard, the lane plants every not-covered mutant inside a
function body itself in the sweep's scratch copy: the token change gremlins'
mutator makes at the line and column its report names, the package's tests
run under the sweep's own environment, the file restored.  The tests failing
kill it, their passing leaves it lived, and a mutant the go command cannot
build is not viable; a run go test's own deadline ended is timed out, which
the lane's timeout ceiling refuses, as it refuses a sweep in which gremlins'
cap fired.

The sweep's log is rewritten in place: each planted mutant's line carries the
verdict its run gave, in gremlins' own column, and gremlins' two summary lines
move each planted mutant from ``Not covered`` to that verdict's count, so
every reader of a sweep's log, the drift gate's survivor rows and the shards'
merge included, reads a planted survivor as it reads one of gremlins'.  A
mutant outside every function body, in a package-level declaration or a
function's signature, is never planted: Go's cover tool counts no statement
there for a test to reach, and the mutant is left to the record's
``not_covered_ledger``.  Before the first plant the unmutated tests run once
under the same environment, and where they fail nothing is planted, since
every plant would then read as killed: the mutants stay not covered, which
the record refuses.
"""

from __future__ import annotations

import re
import shutil
import subprocess
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType

from tools._common import CommandWord, EnvName, EnvValue, run_capture, run_streaming
from tools.mutation_go import GO_PACKAGE, GREMLINS_BUCKETS, GremlinsBucket, GremlinsLog, PackageFile

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping, Sequence
    from pathlib import Path

# A mutator as gremlins names it in its report, ``CONDITIONALS_NEGATION``.
MutatorName = NewType("MutatorName", str)

# A Go operator or keyword as the source spells it.
TokenSpelling = NewType("TokenSpelling", str)

# A line of a package file as gremlins reports it, numbered from one.
SourceLine = NewType("SourceLine", int)

# A column of that line as gremlins reports it: Go's, a byte count from one.
SourceColumn = NewType("SourceColumn", int)

# Go source as the file holds it, the whole file or one line of it.
GoSource = NewType("GoSource", bytes)

# Where a line starts in a sweep's log, counted in characters.
LogOffset = NewType("LogOffset", int)

# A mutant's status as gremlins prints it, right-aligned in its column.
StatusField = NewType("StatusField", str)

# The go command, by its absolute path.
GoBinary = NewType("GoBinary", str)

# How a process ended, and what it printed on both streams.
ExitStatus = NewType("ExitStatus", int)
GoTestOutput = NewType("GoTestOutput", str)

# The verdict a planted mutant's run gives, in gremlins' words.
PlantedVerdict = Literal["KILLED", "LIVED", "NOT VIABLE", "TIMED OUT"]

_BUCKET_OF: dict[PlantedVerdict, GremlinsBucket] = {
    "KILLED": "Killed",
    "LIVED": "Lived",
    "NOT VIABLE": "Not viable",
    "TIMED OUT": "Timed out",
}

# gremlins 0.6.0's ``tokenMutations`` (internal/engine/mappings.go), by the
# names its report prints (internal/mutator/mutator.go), each token spelled as
# Go spells it.  ``%=`` under INVERT_ASSIGNMENTS stays ``%=`` there, and here.
_GREMLINS_TABLE = {
    "ARITHMETIC_BASE": {"+": "-", "*": "/", "/": "*", "%": "*", "-": "+"},
    "CONDITIONALS_BOUNDARY": {">=": ">", ">": ">=", "<=": "<", "<": "<="},
    "CONDITIONALS_NEGATION": {"==": "!=", ">=": "<", ">": "<=", "<=": ">", "<": ">=", "!=": "=="},
    "INCREMENT_DECREMENT": {"--": "++", "++": "--"},
    "INVERT_ASSIGNMENTS": {"+=": "-=", "*=": "/=", "/=": "*=", "%=": "%=", "-=": "+="},
    "INVERT_BITWISE": {"&": "|", "|": "&", "^": "&", "&^": "&", "<<": ">>", ">>": "<<"},
    "INVERT_BWASSIGN": {
        "&=": "|=",
        "|=": "&=",
        "^=": "&=",
        "&^=": "&=",
        "<<=": ">>=",
        ">>=": "<<=",
    },
    "INVERT_LOGICAL": {"&&": "||", "||": "&&"},
    "INVERT_LOOPCTRL": {"break": "continue", "continue": "break"},
    "INVERT_NEGATIVES": {"-": "+"},
    "REMOVE_SELF_ASSIGNMENTS": dict.fromkeys(
        ("+=", "&=", "&^=", "*=", "|=", "/=", "%=", "<<=", ">>=", "-=", "^="), "="
    ),
}
TOKEN_MUTATIONS: dict[MutatorName, dict[TokenSpelling, TokenSpelling]] = {
    MutatorName(name): {TokenSpelling(token): TokenSpelling(into) for token, into in row.items()}
    for name, row in _GREMLINS_TABLE.items()
}

# Every operator and punctuation token of Go, which the scanner reads longest
# first: the token at a column is the longest of these the text there opens with.
_GO_OPERATORS = sorted(
    (
        *"+-*/%&|^<>=!(),;.:[]{}~",
        *("+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "&^", "&&", "||"),
        *("<-", "++", "--", "==", "!=", "<=", ">=", ":=", "...", "<<=", ">>=", "&^="),
    ),
    key=len,
    reverse=True,
)
_IDENTIFIER = re.compile(rb"[A-Za-z_]\w*")

# A mutant gremlins reported not covered: its status, right-aligned in
# gremlins' column, then the mutator and the position, the file named
# relative to the package.
_NOT_COVERED = re.compile(
    r"^(?P<status> *NOT COVERED) (?P<mutator>\w+) at (?P<file>[\w.]+\.go)"
    + r":(?P<line>\d+):(?P<column>\d+)",
    re.MULTILINE,
)

# gremlins' summary of a sweep, its six buckets over two lines.
_SUMMARY = re.compile(
    r"^Killed: (\d+), Lived: (\d+), Not covered: (\d+)\n"
    + r"Timed out: (\d+), Not viable: (\d+), Skipped: (\d+)$",
    re.MULTILINE,
)

# What reads as no token here: white space but a line's end, a comment, and a
# string, rune or raw string literal, a backslash escaping the byte after it
# in the first two, so a brace inside any of them opens and closes nothing.
# Every other byte is in a token: a line's end, a word (an identifier, a
# keyword or a number's digits and letters), a receive arrow, or one byte.
_SCAN = re.compile(
    rb"[^\S\n]+|//[^\n]*|/\*.*?\*/"
    + rb'|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|`[^`]*`'
    + rb"|(\n|\w+|<-|.)",
    re.DOTALL,
)

_OPENING = frozenset((b"(", b"[", b"{"))
_CLOSING = frozenset((b")", b"]", b"}"))

# The keywords whose brace opens a type in a signature, not the function's body.
_TYPE_BRACES = frozenset((b"struct", b"interface"))

# What may follow a function's keyword at its own depth on the way to its
# body, besides words and brackets: a qualified name's dot, a pointer's star
# and a receive-only channel's arrow.
_SIGNATURE_MARKS = frozenset((b".", b"*", b"<-"))

# Where a byte of a package file lies, counted from zero.
SourceOffset = NewType("SourceOffset", int)

# A token as the file spells it.
GoToken = NewType("GoToken", bytes)

# How many brackets are open around a token.
BracketDepth = NewType("BracketDepth", int)


class _Body(NamedTuple):
    """A function body in its file: where its opening brace lies, and its closing one."""

    opens: SourceOffset
    closes: SourceOffset


def _tokens(text: GoSource) -> Iterator[tuple[SourceOffset, GoToken]]:
    """Read a file's tokens, and where each lies, every line's end one of them."""
    for found in _SCAN.finditer(text):
        if found[1] is not None:
            yield SourceOffset(found.start()), GoToken(found[1])


def function_bodies(text: GoSource) -> list[_Body]:
    """Find a file's function bodies, a declaration's and a literal's alike.

    A ``func`` keyword waits for its body at its bracket depth, unless a
    ``]`` comes just before it, which makes it an element type, as in
    ``[]func(){f}``.  Its signature follows, nested in brackets but for
    words and ``.``, ``*`` and ``<-``, and the first ``{`` at its depth that
    opens no ``struct`` or ``interface`` type opens its body.  Any other
    token at that depth, a line's end included, or the bracket around it
    closing, ends the wait: the keyword began a function type.
    """
    bodies: list[_Body] = []
    brackets: list[tuple[SourceOffset, bool]] = []
    waiting: set[BracketDepth] = set()
    previous = GoToken(b"")
    for at, token in _tokens(text):
        depth = BracketDepth(len(brackets))
        if token == b"func" and previous != b"]":
            waiting.add(depth)
        elif token in _OPENING:
            body = token == b"{" and depth in waiting and previous not in _TYPE_BRACES
            brackets.append((at, body))
        elif token in _CLOSING:
            waiting.discard(depth)
            opens, body = brackets.pop()
            if body:
                bodies.append(_Body(opens, at))
        elif _IDENTIFIER.fullmatch(token) is None and token not in _SIGNATURE_MARKS:
            waiting.discard(depth)
        previous = token
    return bodies


class _Layout(NamedTuple):
    """Where each line of a package file starts, and the file's function bodies."""

    starts: list[SourceOffset]
    bodies: list[_Body]


def _layout(source: Path) -> _Layout:
    """Read a package file's layout; a file the tree does not have is empty."""
    text = GoSource(source.read_bytes() if source.is_file() else b"")
    ends = (SourceOffset(at + 1) for at, byte in enumerate(text) if byte == ord("\n"))
    return _Layout([SourceOffset(0), *ends], function_bodies(text))


class BodyMutant(NamedTuple):
    """One mutant gremlins reported not covered inside a function body.

    ``start`` and ``end`` are its line's span in the sweep's log.
    """

    mutator: MutatorName
    file: PackageFile
    line: SourceLine
    column: SourceColumn
    source: Path
    status: StatusField
    start: LogOffset
    end: LogOffset


def sweep_go_package(
    command: Sequence[CommandWord], tree: Path, env: Mapping[EnvName, EnvValue]
) -> subprocess.CompletedProcess[GremlinsLog]:
    """Run gremlins' sweep of the package in ``tree``, then plant its function bodies' mutants.

    The sweep runs from the tree's ``go/`` and streams its lines as it runs;
    its output comes back with every not-covered mutant inside a function
    body planted (``plant_function_bodies``).
    """
    swept = run_streaming(command, cwd=tree / "go", env=env)
    planted = plant_function_bodies(GremlinsLog(swept.stdout), tree, env)
    return subprocess.CompletedProcess(command, swept.returncode, planted, GremlinsLog(""))


def body_mutants(log: GremlinsLog, tree: Path) -> list[BodyMutant]:
    """Find the not-covered mutants of a sweep's log whose token lies inside a function body.

    A mutant in a file the tree does not have, or on a line past its end, is
    in no function body and is left as gremlins reported it.
    """
    found: list[BodyMutant] = []
    layouts: dict[Path, _Layout] = {}
    for match in _NOT_COVERED.finditer(log):
        source = tree / GO_PACKAGE / match["file"]
        if source not in layouts:
            layouts[source] = _layout(source)
        starts, bodies = layouts[source]
        line = SourceLine(int(match["line"]))
        column = SourceColumn(int(match["column"]))
        at = SourceOffset(starts[line - 1] + column - 1) if 1 <= line <= len(starts) else None
        if at is not None and any(body.opens < at < body.closes for body in bodies):
            found.append(
                BodyMutant(
                    MutatorName(match["mutator"]),
                    PackageFile(match["file"]),
                    line,
                    column,
                    source,
                    StatusField(match["status"]),
                    LogOffset(match.start()),
                    LogOffset(match.end()),
                )
            )
    return found


def _token_at(text: GoSource, column: SourceColumn) -> TokenSpelling | None:
    """Read the Go token that starts at a column of a line, as the scanner reads it."""
    word = _IDENTIFIER.match(text, column - 1)
    if word is not None:
        return TokenSpelling(word.group().decode("ascii"))
    for spelling in _GO_OPERATORS:
        if text.startswith(spelling.encode("ascii"), column - 1):
            return TokenSpelling(spelling)
    return None


def mutated_source(source: GoSource, mutant: BodyMutant) -> GoSource | Prose:
    """Make gremlins' token change at the mutant's position, or say why it cannot be made.

    The token at the column must be one the mutator changes: anything else
    is a report and a source that disagree, and nothing is planted.
    """
    row = TOKEN_MUTATIONS.get(mutant.mutator)
    if row is None:
        return Prose(f"gremlins 0.6.0 has no mutator {mutant.mutator}")
    lines = source.split(b"\n")
    text = lines[mutant.line - 1]
    token = _token_at(GoSource(text), mutant.column)
    if token is None or token not in row:
        return Prose(f"{mutant.mutator} changes no token {token!r} at column {mutant.column}")
    at = mutant.column - 1
    lines[mutant.line - 1] = text[:at] + row[token].encode("ascii") + text[at + len(token) :]
    return GoSource(b"\n".join(lines))


def planted_verdict(status: ExitStatus, output: GoTestOutput) -> PlantedVerdict:
    """Read a planted mutant's verdict from its test run's exit status and output.

    go test exits 1 whether a test failed or the package did not build, so a
    build is told apart by the line go test prints for the package, and a run
    its own deadline ended by the panic that deadline raises.
    """
    if status == 0:
        return "LIVED"
    if "[build failed]" in output or "[setup failed]" in output:
        return "NOT VIABLE"
    if "panic: test timed out after" in output:
        return "TIMED OUT"
    return "KILLED"


def _go_test(go: GoBinary, tree: Path, env: Mapping[EnvName, EnvValue]) -> PlantedVerdict:
    """Run the package's tests as gremlins runs a mutant's, without its clock, for the verdict."""
    words = [CommandWord(word) for word in (go, "test", "-failfast", "./aletheia")]
    ran = run_capture(words, cwd=tree / "go", env=env)
    return planted_verdict(ExitStatus(ran.returncode), GoTestOutput(ran.stdout + ran.stderr))


class NotPlanted(NamedTuple):
    """Why a mutant was left as gremlins reported it: its position and the source disagree."""

    reason: Prose


class Planted(NamedTuple):
    """A mutant the lane planted, and the verdict its run gave."""

    mutant: BodyMutant
    verdict: PlantedVerdict


def _plant(
    mutant: BodyMutant, go: GoBinary, tree: Path, env: Mapping[EnvName, EnvValue]
) -> Planted | NotPlanted:
    """Run the package's tests on one planted mutant, the file restored whatever the run did."""
    original = GoSource(mutant.source.read_bytes())
    mutated = mutated_source(original, mutant)
    if not isinstance(mutated, bytes):
        return NotPlanted(Prose(f"{mutant.file}:{mutant.line} was not planted: {mutated}"))
    _ = mutant.source.write_bytes(mutated)
    try:
        return Planted(mutant, _go_test(go, tree, env))
    finally:
        _ = mutant.source.write_bytes(original)


def _plant_all(
    mutants: Sequence[BodyMutant], tree: Path, env: Mapping[EnvName, EnvValue]
) -> tuple[list[Planted], list[Prose]]:
    """Plant each mutant in turn, and say why any one, or all, went unplanted.

    The unmutated package runs first, read as a mutant's run: it must pass,
    or every plant would read as killed whatever it changed.
    """
    found = shutil.which("go", path=env.get(EnvName("PATH")))
    if found is None:
        return [], [Prose("No go on the sweep's PATH: no mutant was planted.")]
    control = _go_test(GoBinary(found), tree, env)
    if control != "LIVED":
        return [], [Prose(f"The unmutated tests read as {control}: no mutant was planted.")]
    outcomes = [_plant(mutant, GoBinary(found), tree, env) for mutant in mutants]
    planted = [outcome for outcome in outcomes if isinstance(outcome, Planted)]
    tally = ", ".join(
        f"{sum(1 for done in planted if done.verdict == kind)} {kind.lower()}"
        for kind in _BUCKET_OF
    )
    return planted, [
        Prose(
            f"The lane planted {len(planted)} of the {len(mutants)} mutants gremlins left "
            + f"untried in a function body: {tally}."
        ),
        *(outcome.reason for outcome in outcomes if isinstance(outcome, NotPlanted)),
    ]


def _with_verdicts(log: GremlinsLog, planted: Sequence[Planted]) -> GremlinsLog:
    """Rewrite each planted mutant's line with its verdict, in gremlins' own column."""
    for mutant, verdict in reversed(planted):
        line = (
            f"{verdict:>{len(mutant.status)}} {mutant.mutator} at {mutant.file}:{mutant.line}"
            + f":{mutant.column} (planted in a function body)"
        )
        log = GremlinsLog(log[: mutant.start] + line + log[mutant.end :])
    return log


def plant_function_bodies(
    log: GremlinsLog, tree: Path, env: Mapping[EnvName, EnvValue]
) -> GremlinsLog:
    """Plant every not-covered mutant of a sweep's log inside a function body, and rewrite the log.

    Each planted mutant's line carries its verdict, and gremlins' summary
    moves it from ``Not covered`` to that verdict's count, the lines saying
    what was planted, or why nothing was, set just above it.  A log without
    gremlins' summary is a sweep that did not finish, and comes back as it
    was, for the summary's reader to refuse; so does one with no such
    mutant, without a process started.
    """
    summary = _SUMMARY.search(log)
    mutants = body_mutants(log, tree) if summary is not None else []
    if summary is None or not mutants:
        return log
    counts = dict(zip(GREMLINS_BUCKETS, (int(count) for count in summary.groups()), strict=True))
    planted, notes = _plant_all(mutants, tree, env)
    for done in planted:
        counts["Not covered"] -= 1
        counts[_BUCKET_OF[done.verdict]] += 1
    tail = (
        "".join(f"{note}\n" for note in notes)
        + f"Killed: {counts['Killed']}, Lived: {counts['Lived']}, "
        + f"Not covered: {counts['Not covered']}\n"
        + f"Timed out: {counts['Timed out']}, Not viable: {counts['Not viable']}, "
        + f"Skipped: {counts['Skipped']}"
    )
    return GremlinsLog(_SUMMARY.sub(lambda _: tail, _with_verdicts(log, planted), count=1))
