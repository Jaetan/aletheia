# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Go lane plants the mutants gremlins leaves untried in a function body.

gremlins reports every mutant of a case clause's expression NOT COVERED,
since Go's cover tool opens the clause's block after its colon, and others
in function bodies besides.  The lane makes gremlins' token change at the
reported column itself, runs the package's tests, restores the file, and
rewrites the sweep's log so the mutant reads as the run judged it; a mutant
outside every function body stays as gremlins reported it.  Each test
stands go and gremlins in process: go answers from the source it finds
planted, gremlins prints what the test scripts, and no tool runs.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import dataclass, field
from itertools import pairwise
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

import pytest
import yaml
from _scratch_copies import install as install_copies
from _stand_in import ScriptSource, ToolName, install_stand_in

from tools import mutation_run
from tools._common import CommandWord, EnvName, EnvValue, RelPath
from tools.mutation_go import (
    GO_CONFIG,
    GO_MERGE_STAGE,
    GO_PACKAGE,
    GO_SHARDS,
    GO_SHARDS_ENV,
    GO_STAGE_ENV,
    FilePattern,
    GremlinsLog,
    PackageFile,
    ShortSha,
    parse_gremlins_summary,
    swept_counts,
)
from tools.mutation_go_cases import (
    BodyMutant,
    ExitStatus,
    GoSource,
    GoTestOutput,
    LogOffset,
    MutatorName,
    PlantedVerdict,
    SourceColumn,
    SourceLine,
    StatusField,
    mutated_source,
    plant_function_bodies,
    planted_verdict,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence

# A package file's text, or one line of it, as the tests plant it and as go finds it.
_GoText = NewType("_GoText", str)

_QUOTE_GO = PackageFile("quote.go")

# The file every test but the shards' plants, its lines numbered as gremlins
# numbers them: a package-level constant on line 3, case clauses on 7 and 9.
_QUOTE = _GoText(
    "package aletheia\n"
    + "\n"
    + "const Max = 1<<11 - 1\n"
    + "\n"
    + "func quote(r rune) string {\n"
    + "\tswitch {\n"
    + "\tcase r == '\"':\n"
    + '\t\treturn "q"\n'
    + "\tcase r < 0x20 || r >= 0x7f:\n"
    + '\t\treturn "u"\n'
    + "\t}\n"
    + '\treturn ""\n'
    + "}\n"
)

# A sweep of that file in gremlins' words: one mutant killed elsewhere, one
# on the constant and three on the case clauses, all four not covered.  The
# head is every line above the summary, the tail the summary and below.
_SWEEP_HEAD = (
    "Starting...\n"
    + "Gathering coverage... done in 1s\n"
    + "      KILLED CONDITIONALS_NEGATION at other.go:4:7\n"
    + " NOT COVERED INVERT_BITWISE at quote.go:3:14\n"
    + " NOT COVERED CONDITIONALS_NEGATION at quote.go:7:9\n"
    + " NOT COVERED CONDITIONALS_BOUNDARY at quote.go:9:9\n"
    + " NOT COVERED INVERT_LOGICAL at quote.go:9:16\n"
    + "Mutation testing completed in 1 second\n"
)
_SWEEP_TAIL = (
    "Killed: 1, Lived: 0, Not covered: 4\n"
    + "Timed out: 0, Not viable: 0, Skipped: 0\n"
    + "Test efficacy: 100.00%\n"
    + "Mutator coverage: 20.00%\n"
)
_SWEEP = GremlinsLog(_SWEEP_HEAD + _SWEEP_TAIL)

# The three case clauses' lines as gremlins' mutators leave them, in the log's order.
_EQUALS_NEGATED = _GoText("\tcase r != '\"':")
_BOUNDARY_MOVED = _GoText("\tcase r <= 0x20 || r >= 0x7f:")
_LOGIC_INVERTED = _GoText("\tcase r < 0x20 && r >= 0x7f:")


class _Answer(NamedTuple):
    """What go test ends with: its exit status and what it printed."""

    status: ExitStatus
    output: GoTestOutput


_PASS = _Answer(ExitStatus(0), GoTestOutput("ok  \tgithub.com/x/aletheia\t0.1s\n"))
_FAIL = _Answer(ExitStatus(1), GoTestOutput("--- FAIL: TestQuote (0.00s)\nFAIL\n"))
_NO_BUILD = _Answer(ExitStatus(1), GoTestOutput("FAIL\tgithub.com/x/aletheia [build failed]\n"))


@dataclass
class _GoRun:
    """One test run the plant started: its words, where, under what, and the lines it changed."""

    words: list[CommandWord]
    cwd: Path
    env: dict[EnvName, EnvValue]
    changed: list[_GoText]


@dataclass
class _Go:
    """go test as the lane runs it, answering by the line it finds planted in the package.

    ``originals`` are the package's files as the test planted them; a run
    finding none changed is the unmutated control run.
    """

    originals: dict[PackageFile, _GoText]
    answers: dict[_GoText, _Answer]
    unmutated: _Answer = _PASS
    runs: list[_GoRun] = field(default_factory=list[_GoRun])

    def __call__(
        self, cmd: Sequence[CommandWord], *, cwd: Path, env: Mapping[EnvName, EnvValue]
    ) -> subprocess.CompletedProcess[GoTestOutput]:
        """Record the run with the lines it found changed, and answer for them."""
        changed = [
            _GoText(now)
            for name, text in self.originals.items()
            for now, was in zip(
                (cwd / "aletheia" / name).read_text(encoding="utf-8").split("\n"),
                text.split("\n"),
                strict=True,
            )
            if now != was
        ]
        self.runs.append(_GoRun(list(cmd), cwd, dict(env), changed))
        answer = self.answers[changed[0]] if changed else self.unmutated
        return subprocess.CompletedProcess(cmd, answer.status, answer.output, GoTestOutput(""))


def _tree(root: Path, files: Mapping[PackageFile, _GoText]) -> Path:
    """Plant a tree whose package holds the files given."""
    package = root / "go" / "aletheia"
    package.mkdir(parents=True)
    for name, text in files.items():
        _ = (package / name).write_text(text, encoding="utf-8")
    return root


def _go_on_path(directory: Path) -> dict[EnvName, EnvValue]:
    """Plant an executable go the plant can find, and the environment that finds it."""
    directory.mkdir(parents=True, exist_ok=True)
    go = directory / "go"
    _ = go.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
    go.chmod(0o755)
    return {EnvName("PATH"): EnvValue(str(directory)), EnvName("GOFLAGS"): EnvValue("-count=1")}


def _install_go(monkeypatch: pytest.MonkeyPatch, go: _Go) -> _Go:
    monkeypatch.setattr("tools.mutation_go_cases.run_capture", go)
    return go


def _quote_go(monkeypatch: pytest.MonkeyPatch, answers: dict[_GoText, _Answer]) -> _Go:
    return _install_go(monkeypatch, _Go({_QUOTE_GO: _QUOTE}, answers))


def test_each_case_clause_mutant_is_planted_as_gremlins_mutates_it(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The token at the reported byte column changes as gremlins' table says, one per run.

    The unmutated tests run first; each mutant then runs with its own line
    alone changed, from the package directory's parent under the sweep's
    environment, and the file reads as it did once the plants are done.
    """
    tree = _tree(tmp_path / "tree", {_QUOTE_GO: _QUOTE})
    env = _go_on_path(tmp_path / "bin")
    go = _quote_go(
        monkeypatch, {_EQUALS_NEGATED: _FAIL, _BOUNDARY_MOVED: _FAIL, _LOGIC_INVERTED: _FAIL}
    )
    _ = plant_function_bodies(_SWEEP, tree, env)
    assert [run.changed for run in go.runs] == [
        [],
        [_EQUALS_NEGATED],
        [_BOUNDARY_MOVED],
        [_LOGIC_INVERTED],
    ]
    assert {tuple(run.words) for run in go.runs} == {
        (str(tmp_path / "bin" / "go"), "test", "-failfast", "./aletheia")
    }
    assert {run.cwd for run in go.runs} == {tree / "go"}
    assert all(run.env == env for run in go.runs)
    assert (tree / "go" / "aletheia" / _QUOTE_GO).read_text(encoding="utf-8") == _QUOTE


def test_a_planted_mutant_leaves_not_covered_for_the_bucket_its_run_gives(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Killed, lived and not viable land in gremlins' own buckets, and a lived one is a survivor.

    Every mutant is still on one line of the log, so the census a shard is
    held to is unchanged; the summary's first figures are the lane's, and
    the survivor is keyed on its line as one of gremlins' is.
    """
    tree = _tree(tmp_path / "tree", {_QUOTE_GO: _QUOTE})
    _ = _quote_go(
        monkeypatch,
        {_EQUALS_NEGATED: _FAIL, _BOUNDARY_MOVED: _PASS, _LOGIC_INVERTED: _NO_BUILD},
    )
    planted = plant_function_bodies(_SWEEP, tree, _go_on_path(tmp_path / "bin"))
    assert planted == (
        "Starting...\n"
        + "Gathering coverage... done in 1s\n"
        + "      KILLED CONDITIONALS_NEGATION at other.go:4:7\n"
        + " NOT COVERED INVERT_BITWISE at quote.go:3:14\n"
        + "      KILLED CONDITIONALS_NEGATION at quote.go:7:9 (planted in a function body)\n"
        + "       LIVED CONDITIONALS_BOUNDARY at quote.go:9:9 (planted in a function body)\n"
        + "  NOT VIABLE INVERT_LOGICAL at quote.go:9:16 (planted in a function body)\n"
        + "Mutation testing completed in 1 second\n"
        + "The lane planted 3 of the 3 mutants gremlins left untried in a function "
        + "body: 1 killed, 1 lived, 1 not viable, 0 timed out.\n"
        + "Killed: 2, Lived: 1, Not covered: 1\n"
        + "Timed out: 0, Not viable: 1, Skipped: 0\n"
        + "Test efficacy: 100.00%\n"
        + "Mutator coverage: 20.00%\n"
    )
    report = parse_gremlins_summary(planted, Prose("planted"))
    assert (report.killed, report.survived, report.observed.generated) == (2, 1, 5)
    assert swept_counts(planted) == swept_counts(_SWEEP)
    assert mutation_run.go_mutant_rows(planted, "LIVED", tree) == {
        ("CONDITIONALS_BOUNDARY", "go/aletheia/quote.go", "case r < 0x20 || r >= 0x7f:"): 1
    }
    assert mutation_run.go_mutant_rows(planted, "NOT COVERED", tree) == {
        ("INVERT_BITWISE", "go/aletheia/quote.go", "const Max = 1<<11 - 1"): 1
    }


@pytest.mark.parametrize(
    ("answer", "verdict"),
    [
        (_PASS, "LIVED"),
        (_FAIL, "KILLED"),
        (_NO_BUILD, "NOT VIABLE"),
        (
            _Answer(ExitStatus(1), GoTestOutput("# x [x.test]\nFAIL\tx [setup failed]\n")),
            "NOT VIABLE",
        ),
        (
            _Answer(ExitStatus(1), GoTestOutput("panic: test timed out after 10m0s\nFAIL\n")),
            "TIMED OUT",
        ),
    ],
)
def test_the_verdict_is_read_from_the_run_as_gremlins_names_it(
    answer: _Answer, verdict: PlantedVerdict
) -> None:
    """A failed test and an unbuilt package both exit 1, so the output tells them apart."""
    assert planted_verdict(answer.status, answer.output) == verdict


def test_a_mutant_outside_every_function_body_is_left_as_gremlins_reported_it(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A not-covered constant is the record's to name: no process starts, the log is unchanged.

    So is a mutant in a file the tree does not have, or on a line past its end.
    """
    tree = _tree(tmp_path / "tree", {_QUOTE_GO: _QUOTE})
    go = _quote_go(monkeypatch, {})
    log = GremlinsLog(
        " NOT COVERED INVERT_BITWISE at quote.go:3:14\n"
        + " NOT COVERED CONDITIONALS_NEGATION at gone.go:7:9\n"
        + " NOT COVERED CONDITIONALS_NEGATION at quote.go:70:9\n"
        + "Killed: 0, Lived: 0, Not covered: 3\n"
        + "Timed out: 0, Not viable: 0, Skipped: 0\n"
    )
    assert plant_function_bodies(log, tree, {}) == log
    assert not go.runs


_BODIES_GO = PackageFile("bodies.go")

# A file with not-covered mutants on both sides of function bodies' braces,
# its lines numbered as gremlins numbers them.  Outside every body: a
# constant (line 3), composite literals after a function type (7 to 9), a
# signature's type set (14) and an array length in a signature's struct and
# interface (18, 22).  Inside one: a function literal's at package level
# (11), and the bodies of functions whose signatures carry type parameters
# (on the line after a ``]``), a struct, an interface, a receive-only channel
# and a pointer to a qualified name (15 to 32), the last after a brace in
# each kind of literal and comment (31), which opens nothing.
_BODIES = _GoText(
    "package aletheia\n"
    + "\n"
    + "const Mask = 1<<4 - 1\n"
    + "\n"
    + "type op func(int) int\n"
    + "\n"
    + "var ops = [2]int{1 << 4, 2}\n"
    + "var steps = []func() int{step(1 << 2)}\n"
    + "var grid = Grid[func()]{{1 << 5}}\n"
    + "var table = map[string]func() int{\n"
    + '\t"a": func() int { return 1 << 3 },\n'
    + "}\n"
    + "var first = steps[0]\n"
    + "func narrow[T ~uint8 | ~uint16](v int64) (T, bool) {\n"
    + "\treturn T(v), v >= 0\n"
    + "}\n"
    + "\n"
    + "func pair(n int) struct{ a, b [1 << 1]int } {\n"
    + "\treturn struct{ a, b [1 << 1]int }{}\n"
    + "}\n"
    + "\n"
    + "func boxed(n int) interface{ M([1 >> 1]int) } {\n"
    + "\treturn box(n >> 1)\n"
    + "}\n"
    + "\n"
    + "func recv(c chan int, n int) <-chan int {\n"
    + "\treturn ring(c, n-1)\n"
    + "}\n"
    + "\n"
    + "func escape(r rune) *fmt.State {\n"
    + "\tq, c, d, raw := \"{\\\"\", '\\\\', '{', `{\\` /* { */ // {\n"
    + "\tfmt.Fprintf(&b, `\\u%04x`, r)\n"
    + "\treturn nil\n"
    + "}\n"
)


def test_every_mutant_in_a_function_body_is_planted_and_none_outside_one(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A mutant is planted where a function's body holds it, whatever its line holds.

    A body runs from the brace that ends its function's signature to the one
    that closes it.  The ``&`` of ``fmt.Fprintf(&b, ...)``, which gremlins
    inverts to ``|``, is planted, and its package does not build; the
    mutants outside every body stay rows of the record.
    """
    tree = _tree(tmp_path / "tree", {_BODIES_GO: _BODIES})
    inside = {
        _GoText('\t"a": func() int { return 1 >> 3 },'): _FAIL,
        _GoText("\treturn T(v), v > 0"): _FAIL,
        _GoText("\treturn struct{ a, b [1 >> 1]int }{}"): _FAIL,
        _GoText("\treturn box(n << 1)"): _FAIL,
        _GoText("\treturn ring(c, n+1)"): _FAIL,
        _GoText("\tfmt.Fprintf(|b, `\\u%04x`, r)"): _NO_BUILD,
    }
    outside = {
        _GoText("const Mask = 1>>4 - 1"): _PASS,
        _GoText("var ops = [2]int{1 >> 4, 2}"): _PASS,
        _GoText("var steps = []func() int{step(1 >> 2)}"): _PASS,
        _GoText("var grid = Grid[func()]{{1 >> 5}}"): _PASS,
        _GoText("func narrow[T ~uint8 & ~uint16](v int64) (T, bool) {"): _PASS,
        _GoText("func pair(n int) struct{ a, b [1 >> 1]int } {"): _PASS,
        _GoText("func boxed(n int) interface{ M([1 << 1]int) } {"): _PASS,
    }
    go = _install_go(monkeypatch, _Go({_BODIES_GO: _BODIES}, inside | outside))
    log = GremlinsLog(
        " NOT COVERED INVERT_BITWISE at bodies.go:3:15\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:7:20\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:8:33\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:9:28\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:11:29\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:14:22\n"
        + " NOT COVERED CONDITIONALS_BOUNDARY at bodies.go:15:17\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:18:34\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:19:25\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:22:35\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:23:15\n"
        + " NOT COVERED ARITHMETIC_BASE at bodies.go:27:18\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:32:14\n"
        + "Killed: 0, Lived: 0, Not covered: 13\n"
        + "Timed out: 0, Not viable: 0, Skipped: 0\n"
    )
    planted = plant_function_bodies(log, tree, _go_on_path(tmp_path / "bin"))
    assert [run.changed for run in go.runs] == [[], *([line] for line in inside)]
    assert planted == (
        " NOT COVERED INVERT_BITWISE at bodies.go:3:15\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:7:20\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:8:33\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:9:28\n"
        + "      KILLED INVERT_BITWISE at bodies.go:11:29 (planted in a function body)\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:14:22\n"
        + "      KILLED CONDITIONALS_BOUNDARY at bodies.go:15:17 (planted in a function body)\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:18:34\n"
        + "      KILLED INVERT_BITWISE at bodies.go:19:25 (planted in a function body)\n"
        + " NOT COVERED INVERT_BITWISE at bodies.go:22:35\n"
        + "      KILLED INVERT_BITWISE at bodies.go:23:15 (planted in a function body)\n"
        + "      KILLED ARITHMETIC_BASE at bodies.go:27:18 (planted in a function body)\n"
        + "  NOT VIABLE INVERT_BITWISE at bodies.go:32:14 (planted in a function body)\n"
        + "The lane planted 6 of the 6 mutants gremlins left untried in a function "
        + "body: 5 killed, 0 lived, 1 not viable, 0 timed out.\n"
        + "Killed: 5, Lived: 0, Not covered: 7\n"
        + "Timed out: 0, Not viable: 1, Skipped: 0\n"
    )
    assert (tree / "go" / "aletheia" / _BODIES_GO).read_text(encoding="utf-8") == _BODIES


def test_a_sweep_without_its_summary_is_left_for_the_reader_to_refuse(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A sweep that stopped before its summary is no sweep: nothing is planted or written."""
    tree = _tree(tmp_path / "tree", {_QUOTE_GO: _QUOTE})
    go = _quote_go(monkeypatch, {})
    cut = GremlinsLog(_SWEEP_HEAD)
    assert plant_function_bodies(cut, tree, _go_on_path(tmp_path / "bin")) == cut
    assert not go.runs
    assert parse_gremlins_summary(cut, Prose("cut")).error is not None


def test_unmutated_tests_that_fail_plant_nothing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Were the package red as it stands, every plant would read as killed: none is made."""
    tree = _tree(tmp_path / "tree", {_QUOTE_GO: _QUOTE})
    go = _install_go(monkeypatch, _Go({_QUOTE_GO: _QUOTE}, {}, unmutated=_FAIL))
    planted = plant_function_bodies(_SWEEP, tree, _go_on_path(tmp_path / "bin"))
    assert [run.changed for run in go.runs] == [[]]
    assert planted == (
        _SWEEP_HEAD + "The unmutated tests read as KILLED: no mutant was planted.\n" + _SWEEP_TAIL
    )


def _mutant_at(mutator: MutatorName, column: SourceColumn) -> BodyMutant:
    """Name a mutant on the first line of a source, as gremlins would report it."""
    return BodyMutant(
        mutator,
        _QUOTE_GO,
        SourceLine(1),
        column,
        Path("unused"),
        StatusField(" NOT COVERED"),
        LogOffset(0),
        LogOffset(0),
    )


@pytest.mark.parametrize(
    ("line", "mutator", "column", "mutated"),
    [
        ("\tcase r == 1:", "CONDITIONALS_NEGATION", 9, "\tcase r != 1:"),
        ("\tcase x&^m != 0:", "INVERT_BITWISE", 8, "\tcase x&m != 0:"),
        ("\tcase -x > 0:", "INVERT_NEGATIVES", 7, "\tcase +x > 0:"),
        ("\tcase m%n > 0:", "ARITHMETIC_BASE", 8, "\tcase m*n > 0:"),
        ("\tbreak", "INVERT_LOOPCTRL", 2, "\tcontinue"),
        ("\tx %= 2", "INVERT_ASSIGNMENTS", 4, "\tx %= 2"),
    ],
)
def test_the_token_at_the_column_changes_as_gremlins_table_says(
    line: _GoText, mutator: MutatorName, column: SourceColumn, mutated: _GoText
) -> None:
    """The token is read whole at its byte column and replaced, the rest of the line untouched.

    gremlins maps ``%=`` to itself under INVERT_ASSIGNMENTS, and so does the lane.
    """
    source = GoSource(f"{line}\nnext\n".encode())
    assert mutated_source(source, _mutant_at(mutator, column)) == f"{mutated}\nnext\n".encode()


@pytest.mark.parametrize(
    ("line", "mutator", "column", "reason"),
    [
        (
            "\tx <<= 1",
            "CONDITIONALS_BOUNDARY",
            4,
            "CONDITIONALS_BOUNDARY changes no token '<<=' at column 4",
        ),
        (
            "\tcase r <- c:",
            "CONDITIONALS_BOUNDARY",
            9,
            "CONDITIONALS_BOUNDARY changes no token '<-' at column 9",
        ),
        (
            "\tcase r == 1:",
            "CONDITIONALS_NEGATION",
            7,
            "CONDITIONALS_NEGATION changes no token 'r' at column 7",
        ),
        ("\tcase r == 1:", "NO_SUCH_MUTATOR", 9, "gremlins 0.6.0 has no mutator NO_SUCH_MUTATOR"),
    ],
)
def test_a_token_the_mutator_does_not_change_is_not_planted(
    line: _GoText, mutator: MutatorName, column: SourceColumn, reason: Prose
) -> None:
    """The scanner reads the longest token at the column, and a mutator not changing it refuses."""
    source = GoSource(f"{line}\n".encode())
    assert mutated_source(source, _mutant_at(mutator, column)) == reason


def test_no_go_on_the_sweep_s_path_plants_nothing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The go the tests run is the one the sweep's own search path finds, or none is run."""
    tree = _tree(tmp_path / "tree", {_QUOTE_GO: _QUOTE})
    go = _quote_go(monkeypatch, {})
    (tmp_path / "empty").mkdir()
    planted = plant_function_bodies(
        _SWEEP, tree, {EnvName("PATH"): EnvValue(str(tmp_path / "empty"))}
    )
    assert not go.runs
    assert planted == (
        _SWEEP_HEAD + "No go on the sweep's PATH: no mutant was planted.\n" + _SWEEP_TAIL
    )


def test_a_position_the_source_disagrees_with_stays_not_covered(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A mutator naming a token it does not change at that column plants nothing, and says so."""
    tree = _tree(tmp_path / "tree", {_QUOTE_GO: _QUOTE})
    go = _quote_go(monkeypatch, {})
    mutant = " NOT COVERED CONDITIONALS_NEGATION at quote.go:9:16\n"
    summary = "Killed: 0, Lived: 0, Not covered: 1\nTimed out: 0, Not viable: 0, Skipped: 0\n"
    planted = plant_function_bodies(
        GremlinsLog(mutant + summary), tree, _go_on_path(tmp_path / "bin")
    )
    assert [run.changed for run in go.runs] == [[]]
    assert planted == (
        mutant
        + "The lane planted 0 of the 1 mutants gremlins left untried in a function "
        + "body: 0 killed, 0 lived, 0 not viable, 0 timed out.\n"
        + "quote.go:9 was not planted: CONDITIONALS_NEGATION changes no token '||' at column 16\n"
        + summary
    )


# The gremlins the lane finds on the search path; the lane runs it through
# the stand-ins below, never as a process.
_NEVER_RUN = ScriptSource("raise SystemExit('the stand-in never runs')")


@dataclass
class _Gremlins:
    """gremlins as the lane runs it: every call answers ``log`` and is recorded with its cwd."""

    log: GremlinsLog
    cwds: list[Path] = field(default_factory=list[Path])

    def __call__(
        self, cmd: Sequence[CommandWord], *, cwd: Path, env: Mapping[EnvName, EnvValue]
    ) -> subprocess.CompletedProcess[GremlinsLog]:
        """Record where the sweep ran and print the scripted log."""
        assert env
        self.cwds.append(cwd)
        return subprocess.CompletedProcess(cmd, 0, self.log, GremlinsLog(""))


def _lane_repo(root: Path, files: Mapping[PackageFile, _GoText]) -> Path:
    """Plant a repository with the package's files, gremlins' configuration and a built kernel."""
    repo = _tree(root, files)
    _ = (repo / GO_CONFIG).write_text("unleash:\n  exclude-files: []\n", encoding="utf-8")
    (repo / "build").mkdir()
    _ = (repo / "build" / "libaletheia-ffi.so").write_bytes(b"")
    return repo.resolve()


def _lane_env(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Put the stand-in gremlins and a go the plant can find first on the search path."""
    install_stand_in(tmp_path, monkeypatch, ToolName("gremlins"), _NEVER_RUN)
    _ = _go_on_path(tmp_path / "bin")


def test_the_whole_package_s_sweep_plants_its_case_clauses_in_the_scratch_copy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """run_go plants in the copy it swept, under the sweep's variables, and reports the plants."""
    repo = _lane_repo(tmp_path / "repo", {_QUOTE_GO: _QUOTE})
    _lane_env(tmp_path, monkeypatch)
    copies = install_copies(monkeypatch, tmp_path / "copies")
    gremlins = _Gremlins(_SWEEP)
    monkeypatch.setattr("tools.mutation_go_cases.run_streaming", gremlins)
    go = _quote_go(
        monkeypatch,
        {_EQUALS_NEGATED: _FAIL, _BOUNDARY_MOVED: _PASS, _LOGIC_INVERTED: _FAIL},
    )
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    report = mutation_run.run_go(artifacts)
    assert report.error is None
    assert (report.killed, report.survived, report.observed.generated) == (3, 1, 5)
    [copy] = copies.made
    assert gremlins.cwds == [copy / "go"]
    assert [run.cwd for run in go.runs] == [copy / "go"] * 4
    assert {
        name: {run.env.get(EnvName(name)) for run in go.runs}
        for name in ("ALETHEIA_REPO_ROOT", "ALETHEIA_LIB")
    } == {
        "ALETHEIA_REPO_ROOT": {str(copy)},
        "ALETHEIA_LIB": {str(repo / "build" / "libaletheia-ffi.so")},
    }
    assert all("-count=1" in str(run.env.get(EnvName("GOFLAGS"))).split() for run in go.runs)
    assert (artifacts / "go.raw.txt").read_text(encoding="utf-8") == report.raw_log
    assert mutation_run.go_mutant_rows(report.raw_log, "LIVED", repo) == {
        ("CONDITIONALS_BOUNDARY", "go/aletheia/quote.go", "case r < 0x20 || r >= 0x7f:"): 1
    }
    assert sum(mutation_run.go_mutant_rows(report.raw_log, "NOT COVERED", repo).values()) == 1
    assert (repo / "go" / "aletheia" / _QUOTE_GO).read_text(encoding="utf-8") == _QUOTE


def _clause(comment: _GoText) -> _GoText:
    """Write a package file whose one case clause is on line 4, ``==`` at byte column 9."""
    return _GoText(
        "package aletheia\n"
        + "func f(r int) bool {\n"
        + "\tswitch {\n"
        + "\tcase r == 1:\n"
        + "\t\treturn true\n"
        + "\t}\n"
        + "\treturn false\n"
        + "}\n"
        + f"// {comment}\n"
    )


_CLAUSE_NEGATED = _GoText("\tcase r != 1:")

_Unleash = TypedDict("_Unleash", {"exclude-files": list[FilePattern]})


class _Config(TypedDict):
    """The part of a gremlins configuration the stand-in reads."""

    unleash: _Unleash


@dataclass
class _ShardGremlins:
    """gremlins under a shard's configuration: each file it does not hold out has one case mutant.

    A sweep and a dry run alike report the mutant not covered, as gremlins
    reports every mutant of a case clause's expression.
    """

    def __call__(
        self, cmd: Sequence[CommandWord], *, cwd: Path, env: Mapping[EnvName, EnvValue]
    ) -> subprocess.CompletedProcess[GremlinsLog]:
        """Answer the run with one not-covered case mutant per file the configuration sweeps."""
        assert env
        [named] = [after for before, after in pairwise(cmd) if before == "--config"]
        assert named == str(cwd.parent / GO_CONFIG)
        config = cast("_Config", yaml.safe_load((cwd.parent / GO_CONFIG).read_text()))
        held = [re.compile(pattern) for pattern in config["unleash"]["exclude-files"]]
        names = sorted(
            path.name
            for path in (cwd / "aletheia").glob("*.go")
            if not any(pattern.search(path.name) for pattern in held)
        )
        lines = [f" NOT COVERED CONDITIONALS_NEGATION at {name}:4:9\n" for name in names]
        if "--dry-run" in cmd:
            lines.append(f"Runnable: 0, Not covered: {len(names)}\n")
        else:
            lines.append(f"Killed: 0, Lived: 0, Not covered: {len(names)}\n")
            lines.append("Timed out: 0, Not viable: 0, Skipped: 0\n")
        return subprocess.CompletedProcess(cmd, 0, GremlinsLog("".join(lines)), GremlinsLog(""))


def _package_files(repo: Path, *patterns: RelPath) -> list[RelPath]:
    """``git ls-files`` of the package in a planted tree, every file of which is tracked."""
    assert patterns == (RelPath(GO_PACKAGE),)
    return [RelPath(f"{GO_PACKAGE}/{path.name}") for path in sorted((repo / GO_PACKAGE).iterdir())]


_SHA = ShortSha("abc1234")


def _fixed_sha(_repo_root: Path | None = None) -> ShortSha:
    """Read every repository's commit as ``_SHA``."""
    return _SHA


def _sweep_shards(shards_dir: Path, monkeypatch: pytest.MonkeyPatch, go: _Go) -> None:
    """Sweep each shard through the runner as its CI job does, the first's mutant killed.

    Each shard's report, log, record and summary land where the merge reads them.
    """
    for number in range(1, GO_SHARDS + 1):
        monkeypatch.setenv(GO_STAGE_ENV, str(number))
        go.answers[_CLAUSE_NEGATED] = _FAIL if number == 1 else _PASS
        artifacts = shards_dir / f"mutation-go-{number}" / _SHA
        artifacts.mkdir(parents=True)
        report = mutation_run.run_go(artifacts)
        assert report.error is None
        assert report.raw_log.count("(planted in a function body)") == 1
        summary = {"commit": _SHA, "elapsed_s": {"go": 1.0}, "runs": [report.to_dict()]}
        _ = (artifacts / "summary.json").write_text(json.dumps(summary))


def test_the_shards_plant_their_own_case_clauses_and_the_merge_reads_the_plants(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Each shard plants the case clauses of its files; the merge sums them as gremlins' verdicts.

    One shard's mutant is killed and the other's lives, so the merged lane
    reports one of each and the survivor by its line, nothing left not
    covered, and each shard's census still matches its sweep.
    """
    files = {
        PackageFile("a.go"): _clause(_GoText("short")),
        PackageFile("b.go"): _clause(_GoText("a comment long enough to weigh more than a.go")),
    }
    repo = _lane_repo(tmp_path / "repo", files)
    _lane_env(tmp_path, monkeypatch)
    copies = install_copies(monkeypatch, tmp_path / "copies")
    gremlins = _ShardGremlins()
    monkeypatch.setattr("tools.mutation_go_cases.run_streaming", gremlins)
    monkeypatch.setattr(mutation_run, "run_capture", gremlins)
    monkeypatch.setattr("tools.mutation_go.git_ls_files", _package_files)
    monkeypatch.setattr(mutation_run, "short_sha", _fixed_sha)
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    go = _install_go(monkeypatch, _Go(files, {}))
    _sweep_shards(tmp_path / "shards", monkeypatch, go)
    assert len(copies.made) == GO_SHARDS
    assert [run.changed for run in go.runs if run.changed] == [[_CLAUSE_NEGATED]] * GO_SHARDS
    monkeypatch.setenv(GO_STAGE_ENV, GO_MERGE_STAGE)
    monkeypatch.setenv(GO_SHARDS_ENV, str(tmp_path / "shards"))
    (tmp_path / "merge").mkdir()
    merged = mutation_run.run_go(tmp_path / "merge")
    assert merged.error is None
    assert (merged.killed, merged.survived, merged.observed.generated) == (1, 1, 2)
    [(mutator, survived_in, text)] = mutation_run.go_mutant_rows(merged.raw_log, "LIVED", repo)
    assert (mutator, text) == ("CONDITIONALS_NEGATION", "case r == 1:")
    assert survived_in in {"go/aletheia/a.go", "go/aletheia/b.go"}
    assert not mutation_run.go_mutant_rows(merged.raw_log, "NOT COVERED", repo)
