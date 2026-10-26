# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The const-locals gate reads its query, settles what a compile shows, and judges both ways.

A declaration's names and its const spelling are read from its text; the query's
candidates come back without the ones an exclusion names, without a macro's
locals and without another tree's files; a failed compile settles the candidate
the compiler names or the one an error line names alone, and the resolution
falls back on halving when nothing is settled; the judge refuses an unrecorded
local, a stale row and a read of a const JSON document. The compiler itself is
stood in for: what it reports is the gate's red evidence, not these tests'.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType

import pytest
from _executors import DrivenExecutor

from tools import _clang_query as clang_query
from tools import check_cpp_const_locals as gate
from tools._clang_query import CompileArg, Query, QueryOutput, UnitPath
from tools._common import RelPath, WorkerCount
from tools._ratchet import CanonicalText, RowKey, as_row
from tools.check_cpp_const_locals import (
    BindName,
    Candidate,
    Column,
    CompileCommand,
    Compiled,
    Diagnostics,
    LineNo,
    Name,
    Site,
    SourceLine,
    compile_commands,
    const_able,
    constify,
    declared_names,
    report,
    resolve,
    scan,
    settled,
    syntax_check,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable

    from tools._common import ExecutorFactory

_FILE = RelPath("cpp/src/a.cpp")
_UNIT = UnitPath("/unit.cpp")
_NO_SCOPE = LineNo(0)

# A whole C++ file's text, as a test writes it and reads it back.
FileText = NewType("FileText", str)


def _candidate(
    line: LineNo, *names: Name, file: RelPath = _FILE, scope: LineNo = _NO_SCOPE
) -> Candidate:
    """Build a candidate on ``line`` of ``file``, declaring ``names``, in function ``scope``."""
    text = CanonicalText(f"auto {names[0]} = f()")
    return Candidate(Site(file, line, Column(5)), names, text, _UNIT, scope)


def _many(count: LineNo) -> frozenset[Candidate]:
    """Candidates v1 to v``count``, one per line."""
    return frozenset(_candidate(LineNo(n), Name(f"v{n}")) for n in range(1, count + 1))


def _printed(monkeypatch: pytest.MonkeyPatch) -> list[Prose]:
    """Collect what the gate prints, line by line."""
    lines: list[Prose] = []
    monkeypatch.setattr(gate, "emit", lines.append)
    monkeypatch.setattr(clang_query, "emit", lines.append)
    return lines


@pytest.mark.parametrize(
    ("text", "names"),
    [
        ("auto result = f(x);", ("result",)),
        ("std::vector<std::pair<int, int>> rows{};", ("rows",)),
        ("std::vector<int> v(3);", ("v",)),
        ("static int count = 0;", ("count",)),
        ("static thread_local std::array<int, 3> table;", ("table",)),
        ("auto [code, out] = run();", ("code", "out")),
        ("auto& [a, b] = pair;", ("a", "b")),
        ("std::int64_t ts : {1000, 2000})", ("ts",)),
        ("aletheia::DbcMessage msg{", ("msg",)),
        ("auto cp = [](int p) { return p; };", ("cp",)),
        ("static auto [lo, hi] = bounds();", ("lo", "hi")),
        ("auto [ a , b ] = f();", ("a", "b")),
        ("int values[N] = {};", ("values",)),
        ("std::map<int, int> m = make(x);", ("m",)),
        ("auto row : rows)", ("row",)),
        ("Widget item{source};", ("item",)),
        ("Widget slot; fill(other);", ("slot",)),
        ("decltype(make()) typed = make();", ("typed",)),
        ("CHECK(x == 1);", ()),
        ("n = std::move(x)] { return n; };", ()),
        ("x = 2;", ()),
    ],
)
def test_a_declaration_names_what_it_declares(text: SourceLine, names: tuple[Name, ...]) -> None:
    """The last identifier before the initializer, a structured binding's list, or nothing."""
    assert declared_names(text) == names


@pytest.mark.parametrize(
    ("text", "made"),
    [
        ("auto x = f();", "auto const x = f();"),
        ("auto [a, b] = f();", "auto const [a, b] = f();"),
        ("std::string s = t;", "const std::string s = t;"),
        ("static int count = 0;", "static const int count = 0;"),
        (
            "static thread_local auto table = make();",
            "static thread_local auto const table = make();",
        ),
        ("autonomous x{};", "const autonomous x{};"),
    ],
)
def test_const_is_spelled_as_the_tree_spells_it(text: SourceLine, made: SourceLine) -> None:
    """`auto const` for a deduced type, `const T` for a named one, after the storage words."""
    assert constify(text) == made


def _source(repo: Path, rel: RelPath, lines: list[SourceLine]) -> Path:
    """Write a source file under the repo and return its path."""
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    _ = path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def _binds(path: Path, line: LineNo, name: BindName) -> QueryOutput:
    """One match of one binding, at column 5, as clang-query prints it."""
    return QueryOutput(f'\nMatch #1:\n\n{path}:{line}:5: note: "{name}" binds here\n')


def test_the_scan_keeps_candidates_and_drops_what_an_exclusion_names(tmp_path: Path) -> None:
    """Exclusions, macro locals, another tree's files and repeats across units do not survive.

    What is left comes back in the file's order, its text collapsed as the record keys it.
    """
    rel = RelPath("cpp/tests/t.cpp")
    texts = (
        "auto  kept =  f();",
        "auto moved = g();",
        "CHECK(kept);",
        "auto j = h();",
        "int later;",
    )
    source = _source(tmp_path, rel, [SourceLine(f"    {t}") for t in texts])
    elsewhere = _source(tmp_path, RelPath("vendor/v.cpp"), [SourceLine("    auto far = f();")])
    candidate, moved, read = BindName("candidate"), BindName("moved"), BindName("const_json_read")
    scoped = QueryOutput(
        _binds(source, LineNo(1), candidate) + f'{source}:1:1: note: "scope" binds here\n'
    )
    first = QueryOutput(
        _binds(source, LineNo(5), candidate)
        + scoped
        + _binds(source, LineNo(2), candidate)
        + _binds(source, LineNo(2), moved)
        + _binds(source, LineNo(3), candidate)
        + _binds(elsewhere, LineNo(1), candidate)
        + _binds(source, LineNo(4), read)
    )
    second = _binds(source, LineNo(1), candidate)
    found = scan(tmp_path, [UnitPath("/u1.cpp"), UnitPath("/u2.cpp")], [first, second])
    kept = Candidate(
        Site(rel, LineNo(1), Column(5)),
        (Name("kept"),),
        CanonicalText("auto kept = f();"),
        UnitPath("/u1.cpp"),
        LineNo(1),
    )
    later = Candidate(
        Site(rel, LineNo(5), Column(5)),
        (Name("later"),),
        CanonicalText("int later;"),
        UnitPath("/u1.cpp"),
        _NO_SCOPE,
    )
    assert found.candidates == [kept, later]
    assert found.const_json_reads == [Site(rel, LineNo(4), Column(5))]


def _lines(*texts: SourceLine) -> list[SourceLine]:
    """Return a file's lines, numbered from 1 by their position."""
    return list(texts)


def test_a_declared_const_note_settles_its_declaration(tmp_path: Path) -> None:
    """The note naming a declaration made const settles that candidate."""
    file = tmp_path / "a.cpp"
    a, b = _candidate(LineNo(1), Name("a")), _candidate(LineNo(2), Name("b"))
    diagnostics = Diagnostics(
        f"{file}:3:5: error: cannot assign to variable 'a' with const-qualified type 'const int'\n"
        + f"{file}:1:16: note: variable 'a' declared const here\n"
    )
    lines = _lines(
        SourceLine("auto const a = 1;"), SourceLine("auto const b = 2;"), SourceLine("x(); y();")
    )
    assert settled(
        Compiled(ok=False, diagnostics=diagnostics), file, lines, frozenset({a, b}), (LineNo(0),)
    ) == frozenset({a})


def test_an_error_line_naming_one_candidate_settles_it_and_one_naming_two_does_not(
    tmp_path: Path,
) -> None:
    """A line names its candidate only when it names exactly one."""
    file = tmp_path / "a.cpp"
    a, b, c = (
        _candidate(LineNo(1), Name("a")),
        _candidate(LineNo(2), Name("b")),
        _candidate(LineNo(3), Name("cc")),
    )
    lines = [
        SourceLine(t)
        for t in (
            "auto const a = 1;",
            "auto const b = 2;",
            "auto const cc = 3;",
            "a.push(b);",
            "cc.push(1);",
        )
    ]
    diagnostics = Diagnostics(f"{file}:4:3: error: no member\n{file}:5:4: error: no member\n")
    assert settled(
        Compiled(ok=False, diagnostics=diagnostics), file, lines, frozenset({a, b, c}), (LineNo(0),)
    ) == frozenset({c})


def test_an_instantiation_line_settles_and_another_note_or_file_does_not(tmp_path: Path) -> None:
    """A "requested here" note names a line; another note, file, or a line past the end does not."""
    file = tmp_path / "a.cpp"
    a, b, c = (
        _candidate(LineNo(1), Name("a")),
        _candidate(LineNo(2), Name("b")),
        _candidate(LineNo(3), Name("c")),
    )
    texts = (
        "auto const a = 1;",
        "auto const b = 2;",
        "auto const c = 3;",
        "use(a);",
        "use(b);",
        "use(c);",
    )
    lines = [SourceLine(t) for t in texts]
    diagnostics = Diagnostics(
        "/usr/include/x.h:9:1: error: in a header\n"
        + f"{file}:4:5: note: in instantiation of function template specialization requested here\n"
        + f"{file}:5:5: note: candidate function not viable\n"
        + f"{tmp_path / 'b.cpp'}:6:5: error: elsewhere\n"
        + f"{file}:99:1: error: past the end\n"
        + f"{file}:6:1: warning: not an error\n"
    )
    assert settled(
        Compiled(ok=False, diagnostics=diagnostics), file, lines, frozenset({a, b, c}), (LineNo(0),)
    ) == frozenset({a})


def test_a_diagnostic_spelling_the_file_through_a_parent_segment_settles_it(
    tmp_path: Path,
) -> None:
    """A header a relative include reaches is named through `..`; folded, it is the file."""
    file = tmp_path / "src" / "a.hpp"
    a = _candidate(LineNo(1), Name("a"))
    lines = [SourceLine("auto a = 1;"), SourceLine("use(a);")]
    diagnostics = Diagnostics(
        f"{tmp_path}/tests/../src/a.hpp:2:5: error: no matching function for call to 'use'\n"
        + f"{tmp_path}/tests/../src/a.hpp:1:6: note: variable 'a' declared const here\n"
    )
    assert settled(
        Compiled(ok=False, diagnostics=diagnostics), file, lines, frozenset({a}), (LineNo(0),)
    ) == frozenset({a})


def test_a_const_object_is_blamed_where_the_column_points(tmp_path: Path) -> None:
    """A const object is blamed where the column points: before a `.`, at it, or just before it."""
    file = tmp_path / "a.cpp"
    a, b, c = (
        _candidate(LineNo(1), Name("client")),
        _candidate(LineNo(2), Name("props")),
        _candidate(LineNo(3), Name("m")),
    )
    texts = (
        "auto client = make();",
        "auto props = list();",
        "auto m = map();",
        "    REQUIRE(client.set(props).ok());",
        "    props.push_back(client.make());",
        "    m[1] = props.size();",
    )
    lines = [SourceLine(t) for t in texts]
    diagnostics = Diagnostics(
        f"{file}:4:13: error: 'this' argument to member function 'set' has type 'const C'\n"
        + f"{file}:5:11: error: no matching member function for call to 'push_back'\n"
        + "/usr/include/v.h:1:1: note: candidate not viable: 'this' argument has type 'const V'\n"
        + f"{file}:6:6: error: no viable overloaded operator[] for type 'const M'\n"
    )
    pending = frozenset({a, b, c})
    assert (
        settled(Compiled(ok=False, diagnostics=diagnostics), file, lines, pending, (LineNo(0),))
        == pending
    )


def test_a_name_reads_as_its_nearest_declaration_in_the_same_function(tmp_path: Path) -> None:
    """Two cases declare one name; a use in a later case never settles an earlier one's."""
    file = tmp_path / "a.cpp"
    first = _candidate(LineNo(2), Name("id"), scope=LineNo(1))
    other = _candidate(LineNo(6), Name("other"), scope=LineNo(5))
    later = _candidate(LineNo(12), Name("id"), scope=LineNo(10))
    texts = [
        "TEST_CASE(a) {",
        "auto id = 1;",
        "}",
        "",
        "TEST_CASE(b) {",
        "auto other = 2;",
        "use(id);",
        "}",
        "",
        "TEST_CASE(c) {",
        "",
        "auto id = 3;",
        "id.write();",
    ]
    lines = [SourceLine(t) for t in texts]
    diagnostics = Diagnostics(
        f"{file}:7:1: error: no matching function\n{file}:13:1: error: 'this' argument is const\n"
    )
    scopes = (LineNo(1), LineNo(5), LineNo(10))
    found = settled(
        Compiled(ok=False, diagnostics=diagnostics),
        file,
        lines,
        frozenset({first, other, later}),
        scopes,
    )
    assert found == frozenset({later})


def test_a_use_on_its_declaration_line_in_a_one_line_function_settles_it(tmp_path: Path) -> None:
    """A function opening on the line its local is declared and used on still reads that local."""
    file = tmp_path / "a.cpp"
    earlier = _candidate(LineNo(1), Name("y"), scope=LineNo(1))
    oneliner = Candidate(
        Site(_FILE, LineNo(3), Column(16)),
        (Name("y"),),
        CanonicalText("auto const y = f();"),
        _UNIT,
        LineNo(3),
    )
    texts = (
        "int e() { auto y = f(); return y; }",
        "",
        "int g() { auto const y = f(); y.put(); return 0; }",
    )
    lines = [SourceLine(t) for t in texts]
    diagnostics = Diagnostics(
        f"{file}:3:31: error: 'this' argument to member function 'put' is const\n"
    )
    pending = frozenset({earlier, oneliner})
    found = settled(
        Compiled(ok=False, diagnostics=diagnostics), file, lines, pending, (LineNo(1), LineNo(3))
    )
    assert found == frozenset({oneliner})


def test_a_declared_const_note_settles_only_the_declaration_it_points_at(tmp_path: Path) -> None:
    """The note settles the candidate on its line with its name: not a namesake, not a neighbour."""
    file = tmp_path / "a.cpp"
    here = Candidate(
        Site(_FILE, LineNo(1), Column(11)),
        (Name("a"),),
        CanonicalText("auto a = 1;"),
        _UNIT,
        LineNo(1),
    )
    neighbour = Candidate(
        Site(_FILE, LineNo(1), Column(23)),
        (Name("b"),),
        CanonicalText("auto b = 2;"),
        _UNIT,
        LineNo(1),
    )
    namesake = _candidate(LineNo(2), Name("a"), scope=LineNo(2))
    lines = _lines(
        SourceLine("int e() { auto a = 1; auto b = 2; a = b; return a; }"),
        SourceLine("int g() { auto a = 3; return a; }"),
    )
    diagnostics = Diagnostics(
        f"{file}:1:37: error: cannot assign to variable 'a' with const-qualified type 'const int'\n"
        + f"{file}:1:21: note: variable 'a' declared const here\n"
    )
    pending = frozenset({here, neighbour, namesake})
    compiled = Compiled(ok=False, diagnostics=diagnostics)
    assert settled(compiled, file, lines, pending, (LineNo(1), LineNo(2))) == frozenset({here})


def test_a_name_inside_a_longer_word_is_no_use_of_it(tmp_path: Path) -> None:
    """A candidate's name read inside another identifier does not make the line name it."""
    file = tmp_path / "a.cpp"
    a, b = _candidate(LineNo(1), Name("a")), _candidate(LineNo(2), Name("b"))
    lines = _lines(
        SourceLine("auto a = 1;"), SourceLine("auto b = v();"), SourceLine("cat.push(b);")
    )
    diagnostics = Diagnostics(f"{file}:3:1: error: no matching function for call to 'push'\n")
    compiled = Compiled(ok=False, diagnostics=diagnostics)
    assert settled(compiled, file, lines, frozenset({a, b}), (LineNo(0),)) == frozenset({b})


def test_a_shadowed_name_reads_as_the_inner_declaration(tmp_path: Path) -> None:
    """Of two declarations of one name in one function, the nearer one above the use is meant."""
    file = tmp_path / "a.cpp"
    outer = _candidate(LineNo(2), Name("v"), scope=LineNo(1))
    inner = _candidate(LineNo(4), Name("v"), scope=LineNo(1))
    texts = ("int f() {", "auto v = 1;", "{", "auto v = make();", "v.write();", "}")
    diagnostics = Diagnostics(
        f"{file}:5:1: error: 'this' argument to member function 'write' has type 'const V'\n"
    )
    compiled = Compiled(ok=False, diagnostics=diagnostics)
    lines = [SourceLine(t) for t in texts]
    assert settled(compiled, file, lines, frozenset({outer, inner}), (LineNo(1),)) == frozenset(
        {inner}
    )


def test_an_error_blames_its_object_only_by_its_own_notes(tmp_path: Path) -> None:
    """A member error's object is blamed; the next error, whose notes blame nothing, is not."""
    file = tmp_path / "a.cpp"
    alpha, beta, gamma, delta = (
        _candidate(LineNo(n), Name(name))
        for n, name in enumerate(("alpha", "beta", "gamma", "delta"), start=1)
    )
    texts = (
        "auto alpha = a();",
        "auto beta = b();",
        "auto gamma = c();",
        "auto delta = d();",
        "alpha.set(beta);",
        "call(gamma, delta);",
    )
    diagnostics = Diagnostics(
        f"{file}:5:1: error: 'this' argument to member function 'set' has type 'const A'\n"
        + f"{file}:6:6: error: no matching function for call to 'call'\n"
    )
    compiled = Compiled(ok=False, diagnostics=diagnostics)
    lines = [SourceLine(t) for t in texts]
    pending = frozenset({alpha, beta, gamma, delta})
    assert settled(compiled, file, lines, pending, (LineNo(0),)) == frozenset({alpha})


def test_a_note_after_no_error_the_gate_reads_still_names_its_line(tmp_path: Path) -> None:
    """A note opening the diagnostics, as one after a fatal error does, is read on its own."""
    file = tmp_path / "a.cpp"
    a = _candidate(LineNo(1), Name("a"))
    diagnostics = Diagnostics(
        f"{file}:2:1: note: in instantiation of function template specialization requested here\n"
    )
    compiled = Compiled(ok=False, diagnostics=diagnostics)
    lines = _lines(SourceLine("auto a = 1;"), SourceLine("use(a);"))
    assert settled(compiled, file, lines, frozenset({a}), (LineNo(0),)) == frozenset({a})


def test_an_object_reached_through_an_arrow_is_blamed(tmp_path: Path) -> None:
    """A member call through ``->``, pointed at its member, blames the object before it."""
    file = tmp_path / "a.cpp"
    owner, item = _candidate(LineNo(1), Name("owner")), _candidate(LineNo(2), Name("item"))
    lines = _lines(
        SourceLine("auto owner = o();"),
        SourceLine("auto item = i();"),
        SourceLine("owner->add(item);"),
    )
    diagnostics = Diagnostics(
        f"{file}:3:8: error: 'this' argument to member function 'add' has type 'const O'\n"
    )
    compiled = Compiled(ok=False, diagnostics=diagnostics)
    assert settled(compiled, file, lines, frozenset({owner, item}), (LineNo(0),)) == frozenset(
        {owner}
    )


def _compiler(
    written: set[Candidate], calls: list[frozenset[Candidate]]
) -> Callable[[frozenset[Candidate]], Compiled]:
    """Return a compiler failing exactly when a written candidate is made const; log each call."""

    def compile_with(made: frozenset[Candidate]) -> Compiled:
        calls.append(made)
        return Compiled(ok=not made & written, diagnostics=Diagnostics(""))

    return compile_with


def _settles_nothing(_compiled: Compiled, _pending: frozenset[Candidate]) -> frozenset[Candidate]:
    """Settle nothing, as an attribution that can never name a candidate would."""
    return frozenset()


def test_a_clean_compile_settles_everything_at_once() -> None:
    """When every candidate compiles as const, one compile says so."""
    pending = _many(LineNo(8))
    calls: list[frozenset[Candidate]] = []
    assert resolve(pending, _compiler(set(), calls), _settles_nothing) == pending
    assert calls == [pending]


def test_settled_candidates_leave_and_the_rest_compile_again() -> None:
    """Each round drops what the compile settled, until the rest compile."""
    a, b, c = (
        _candidate(LineNo(1), Name("a")),
        _candidate(LineNo(2), Name("b")),
        _candidate(LineNo(3), Name("c")),
    )
    calls: list[frozenset[Candidate]] = []
    found = resolve(frozenset({a, b, c}), _compiler({a}, calls), lambda _c, pending: pending & {a})
    assert found == frozenset({b, c})
    assert calls == [frozenset({a, b, c}), frozenset({b, c})]


def test_nothing_settled_halves_the_pending_and_ends_at_single_candidates() -> None:
    """With no attribution the pending set is halved, each half alone, down to singles."""
    pending = _many(LineNo(10))
    v3, v8 = _candidate(LineNo(3), Name("v3")), _candidate(LineNo(8), Name("v8"))
    calls: list[frozenset[Candidate]] = []
    found = resolve(pending, _compiler({v3, v8}, calls), _settles_nothing)
    assert found == pending - {v3, v8}
    assert frozenset({v3}) in calls
    assert frozenset({v8}) in calls


def test_four_unsettled_candidates_are_tried_alone_and_five_are_halved_first() -> None:
    """Up to four candidates a round cannot settle are compiled one by one; five are split first."""
    four = _many(LineNo(4))
    calls: list[frozenset[Candidate]] = []
    v4 = _candidate(LineNo(4), Name("v4"))
    assert resolve(four, _compiler({v4}, calls), _settles_nothing) == four - {v4}
    assert calls == [four, *(frozenset({c}) for c in sorted(four))]
    five = _many(LineNo(5))
    calls.clear()
    v5 = _candidate(LineNo(5), Name("v5"))
    assert resolve(five, _compiler({v5}, calls), _settles_nothing) == five - {v5}
    first, rest = frozenset(sorted(five)[:2]), sorted(five)[2:]
    assert calls == [five, first, frozenset(rest), *(frozenset({c}) for c in rest)]


def test_a_pair_that_only_fails_together_still_ends() -> None:
    """Two candidates const together fail and alone pass: the halving ends, keeping both."""
    a, b = _candidate(LineNo(1), Name("a")), _candidate(LineNo(2), Name("b"))

    def compile_with(made: frozenset[Candidate]) -> Compiled:
        return Compiled(ok=not {a, b} <= made, diagnostics=Diagnostics(""))

    assert resolve(frozenset({a, b}), compile_with, _settles_nothing) == frozenset({a, b})


def test_an_empty_pending_set_compiles_nothing() -> None:
    """No candidates, no compile."""
    calls: list[frozenset[Candidate]] = []
    assert resolve(frozenset(), _compiler(set(), calls), _settles_nothing) == frozenset()
    assert not calls


def test_a_compile_command_loses_its_output_and_gains_a_syntax_check(tmp_path: Path) -> None:
    """Both database spellings, arguments and command, keep their flags and drop `-o FILE`."""
    database = tmp_path / gate.COMPILE_DB
    database.parent.mkdir(parents=True)
    entries = [
        {
            "file": "/u1.cpp",
            "directory": "/b",
            "arguments": ["clang++", "-Ia", "-o", "u1.o", "-c", "/u1.cpp"],
        },
        {"file": "/u2.cpp", "directory": "/b", "command": "clang++ -DX='a b' -o u2.o -c /u2.cpp"},
        {"file": "/u3.cpp", "directory": "/b", "arguments": ["clang++", "-c", "/u3.cpp", "-o"]},
    ]
    _ = database.write_text(json.dumps(entries), encoding="utf-8")
    extra = [CompileArg("-fsyntax-only"), CompileArg("-ferror-limit=0"), CompileArg("-w")]
    commands = compile_commands(tmp_path)
    first = [CompileArg(a) for a in ("clang++", "-Ia", "-c", "/u1.cpp")]
    second = [CompileArg(a) for a in ("clang++", "-DX=a b", "-c", "/u2.cpp")]
    assert commands[UnitPath("/u1.cpp")] == CompileCommand([*first, *extra], Path("/b"))
    assert commands[UnitPath("/u2.cpp")] == CompileCommand([*second, *extra], Path("/b"))
    third = [CompileArg(a) for a in ("clang++", "-c", "/u3.cpp")]
    assert commands[UnitPath("/u3.cpp")] == CompileCommand([*third, *extra], Path("/b"))


class Finished(NamedTuple):
    """What the stand-in for subprocess.run hands back: the two fields the gate reads."""

    returncode: ExitStatus
    stderr: Diagnostics


class Overlay(NamedTuple):
    """What one syntax check handed the compiler: the overlay's fields and the copy it maps."""

    external_names: bool
    mapped: Path
    copy: FileText
    flag: CompileArg


def test_a_syntax_check_overlays_the_file_with_its_candidates_const(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The overlay maps the original to a copy with each candidate const; the tree is untouched."""
    rel = RelPath("cpp/src/a.cpp")
    original = _source(
        tmp_path,
        rel,
        [SourceLine(t) for t in ("int f() {", "    auto x = 1;", "    int y = 2;", "}")],
    )
    seen: list[Overlay] = []

    def run(
        argv: list[CompileArg], *, cwd: Path, capture_output: bool, text: bool, check: bool
    ) -> Finished:
        assert (cwd, capture_output, text, check) == (tmp_path, True, True, False)
        document = json.loads(Path(argv[-1]).read_text(encoding="utf-8"))
        entry = document["roots"][0]
        copy = FileText(Path(entry["contents"][0]["external-contents"]).read_text(encoding="utf-8"))
        mapped = Path(entry["name"]) / entry["contents"][0]["name"]
        seen.append(Overlay(document["use-external-names"], mapped, copy, argv[-2]))
        return Finished(ExitStatus(1), Diagnostics("an error\n"))

    monkeypatch.setattr(gate.subprocess, "run", run)
    x = Candidate(
        Site(rel, LineNo(2), Column(5)),
        (Name("x"),),
        CanonicalText("auto x = 1;"),
        _UNIT,
        LineNo(1),
    )
    y = Candidate(
        Site(rel, LineNo(3), Column(5)), (Name("y"),), CanonicalText("int y = 2;"), _UNIT, LineNo(1)
    )
    compiled = syntax_check(
        tmp_path, CompileCommand([CompileArg("clang++")], tmp_path), tmp_path, frozenset({x, y})
    )
    assert compiled == Compiled(ok=False, diagnostics=Diagnostics("an error\n"))
    made = FileText("int f() {\n    auto const x = 1;\n    const int y = 2;\n}\n")
    assert seen == [
        Overlay(external_names=False, mapped=original, copy=made, flag=CompileArg("-ivfsoverlay"))
    ]
    assert original.read_text(encoding="utf-8") == "int f() {\n    auto x = 1;\n    int y = 2;\n}\n"


def test_each_file_is_resolved_on_the_executor_handed_in(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Candidates group by file, each file compiled through its first candidate's unit."""
    database = tmp_path / gate.COMPILE_DB
    database.parent.mkdir(parents=True)
    _ = database.write_text(
        json.dumps([{"file": "/unit.cpp", "directory": "/b", "arguments": ["cc"]}]),
        encoding="utf-8",
    )
    other = RelPath("cpp/src/b.cpp")
    _ = _source(tmp_path, _FILE, [SourceLine("auto a = 1;"), SourceLine("auto b = 2;")])
    _ = _source(tmp_path, other, [SourceLine("auto c = 3;")])
    a, b = _candidate(LineNo(1), Name("a")), _candidate(LineNo(2), Name("b"))
    c = _candidate(LineNo(1), Name("c"), file=other)
    compiled: list[tuple[RelPath, Path]] = []

    def fake(
        _repo: Path, command: CompileCommand, _scratch: Path, made: frozenset[Candidate]
    ) -> Compiled:
        compiled.append((next(iter(made)).site.file, command.directory))
        return Compiled(ok=b not in made, diagnostics=Diagnostics(""))

    monkeypatch.setattr(gate, "syntax_check", fake)
    assert const_able(tmp_path, [a, b, c], WorkerCount(2), executor=DrivenExecutor) == sorted(
        [a, c]
    )
    assert compiled[0] == (_FILE, Path("/b"))
    assert (other, Path("/b")) in compiled


def test_an_unrecorded_local_fails_with_the_row_that_would_allow_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A finding the record does not name fails the gate, which prints its row."""
    printed = _printed(monkeypatch)
    found = [_candidate(LineNo(4), Name("a")), _candidate(LineNo(9), Name("a"))]
    assert report(found, [], {}) == ExitStatus(1)
    assert Prose(f"{_FILE}:4,9: a local is never written and is not const") in printed
    assert Prose(as_row(_FILE, CanonicalText("auto a = f()"), 2)) in printed


def test_each_unrecorded_row_lists_only_its_own_lines(monkeypatch: pytest.MonkeyPatch) -> None:
    """Two declarations of one file, each its own row, each listed at its own line."""
    printed = _printed(monkeypatch)
    found = [_candidate(LineNo(4), Name("a")), _candidate(LineNo(9), Name("b"))]
    assert report(found, [], {}) == ExitStatus(1)
    assert Prose(f"{_FILE}:4: a local is never written and is not const") in printed
    assert Prose(f"{_FILE}:9: a local is never written and is not const") in printed


def test_a_recorded_local_passes_and_a_stale_row_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    """A row covers its findings; a row naming more than the gate finds is stale."""
    printed = _printed(monkeypatch)
    key = RowKey(_FILE, CanonicalText("auto a = f()"))
    assert report([_candidate(LineNo(4), Name("a"))], [], {key: 1}) == ExitStatus(0)
    assert printed[-1] == Prose(
        "C++ locals that compile as const and are not: 1, every one recorded"
    )
    assert report([], [], {key: 1}) == ExitStatus(1)
    assert Prose(f"{_FILE}: a recorded row names more locals than the gate finds") in printed


def test_a_const_json_read_through_brackets_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    """A read of a const JSON document through operator[] is refused outright."""
    printed = _printed(monkeypatch)
    site = Site(RelPath("cpp/tests/t.cpp"), LineNo(7), Column(9))
    assert report([], [site], {}) == ExitStatus(1)
    assert printed[0].startswith(
        "cpp/tests/t.cpp:7: a const JSON document is read through operator[]"
    )
    assert printed[-1] == Prose("0 unrecorded, 0 stale, 1 const JSON reads")


def test_a_count_below_one_is_refused(monkeypatch: pytest.MonkeyPatch) -> None:
    """--jobs takes a positive count."""
    monkeypatch.setattr("sys.argv", ["check_cpp_const_locals", "--jobs", "0"])
    with pytest.raises(SystemExit) as exited:
        _ = gate.main()
    assert exited.value.code == 2


def test_a_missing_compile_database_fails_the_gate(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Without the lint tree's database the gate cannot run, and says how to configure it."""
    printed = _printed(monkeypatch)
    monkeypatch.setattr("sys.argv", ["check_cpp_const_locals"])
    monkeypatch.setattr(clang_query, "git_toplevel", lambda: tmp_path)
    assert gate.main() == ExitStatus(1)
    assert "is missing, so the gate cannot run" in printed[0]


def _one_unit(_repo: Path) -> list[UnitPath]:
    """List one unit, as the compile database would."""
    return [UnitPath("/u.cpp")]


def _no_units(_repo: Path) -> list[UnitPath]:
    """List no unit."""
    return []


def _failed_query(
    _repo: Path, _units: list[UnitPath], _query: Query, *, executor: ExecutorFactory
) -> Prose:
    """Fail, as the query helper reports a failed clang-query."""
    del executor
    return Prose("clang-query failed")


def _no_outputs(
    _repo: Path, _units: list[UnitPath], _query: Query, *, executor: ExecutorFactory
) -> list[QueryOutput]:
    """Print nothing, as clang-query over no unit does."""
    del executor
    return []


def test_a_failed_query_fails_the_gate_with_its_message(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """When clang-query fails on a unit, the gate prints why and fails without judging."""
    printed = _printed(monkeypatch)
    monkeypatch.setattr("sys.argv", ["check_cpp_const_locals", "--jobs", "1"])
    monkeypatch.setattr(clang_query, "git_toplevel", lambda: tmp_path)
    monkeypatch.setattr(clang_query, "translation_units", _one_unit)
    monkeypatch.setattr(clang_query, "query_units", _failed_query)
    assert gate.main() == ExitStatus(1)
    assert printed == [Prose("clang-query failed")]


def test_an_unreadable_record_fails_the_gate_with_its_message(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """When the record cannot be read, the gate prints why and fails without judging."""
    printed = _printed(monkeypatch)
    monkeypatch.setattr("sys.argv", ["check_cpp_const_locals", "--jobs", "1"])
    monkeypatch.setattr(clang_query, "git_toplevel", lambda: tmp_path)
    monkeypatch.setattr(clang_query, "translation_units", _no_units)
    monkeypatch.setattr(clang_query, "query_units", _no_outputs)
    assert gate.main() == ExitStatus(1)
    assert len(printed) == 1
    assert str(gate.ALLOWLIST) in printed[0]
