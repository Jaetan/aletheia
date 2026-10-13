# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The const-locals gate's query and compiles, run for real over a planted tree.

The planted tree holds one case per exclusion, per kind of local the query never
lists, and per kind it lists although a near neighbour is excluded; clang-query
and the compiler are the real ones, so what the matchers bind and what the
diagnostics settle are held here, end to end through ``main`` as well.
"""

from __future__ import annotations

import functools
import json
import re
from typing import TYPE_CHECKING, NamedTuple

import pytest
from _executors import DrivenExecutor

from tools import _clang_query as clang_query
from tools import check_cpp_const_locals as gate
from tools._clang_query import UnitPath, query_unit
from tools._common import RelPath, WorkerCount
from tools.check_cpp_const_locals import (
    Candidate,
    Compiled,
    LineNo,
    Name,
    SourceLine,
    const_able,
    scan,
    settled,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

# A binding line of clang-query's output: the file it names, and what it binds.
_BOUND = re.compile(r'^(/[^\s:]+):\d+:\d+: note: "([a-z_]+)" binds here$', re.MULTILINE)


def _printed(monkeypatch: pytest.MonkeyPatch) -> list[Prose]:
    """Collect what the gate prints, line by line."""
    lines: list[Prose] = []
    monkeypatch.setattr(gate, "emit", lines.append)
    monkeypatch.setattr(clang_query, "emit", lines.append)
    return lines


_PLANTED = """\
#include <cstddef>
#include <string>
#include <utility>
#include <vector>
#include "../vendor/planted_relative.hpp"
#include "planted_benchmarks.hpp"
#include "planted_include.hpp"
#include "planted_src.hpp"
#include "planted_vendor.hpp"
namespace nlohmann {
template <class T> struct basic_json {
    auto operator[](const char* key) -> basic_json&;
    auto operator[](const char* key) const -> const basic_json&;
};
}  // namespace nlohmann
using Json = nlohmann::basic_json<int>;
#define HOLD(x) auto held = (x)
auto make() -> std::string;
auto sink(std::string s) -> void;
auto read(const std::string& s) -> std::size_t;
struct Wide { Wide(std::string s); };
struct Pair { Pair(std::string a, int b); };
struct Holder { std::vector<int> entries; };
auto f() -> std::size_t {
    auto never_written = make();
    auto pushed = std::vector<int>{};
    pushed.push_back(1);
    auto moved = make();
    sink(std::move(moved));
    auto [left, right] = std::pair{make(), 1};
    auto [first_moved, second_kept] = std::pair{make(), make()};
    sink(std::move(first_moved));
    auto member_moved = std::pair{make(), 1};
    sink(std::move(member_moved.first));
    static int counter = 0;
    ++counter;
    static auto label = make();
    constexpr int limit = 3;
    auto pointer = pushed.data();
    auto j = Json{};
    auto& field = j["k"];
    const Json k{};
    auto& read_field = k["k"];
    auto table = std::vector<int>{1};
    const std::vector<int> fixed_table{1};
    decltype(make()) typed = make();
    auto with_init = [n = make()] { return read(n); };
    HOLD(make());
    return read(never_written) + pushed.size() + read(left) + read(second_kept) + read(held)
        + static_cast<std::size_t>(right + counter + limit + table[0] + fixed_table[0])
        + read(label) + read(typed) + with_init() + sizeof(field) + sizeof(read_field)
        + sizeof(pointer);
}
auto g() -> std::string { auto returned = make(); return returned; }
auto gp() -> std::string { auto parenthesized = make(); return (parenthesized); }
auto h() -> Wide { auto converted = make(); return converted; }
auto o() -> Pair { auto first = make(); return Pair(first, 1); }
auto li() -> Wide { auto braced = make(); return {braced}; }
auto sc() -> int { auto scalar = 1; return scalar; }
auto kept() -> const std::string& { static auto stored = make(); return stored; }
auto t() -> void { auto thrown = make(); throw thrown; }
auto tp() -> void { auto thrown_paren = make(); throw (thrown_paren); }
auto tc() -> void { auto copied_out = make(); throw Wide(copied_out); }
auto loop() -> void {
    auto rows = std::vector<std::string>{};
    for (auto& r : rows) sink(std::move(r));
}
auto loop_read() -> void {
    auto items = std::vector<std::string>{};
    for (auto& item : items) {
        auto spare = make();
        sink(item);
        sink(std::move(spare));
    }
}
auto lam() -> std::size_t {
    auto captured = make();
    auto by_ref = [&] { return read(captured); };
    return by_ref();
}
auto p(std::string param) -> std::size_t { return read(param); }
auto sa() -> std::size_t { auto entries = make(); return read(entries); }
auto sb() -> std::size_t {
    auto holder = Holder{};
    holder.entries.push_back(1);
    return holder.entries.size();
}
auto sl() -> std::size_t {
    auto outer = std::vector<int>{};
    auto fill = [&] {
        auto step = 1;
        outer.push_back(step);
    };
    fill();
    return outer.size();
}
"""

# One header per directory, each declaring one never-written local, all reached
# through the include path but the one a relative include reaches from cpp/tests.
_HEADERS = {
    RelPath(f"cpp/{where}/planted_{name}.hpp"): f"""\
#pragma once
#include <string>
inline auto from_{name}() -> std::size_t {{
    auto in_{name} = std::string{{"x"}};
    return in_{name}.size();
}}
"""
    for where, name in (
        ("src", "src"),
        ("include", "include"),
        ("benchmarks", "benchmarks"),
        ("vendor", "vendor"),
        ("vendor", "relative"),
    )
}
_INCLUDE_PATH = ("src", "include", "benchmarks", "vendor")

# What the planted tree declares: every candidate, and the ones that compile as const.
_CANDIDATES = frozenset(
    Name(n)
    for n in (
        "in_src", "in_include", "in_benchmarks", "never_written", "pushed", "left", "right",
        "counter", "label", "table", "typed", "with_init", "first", "braced", "scalar", "stored",
        "copied_out", "items", "captured", "by_ref", "entries", "holder", "outer", "fill", "step",
    )
)  # fmt: skip
_WRITTEN = frozenset(Name(n) for n in ("pushed", "counter", "holder", "outer"))


class Planted(NamedTuple):
    """The planted tree: its root, its one unit, and that unit repo-relative."""

    root: Path
    unit: UnitPath
    rel: RelPath


def _planted_tree(root: Path) -> Planted:
    """Write the planted sources and a compile database naming the unit, as CMake would."""
    rel = RelPath("cpp/tests/planted.cpp")
    for header, text in {rel: _PLANTED, **_HEADERS}.items():
        (root / header).parent.mkdir(parents=True, exist_ok=True)
        _ = (root / header).write_text(text, encoding="utf-8")
    unit = root / rel
    database = root / gate.COMPILE_DB
    database.parent.mkdir(parents=True)
    include = " ".join(f"-I{root / 'cpp' / where}" for where in _INCLUDE_PATH)
    entry = {
        "directory": str(root / "cpp"),
        "file": str(unit),
        "command": f"clang++-23 -std=c++23 {include} -c {unit}",
    }
    _ = database.write_text(json.dumps([entry]), encoding="utf-8")
    return Planted(root, UnitPath(str(unit)), rel)


@pytest.mark.process(
    "what the matchers bind over real C++ is the query tool's own answer, and which"
    + " locals compile as const, with the diagnostics of those that do not, the compiler's"
)
def test_the_real_query_and_compiler_find_exactly_the_planted_const_locals(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Over a planted tree, the query lists the candidates and the compiles keep the const-able.

    The query reaches every project directory and no vendored file; a vendored
    header a relative include reaches from cpp/tests is listed, and dropped
    once its path is folded to where it lies. Excluded before any
    compile: a local moved, through a member or a structured binding, or moved
    from through a range-for; returned or thrown with a move, parenthesized or
    not, or through a conversion; a JSON document read through operator[].
    Never candidates: a const, constexpr, reference or pointer local, a
    parameter, an init-capture, a macro's local. Kept as candidates: a local
    returned without a move (a scalar, a static by reference), copied into an
    explicit construction or a list, iterated without a move, indexed when it is
    no JSON document. The written ones fail as const, each failure settled by
    the diagnostics alone, a member of another function's namesake and a write
    from inside a lambda included; the const JSON read is the second rule's.
    """
    planted = _planted_tree(tmp_path)
    script = tmp_path / "gate.query"
    _ = script.write_text(gate.QUERY, encoding="utf-8")
    output = query_unit(tmp_path, script, planted.unit)
    printed = {path for path, _ in _BOUND.findall(output)}
    assert str(tmp_path / "cpp/vendor/planted_vendor.hpp") not in printed
    assert str(tmp_path / "cpp/tests/../vendor/planted_relative.hpp") in printed
    found = scan(tmp_path, [planted.unit], [output])
    assert {name for candidate in found.candidates for name in candidate.names} == _CANDIDATES
    rounds: list[frozenset[Candidate]] = []

    def recorded(
        compiled: Compiled,
        file: Path,
        lines: list[SourceLine],
        pending: frozenset[Candidate],
        scopes: tuple[LineNo, ...],
    ) -> frozenset[Candidate]:
        rounds.append(settled(compiled, file, lines, pending, scopes))
        return rounds[-1]

    monkeypatch.setattr(gate, "settled", recorded)
    able = const_able(tmp_path, found.candidates, WorkerCount(1), executor=DrivenExecutor)
    assert {name for candidate in able for name in candidate.names} == _CANDIDATES - _WRITTEN
    assert rounds
    assert all(rounds)
    read_line = LineNo(_PLANTED.splitlines().index('    auto& read_field = k["k"];') + 1)
    assert [(site.file, site.line) for site in found.const_json_reads] == [(planted.rel, read_line)]


@pytest.mark.process(
    "the rows main reports are what the real query binds and the real compiler accepts"
    + " as const, passed through main's wiring end to end"
)
def test_main_judges_the_planted_tree_against_its_record(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The gate end to end, pools on the test's thread: every const-able row and the const read."""
    printed = _printed(monkeypatch)
    _ = _planted_tree(tmp_path)
    (tmp_path / gate.ALLOWLIST).parent.mkdir(parents=True)
    _ = (tmp_path / gate.ALLOWLIST).write_text("locals: []\n", encoding="utf-8")
    monkeypatch.setattr(clang_query, "git_toplevel", lambda: tmp_path)
    monkeypatch.setattr(
        gate, "query_tree", functools.partial(clang_query.query_tree, executor=DrivenExecutor)
    )
    monkeypatch.setattr(
        gate, "const_able", functools.partial(gate.const_able, executor=DrivenExecutor)
    )
    monkeypatch.setattr("sys.argv", ["check_cpp_const_locals", "--jobs", "1"])
    assert gate.main() == ExitStatus(1)
    # One row per const-able declaration; the structured binding declares two names.
    rows = len(_CANDIDATES - _WRITTEN) - 1
    assert printed[-1] == Prose(f"{rows} unrecorded, 0 stale, 1 const JSON reads")
