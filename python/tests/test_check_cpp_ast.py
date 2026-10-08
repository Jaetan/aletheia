# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every rule binds what it refuses in the one parse, and only where it refuses it.

The whole query runs under the real clang-query over a tree laid out as the
binding's: a library source holding one unchecked read per spelling the
checked-read rule names, marked on its line, beside the checked form of each,
and one declaration restating its type; a template a public header defines,
read only where a test instantiates it; and the two headers the checked-read
rule holds out, each holding a read. A matcher that stopped binding would pass
every tree, which is the one outcome a gate must not have, so each spelling is
a line here, and each rule is read out of the output it shares with the other.
"""

from __future__ import annotations

import json
import re
import shutil
from pathlib import Path
from typing import NamedTuple, NewType

import pytest

from tools import check_cpp_ast
from tools._clang_query import COMPILE_DB, QueryOutput, UnitPath, query_unit, translation_units
from tools._common import RelPath
from tools._ratchet import CanonicalText
from tools.check_cpp_ast import QUERY, AstRule, main, verdict
from tools.check_cpp_checked_reads import RULES, BindName, LineNumber, Read, reads_in
from tools.check_cpp_restated_types import Hit, parse_hits

from aletheia.common_types import ExitStatus, Prose

# The text of a C++ source the fixture writes.
CppSource = NewType("CppSource", str)

_REPO = Path(__file__).resolve().parents[2]
_CHECKED = Path("cpp/include/aletheia/detail/checked.hpp")
_DOUBLE = Path("cpp/src/detail/mock_backend.hpp")
_LIBRARY = Path("cpp/src/reads.cpp")
_HEADER = Path("cpp/include/aletheia/first.hpp")
_TEST = Path("cpp/tests/uses.cpp")

_LIBRARY_SOURCE = CppSource("""\
#include "aletheia/detail/checked.hpp"
#include "detail/mock_backend.hpp"
#include <array>
#include <cstddef>
#include <expected>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <vector>

auto a(std::optional<int> o) -> int { return *o; } // unchecked value
auto b(std::optional<std::string> o) -> std::size_t { return o->size(); } // unchecked value
auto c(std::expected<int, int> e) -> int { return *e; } // unchecked value
auto d(std::expected<std::string, int> e) -> std::size_t { return e->size(); } // unchecked value
auto f(std::expected<int, int> e) -> int { return e.error(); } // unchecked error
auto g(const std::vector<int>& v) -> int { return v[0]; } // unchecked subscript
auto h(const std::array<int, 2>& v) -> int { return v[0]; } // unchecked subscript
auto i(const std::string& s) -> char { return s[0]; } // unchecked subscript
auto j(std::string_view s) -> char { return s[0]; } // unchecked subscript
auto k(std::span<const int> s) -> std::span<const int> { return s.subspan(1); } // unchecked slice
auto l(std::span<const int> s) -> std::span<const int> { return s.first(1); } // unchecked slice
auto m(std::span<const int> s) -> std::span<const int> { return s.last(1); } // unchecked slice
void n(std::string_view s) { s.remove_prefix(1); } // unchecked narrowing
void p(std::string_view s) { s.remove_suffix(1); } // unchecked narrowing
auto q(const std::vector<int>& v) -> int { return v.front(); } // unchecked end
auto r(const std::array<int, 2>& v) -> int { return v.back(); } // unchecked end
auto s(const std::string& t) -> char { return t.front(); } // unchecked end
auto t(std::string_view u) -> char { return u.back(); } // unchecked end
auto x(const std::string& s) -> std::size_t { const std::size_t size = s.length(); return size; }

auto checked(std::optional<int> o, std::expected<int, int> e, const std::vector<int>& v,
             std::string_view s, std::span<const int> w) -> std::size_t {
    return static_cast<std::size_t>(o.value() + e.value() + aletheia::detail::error_of(e) + v.at(0))
         + s.substr(1).size() + aletheia::detail::subspan_at(w, 1).size();
}
""")

# The declaration the library source restates.
_RESTATED = CanonicalText("const std::size_t size = s.length()")

# The test double, held out: a read in it is not the library's.
_DOUBLE_SOURCE = CppSource("""\
#pragma once
#include <vector>
inline auto double_read(const std::vector<int>& v) -> int { return v[0]; }
""")

_HEADER_SOURCE = CppSource("""\
#pragma once
#include <optional>
template<typename T>
auto first_of(const std::optional<T>& o) -> T { return *o; } // unchecked value
""")

_TEST_SOURCE = CppSource("""\
#include "aletheia/first.hpp"
#include <optional>
auto use(std::optional<int> o) -> int { return first_of(o) + *o; }
""")

_MARK = re.compile(r"// (unchecked [a-z]+)$")


def _marked(path: Path, source: CppSource) -> set[Read]:
    """Collect the reads a source marks, one per line that ends in its rule's name."""
    return {
        Read(RelPath(str(path)), LineNumber(number), BindName(mark.group(1)))
        for number, line in enumerate(source.splitlines(), start=1)
        if (mark := _MARK.search(line)) is not None
    }


def _line_of(source: CppSource, text: CanonicalText) -> LineNumber:
    """Find the line of a source that holds the text, counted from 1."""
    return next(
        LineNumber(number)
        for number, line in enumerate(source.splitlines(), start=1)
        if text in line
    )


class Fixture(NamedTuple):
    """A tree laid out as the binding's, and what the whole query printed over its two units."""

    root: Path
    library: QueryOutput
    test: QueryOutput


def _query_tree(root: Path) -> Fixture:
    """Write the tree and its compile database, then query each unit."""
    cpp = root / "cpp"
    for path, source in (
        (_LIBRARY, _LIBRARY_SOURCE),
        (_DOUBLE, _DOUBLE_SOURCE),
        (_HEADER, _HEADER_SOURCE),
        (_TEST, _TEST_SOURCE),
    ):
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        _ = (root / path).write_text(source, encoding="utf-8")
    (root / _CHECKED).parent.mkdir(parents=True, exist_ok=True)
    _ = shutil.copyfile(_REPO / _CHECKED, root / _CHECKED)
    # Absolute paths in the command, as CMake writes them: clang records the
    # file as the command spells it, and the rules' path checks read that.
    units = [UnitPath(str(root / _LIBRARY)), UnitPath(str(root / _TEST))]
    commands = [
        {
            "directory": str(cpp),
            "file": unit,
            "command": f"clang++-23 -std=c++23 -I{cpp}/include -I{cpp}/src -c {unit}",
        }
        for unit in units
    ]
    (root / COMPILE_DB).parent.mkdir(parents=True)
    _ = (root / COMPILE_DB).write_text(json.dumps(commands), encoding="utf-8")
    script = root / "gate.query"
    _ = script.write_text(QUERY, encoding="utf-8")
    library, test = (query_unit(root, script, unit) for unit in units)
    return Fixture(root, library, test)


@pytest.fixture(scope="module", name="fixture")
def fixture_tree(tmp_path_factory: pytest.TempPathFactory) -> Fixture:
    """Query the tree once for the module."""
    return _query_tree(tmp_path_factory.mktemp("cpp-ast"))


def test_every_spelling_binds_its_rule_and_no_checked_form_binds(fixture: Fixture) -> None:
    """The library's reads are exactly the marked lines: each spelling, and nothing else."""
    assert set(reads_in(fixture.root, fixture.library)) == _marked(_LIBRARY, _LIBRARY_SOURCE)


def test_every_rule_is_spelled_in_the_fixture() -> None:
    """A rule the library source does not mark would go untested."""
    marked = {read.bind for read in _marked(_LIBRARY, _LIBRARY_SOURCE)}
    assert marked == {rule.bind for rule in RULES}


def test_the_held_out_headers_bind_and_are_not_counted(fixture: Fixture) -> None:
    """The helpers' and the double's reads bind, and the rule leaves them out by name."""
    for held_out in (_CHECKED, _DOUBLE):
        assert f"{fixture.root / held_out}:" in fixture.library
    assert not {read.file for read in reads_in(fixture.root, fixture.library)} & {
        RelPath(str(_CHECKED)),
        RelPath(str(_DOUBLE)),
    }


def test_a_header_template_counts_where_a_test_instantiates_it(fixture: Fixture) -> None:
    """The template's read is the library's, and the test's own read is not.

    The restated-type rule reads the source as written, which leaves the
    instantiations out, so this holds that the checked-read rule's own
    traversal is back in force for its matches.
    """
    assert set(reads_in(fixture.root, fixture.test)) == _marked(_HEADER, _HEADER_SOURCE)


def test_the_restated_declaration_is_the_one_hit(fixture: Fixture) -> None:
    """The restated-type rule binds its declaration in the same parse, and nothing else."""
    line = _line_of(_LIBRARY_SOURCE, _RESTATED)
    assert parse_hits(fixture.root, fixture.library) == [
        Hit(RelPath(str(_LIBRARY)), line, _RESTATED)
    ]


def _rule(judged: list[ExitStatus], status: ExitStatus) -> AstRule:
    """Make a rule whose judge records that it ran and returns the status."""

    def judge(_repo: Path, _outputs: list[QueryOutput]) -> ExitStatus:
        judged.append(status)
        return status

    return AstRule(QUERY, judge)


@pytest.mark.parametrize(
    ("first", "second", "expected"),
    [
        (ExitStatus(0), ExitStatus(0), ExitStatus(0)),
        (ExitStatus(1), ExitStatus(0), ExitStatus(1)),
        (ExitStatus(0), ExitStatus(1), ExitStatus(1)),
    ],
)
def test_every_rule_judges_and_any_refusal_fails(
    tmp_path: Path, first: ExitStatus, second: ExitStatus, expected: ExitStatus
) -> None:
    """Each judge prints its own findings, so each runs whatever the one before it said."""
    judged: list[ExitStatus] = []
    rules = (_rule(judged, first), _rule(judged, second))
    assert verdict(tmp_path, [], rules) == expected
    assert judged == [first, second]


def test_a_tree_with_no_database_fails(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """A tree the configure has not run in is a gate that cannot run, never a clean one."""
    printed: list[Prose] = []
    monkeypatch.setattr(check_cpp_ast, "emit", printed.append)
    monkeypatch.setattr(check_cpp_ast, "git_toplevel", lambda: tmp_path)
    monkeypatch.setattr("sys.argv", ["check_cpp_ast"])
    assert main() == ExitStatus(1)
    assert printed == [translation_units(tmp_path)]
