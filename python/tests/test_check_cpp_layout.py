# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ layout gate reads the public roster from the headers and refuses what disagrees.

The roster is every class, struct, enum and type alias a public header declares at
namespace scope, outside ``detail`` and not a template; the gate refuses a type the
record lacks, a row naming a type no header declares, a record whose soversion is
not CMake's, and a type list other than the one it derives.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools.check_cpp_layout import (
    Bytes,
    IncludePath,
    Record,
    Roster,
    Row,
    SoVersion,
    TypeName,
    bump_problems,
    parse_record,
    parse_soversion,
    problems,
    roster,
    roster_text,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_HEADER = """#pragma once
namespace aletheia {
namespace detail {
struct Hidden {
    int x;
};
} // namespace detail

class Client {
    struct Nested {
        int y;
    };
};
struct Derived final : public Client {
};
template<typename T>
class Strong {
};
template<typename T>
using Result = Strong<T>;
enum class Level : unsigned char { Low, High };
enum class Opaque : int;
class Forward;
class [[nodiscard]] Marked {
};
struct alignas(16) Aligned {
};
using Wrapped =
    std::variant<int, long>;
class Based
    : public Client {
};
enum class Split : unsigned char
{ A, B };
struct Declared;
using Payload = std::vector<std::byte>;
using namespace std;
namespace ltl {
struct Atom {
};
} // namespace ltl
namespace {
struct Unnamed {
};
} // namespace
inline namespace v1 {
struct Inlined {
};
} // namespace v1
} // namespace aletheia
"""


def _header(tmp_path: Path) -> Path:
    path = tmp_path / "client.hpp"
    _ = path.write_text(_HEADER, encoding="utf-8")
    return path


def test_the_roster_is_every_namespace_scope_definition_outside_detail_and_templates(
    tmp_path: Path,
) -> None:
    """Classes, structs, enums and aliases count, decorated, wrapped or not; detail, nested not."""
    assert roster(tmp_path, [_header(tmp_path)]).types == [
        TypeName("aletheia::Client"),
        TypeName("aletheia::Derived"),
        TypeName("aletheia::Level"),
        TypeName("aletheia::Marked"),
        TypeName("aletheia::Aligned"),
        TypeName("aletheia::Wrapped"),
        TypeName("aletheia::Based"),
        TypeName("aletheia::Split"),
        TypeName("aletheia::Payload"),
        TypeName("aletheia::ltl::Atom"),
        TypeName("aletheia::v1::Inlined"),
    ]


def _rows(*names: TypeName) -> list[Row]:
    return [Row(name, Bytes(8), Bytes(8)) for name in names]


def test_the_roster_includes_each_header_declaring_a_type_once(tmp_path: Path) -> None:
    """A header declaring a type is named as an include would name it; one declaring none is not."""
    (tmp_path / "aletheia").mkdir()
    declaring = tmp_path / "aletheia" / "client.hpp"
    _ = declaring.write_text(_HEADER, encoding="utf-8")
    bare = tmp_path / "aletheia" / "cli.hpp"
    _ = bare.write_text(
        "#pragma once\nnamespace aletheia {\nint run();\n} // namespace aletheia\n",
        encoding="utf-8",
    )
    assert roster(tmp_path, [bare, declaring]).includes == [IncludePath("aletheia/client.hpp")]


_ROSTER = Roster(
    [TypeName("aletheia::A"), TypeName("aletheia::B")], [IncludePath("aletheia/a.hpp")]
)


def test_a_record_matching_the_roster_the_version_and_the_list_has_no_problem() -> None:
    """Every type recorded, no stale row, one version, the derived list: nothing to say."""
    record = Record(SoVersion(2), _rows(TypeName("aletheia::A"), TypeName("aletheia::B")))
    assert not problems(_ROSTER, record, SoVersion(2), roster_text(_ROSTER))


def test_a_public_type_the_record_lacks_is_refused() -> None:
    """A new public type is a layout change: the gate names it and what the change owes."""
    record = Record(SoVersion(2), _rows(TypeName("aletheia::A")))
    assert problems(_ROSTER, record, SoVersion(2), roster_text(_ROSTER)) == [
        Prose(
            "docs/CPP_LAYOUT.yaml has no row for aletheia::B: a new public type; run the C++ "
            + "layout test and paste the row it prints, then raise SOVERSION and carry the "
            + "breaking mark"
        )
    ]


def test_a_row_no_header_declares_is_refused() -> None:
    """A row whose type is gone is stale: the gate says to delete it."""
    record = Record(
        SoVersion(2),
        _rows(TypeName("aletheia::A"), TypeName("aletheia::B"), TypeName("aletheia::Gone")),
    )
    assert problems(_ROSTER, record, SoVersion(2), roster_text(_ROSTER)) == [
        Prose(
            "docs/CPP_LAYOUT.yaml names aletheia::Gone, which no public header declares: "
            + "delete its row"
        )
    ]


def test_a_record_version_other_than_cmakes_is_refused() -> None:
    """The record's soversion is the one CMake installs the library under."""
    record = Record(SoVersion(2), _rows(TypeName("aletheia::A"), TypeName("aletheia::B")))
    assert problems(_ROSTER, record, SoVersion(1), roster_text(_ROSTER)) == [
        Prose("docs/CPP_LAYOUT.yaml records soversion 2, and cpp/CMakeLists.txt sets SOVERSION 1")
    ]


def test_a_type_list_other_than_the_derived_one_is_refused() -> None:
    """The list the C++ test measures is the roster the gate derives, or it is refused."""
    record = Record(SoVersion(2), _rows(TypeName("aletheia::A"), TypeName("aletheia::B")))
    stale = roster_text(Roster([TypeName("aletheia::A")], _ROSTER.includes))
    assert problems(_ROSTER, record, SoVersion(2), stale) == [
        Prose(
            "cpp/tests/layout_roster.inc is not the roster the headers give: run "
            + "python/.venv/bin/python -m tools.check_cpp_layout --write-roster"
        )
    ]
    assert problems(_ROSTER, record, SoVersion(2), None)


def test_the_type_list_names_the_roster_twice_in_one_order() -> None:
    """The file includes the declaring headers, then lists the types, then their names, in order."""
    lines = str(roster_text(_ROSTER)).splitlines()
    assert [line for line in lines if not line.startswith("//")] == [
        "#include <aletheia/a.hpp>",
        "",
        "#include <array>",
        "#include <string_view>",
        "",
        "namespace {",
        "",
        "template<typename... T>",
        "struct TypeList {};",
        "",
        "using LayoutRoster = TypeList<",
        "    aletheia::A,",
        "    aletheia::B>;",
        "constexpr std::array k_layout_names{",
        '    std::string_view{"aletheia::A"},',
        '    std::string_view{"aletheia::B"},',
        "};",
        "",
        "} // namespace",
    ]


_WHERE = Prose("CPP_LAYOUT.yaml")


def test_the_record_reads_its_version_and_rows() -> None:
    """A record of an integer soversion and name, size and align rows reads back as written."""
    text = Prose("soversion: 3\ntypes:\n  - name: aletheia::A\n    size: 16\n    align: 8\n")
    assert parse_record(text, _WHERE) == Record(
        SoVersion(3), [Row(TypeName("aletheia::A"), Bytes(16), Bytes(8))]
    )


_LACKING = "CPP_LAYOUT.yaml lacks a soversion, a types list or a row's name, size and align: "
_UNSHAPED = "CPP_LAYOUT.yaml: a row is not a name, a size and an alignment: "


def test_a_record_without_a_version_or_with_a_malformed_row_is_refused() -> None:
    """The reader says why: no soversion, one that is not an integer, or a row not shaped."""
    assert parse_record(Prose("types: []\n"), _WHERE) == Prose(_LACKING + "'soversion'")
    assert parse_record(Prose("soversion: true\ntypes: []\n"), _WHERE) == Prose(
        "CPP_LAYOUT.yaml does not carry an integer soversion"
    )
    unsized = Prose("soversion: 2\ntypes:\n  - name: aletheia::A\n")
    assert parse_record(unsized, _WHERE) == Prose(_LACKING + "'size'")
    quoted = Prose("soversion: 2\ntypes:\n  - name: aletheia::A\n    size: '8'\n    align: 8\n")
    assert parse_record(quoted, _WHERE) == Prose(
        _UNSHAPED + "Row(name='aletheia::A', size='8', align=8)"
    )
    numbered = Prose("soversion: 2\ntypes:\n  - name: 5\n    size: 8\n    align: 8\n")
    assert parse_record(numbered, _WHERE) == Prose(_UNSHAPED + "Row(name=5, size=8, align=8)")


def test_cmake_soversion_is_read_from_the_set_target_properties_line() -> None:
    """The version CMake sets is read; a file setting none is refused."""
    where = Prose("CMakeLists.txt")
    text = Prose("set_target_properties(x PROPERTIES\n    SOVERSION 7\n    VERSION 1)\n")
    assert parse_soversion(text, where) == SoVersion(7)
    assert parse_soversion(Prose("project(x)\n"), where) == Prose(
        "CMakeLists.txt sets no SOVERSION"
    )


_BASE = Record(SoVersion(2), [Row(TypeName("aletheia::A"), Bytes(8), Bytes(8))])
_MOVED = [Row(TypeName("aletheia::A"), Bytes(16), Bytes(8))]


def test_a_layout_change_under_a_raised_soversion_passes() -> None:
    """Rows that moved under a soversion above the base's are what the rule asks."""
    assert not bump_problems(_BASE, Record(SoVersion(3), _MOVED))


def test_a_layout_change_without_a_raised_soversion_is_refused() -> None:
    """Rows that moved under the base's soversion are a change no linked program sees coming."""
    assert bump_problems(_BASE, Record(SoVersion(2), _MOVED)) == [
        Prose(
            "docs/CPP_LAYOUT.yaml's rows differ from the base's, and its soversion 2 is not "
            + "above the base's 2: raise SOVERSION in cpp/CMakeLists.txt and in the record, "
            + "and carry the breaking mark"
        )
    ]


def test_a_soversion_raised_with_no_row_changed_passes() -> None:
    """A break the record cannot see, a virtual function added, raises the version on its own."""
    assert not bump_problems(_BASE, Record(SoVersion(3), _BASE.rows))
    assert not bump_problems(_BASE, _BASE)


def test_a_lowered_soversion_is_refused() -> None:
    """A version is never reused, so a record whose version falls is refused, rows moved or not."""
    refusal = [
        Prose(
            "docs/CPP_LAYOUT.yaml's soversion falls from 2 to 1: a SOVERSION is never "
            + "reused, so it only rises"
        )
    ]
    assert bump_problems(_BASE, Record(SoVersion(1), _BASE.rows)) == refusal
    assert bump_problems(Record(SoVersion(2), _MOVED), Record(SoVersion(1), _BASE.rows))


def test_a_first_record_is_held_above_the_base_cmake_soversion() -> None:
    """Where the base has no record, every row is new and the version must pass CMake's."""
    assert not bump_problems(SoVersion(1), Record(SoVersion(2), _MOVED))
    assert bump_problems(SoVersion(1), Record(SoVersion(1), _MOVED))
