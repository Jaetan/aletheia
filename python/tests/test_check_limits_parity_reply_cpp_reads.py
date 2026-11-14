# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads the C++ library as clang-23 compiles it, or names where it cannot.

libclang reads each literal through its escapes, its raw form, its prefix and
its suffix and joins adjacent ones, reads a comparison with its literal on
either side, reads a call whatever its arguments' own calls, a function at its
definition whatever declares it first, and a header's code in that header
wherever it is included, so code written any of those ways reads in parity; a
line the compiler refuses is named at its file and line with its own text,
whatever line ends the file uses, once however many files include it, and ends
the gate with exit 2.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

import pytest
from _cpp_reply_gate import (
    UNPARSED,
    Plant,
    gate_report,
    named_at,
    plant_library,
    planted_line,
    unparsed,
)

from tools import check_limits_parity
from tools._reply_places import CppText, LiteralText, ReplyPlace
from tools._reply_places_cpp import (
    CPP_PARSE,
    CPP_PARSE_DBC,
    CPP_REPLY_SHAPE,
    CPP_REPLY_SHAPE_HEADER,
)
from tools._reply_places_cpp_tree import string_text

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

# The DBC reader written as the cursors read it in parity: a literal on the
# left, escaped, joined, raw, awaited raw, and a read held with no space after
# its `=`.
_DBC_READ = (
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "network")\n        return DbcAttrTargetNetwork{};'),
        CppText('if ("network" == kind)\n        return DbcAttrTargetNetwork{};'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('{"little_endian", ByteOrder::LittleEndian},'),
        CppText('{"little\\x5f" "endian", ByteOrder::LittleEndian},'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('"kind", {"network", "node", "message", "signal", "envVar"})'),
        CppText('"k\\u0069nd", {"network", "node", "message", "signal", "envVar"})'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "string")\n        return DbcAttrValueString'),
        CppText('if (kind == R"(string)")\n        return DbcAttrValueString'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText(
            'auto const presence = field_word(j, path, "presence", {"always", "multiplexed"});\n'
            + '    if (presence == "always")'
        ),
        CppText('if ("always" == field_word(j, path, "presence", {"always", "multiplexed"}))'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('"enum", "hex"});\n    if (kind == "int")\n        return DbcAttrTypeInt'),
        CppText('"enum", R"(hex)"});\n    if (kind == "int")\n        return DbcAttrTypeInt'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText("DbcAttrTarget {\n    auto const kind = field_word("),
        CppText("DbcAttrTarget {\n    auto const kind =field_word("),
    ),
)

# The response reader written as the cursors read it in parity: an unscoped
# enum of the status's name, escaped and joined words, a last entry with no
# comma, a table's specifiers, a comment line in a table, and a field_member
# call whose object is a call.
_JSON_READ = (
    Plant(
        CPP_PARSE,
        CppText("static auto decode_reply("),
        CppText(
            "namespace other {\nenum ReplyStatus : int { Lone };\n} // namespace other\n\n"
            + "static auto decode_reply("
        ),
    ),
    Plant(
        CPP_PARSE,
        CppText('field_word(w, path, "kind", {"uncached_atom"});'),
        CppText('field_word(w, path, "k\\151nd", {"uncached\\x5f" "atom"});'),
    ),
    Plant(
        CPP_PARSE,
        CppText('    {"unresolved", Verdict::Unresolved},\n});'),
        CppText('    {"unresolved", Verdict::Unresolved}\n});'),
    ),
    Plant(
        CPP_PARSE,
        CppText("constexpr auto severity_table = "),
        CppText("static inline constexpr auto severity_table = "),
    ),
    Plant(
        CPP_PARSE,
        CppText('    {"error", IssueSeverity::Error},\n'),
        CppText('    // the grave one\n    {"error", IssueSeverity::Error},\n'),
    ),
    Plant(
        CPP_PARSE,
        CppText('field_member(issue, path, "severity", severity_table)'),
        CppText('field_member(read_object(issue, path), path, "severity", severity_table)'),
    ),
)

# The status's words with one returned escaped.
_SHAPE_READ = (
    Plant(CPP_REPLY_SHAPE, CppText('        return "ack";'), CppText('        return "a\\143k";')),
)

# A dispatch declared before its definition, which the gate reads at its definition.
_VERDICT = "static auto read_verdict(Json const& r, ReplyPath const& path) -> PropertyResult"
_DECLARED_FIRST = (
    Plant(CPP_PARSE, CppText(f"{_VERDICT} {{"), CppText(f"{_VERDICT};\n{_VERDICT} {{")),
)

# A function of the status word's name declared at the header's top level, which
# the gate reads in the header, not in each file including it.
_CLOSED = CppText("} // namespace aletheia::detail")
_AT_TOP = (
    Plant(CPP_REPLY_SHAPE_HEADER, _CLOSED, CppText(f"{_CLOSED}\n\nauto status_word() -> int;")),
)

# The status's header included inside a block, which the gate reads in the
# header, not as the including file's code.
_INCLUDE = CppText('#include "detail/reply_shape.hpp"\n')
_IN_BLOCK = (Plant(CPP_PARSE, _INCLUDE, CppText(f'extern "C++" {{\n{_INCLUDE}}}\n')),)


@pytest.mark.parametrize(
    "plants",
    [
        pytest.param(_DBC_READ, id="the DBC reader"),
        pytest.param(_JSON_READ, id="the response reader"),
        pytest.param(_SHAPE_READ, id="the status's words"),
        pytest.param(_DECLARED_FIRST, id="a dispatch declared before its definition"),
        pytest.param(_AT_TOP, id="the status's header declaring its word's name at top level"),
        pytest.param(_IN_BLOCK, id="the status's header included inside a block"),
    ],
)
def test_code_the_compiler_reads_as_written_reads_in_parity(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...]
) -> None:
    """With ``plants``, which change how the code is written, not what it reads, every row holds.

    The bound kinds aside, which the gate reads from ``limits.hpp`` and this case
    gives none.
    """
    bound_kinds = "reply place bound_kind: "
    found = gate_report(monkeypatch, plants)
    assert [each for each in found if not each.startswith(bound_kinds)] == []


_BROKEN = CppText("int broken = ;")
_IN_DBC = (
    Plant(
        CPP_PARSE_DBC,
        CppText("static auto read_node(Json const& n, ReplyPath const& path) -> DbcNode {"),
        CppText(
            "static auto read_node(Json const& n, ReplyPath const& path) -> DbcNode {\n    "
            + _BROKEN
        ),
    ),
)
_STATUS_ENUM = CppText(
    "enum class ReplyStatus : std::uint8_t { Success, Validation, Complete, Ack, Error };"
)
_IN_HEADER = (Plant(CPP_REPLY_SHAPE_HEADER, _STATUS_ENUM, CppText(f"{_STATUS_ENUM}\n{_BROKEN}")),)


def _refused(plants: tuple[Plant, ...], shown: Prose) -> Prose:
    """Return how the gate names the broken line ``plants`` write in their file."""
    line = planted_line(plants, plants[0].path, _BROKEN)
    return Prose(f"{shown}:{line}: {_BROKEN!r} {UNPARSED}: expected expression")


def test_a_line_the_compiler_refuses_is_named_at_its_file_and_line(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A line of the DBC reader clang-23 refuses is named there, with the compiler's message."""
    found = unparsed(gate_report(monkeypatch, _IN_DBC))
    assert found == [_refused(_IN_DBC, Prose("cpp/src/json_parse_dbc.cpp"))]


def test_a_header_line_the_compiler_refuses_is_named_once(monkeypatch: pytest.MonkeyPatch) -> None:
    """A refused line of a header every parsed file includes is named once, in the header."""
    found = unparsed(gate_report(monkeypatch, _IN_HEADER))
    assert found == [_refused(_IN_HEADER, Prose("cpp/src/detail/reply_shape.hpp"))]


# The line ends clang-23 reads besides a line feed: a bare carriage return, a
# carriage return and a line feed ending one line, and a carriage return inside a
# comment.  Each bare one ends a line a count of line feeds misses.
_ENDS = CppText("\r\r\n/* a\r*/\r")
_BARE = len(re.findall(r"\r(?!\n)", _ENDS))
_READ_NODE = CppText("static auto read_node(Json const& n, ReplyPath const& path) -> DbcNode {")
_REFUSED_AFTER_ENDS = (
    Plant(CPP_PARSE_DBC, _READ_NODE, CppText(f"{_ENDS}{_READ_NODE}\n    {_BROKEN}")),
)


def test_a_refused_line_after_carriage_returns_is_named_with_its_own_text(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A refused line after line ends of every kind is named at its line, with its own text."""
    found = unparsed(gate_report(monkeypatch, _REFUSED_AFTER_ENDS))
    line = planted_line(_REFUSED_AFTER_ENDS, CPP_PARSE_DBC, _BROKEN) + _BARE
    assert found == [
        Prose(f"cpp/src/json_parse_dbc.cpp:{line}: {_BROKEN!r} {UNPARSED}: expected expression")
    ]


def test_a_refused_line_of_a_header_read_from_disk_is_named_with_its_own_text(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A refused line of a header read from disk after commented CR LF lines keeps its text."""
    header = tmp_path / "ends.hpp"
    header.write_bytes(f"/* a */\r\n/* b */\r\n/* c */ {_BROKEN}\r\n".encode())
    plants = (Plant(CPP_PARSE_DBC, _READ_NODE, CppText(f'#include "{header}"\n{_READ_NODE}')),)
    found = unparsed(gate_report(monkeypatch, plants))
    assert found == [Prose(f"{header}:3: {_BROKEN!r} {UNPARSED}: expected expression")]


_READ_ISSUE = CppText(
    "static auto read_issue(Json const& issue, ReplyPath const& path) -> ValidationIssue {"
)
_SEVERITY_READ = CppText('field_member(issue, path, "severity", severity_table)')
_LOOKED_UP = CppText(
    'lookup(severity_table, field_string(issue, path, "severity"))'
    + ".value_or(IssueSeverity::Warning)"
)
_READ_AFTER_ENDS = (
    Plant(CPP_PARSE, _READ_ISSUE, CppText(f"{_ENDS}{_READ_ISSUE}")),
    Plant(CPP_PARSE, _SEVERITY_READ, _LOOKED_UP),
)


def test_a_table_read_after_carriage_returns_is_named_at_its_line_with_its_text(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A table read the gate refuses after line ends of every kind is named at its line."""
    found = named_at(gate_report(monkeypatch, _READ_AFTER_ENDS), ReplyPlace("issues/severity"))
    line = planted_line(_READ_AFTER_ENDS, CPP_PARSE, _LOOKED_UP) + _BARE
    shown = CppText(f"auto const severity = {_LOOKED_UP};")
    assert found == [
        Prose(
            f"cpp/src/json_parse.cpp:{line}: {shown!r} reaches severity_table outside a "
            + "field_member call; "
            + "cpp/src/json_parse.cpp:severity_table: no field_member call reads it"
        )
    ]


# The DBC reader with more refused lines than libclang reports before it stops.
_PAST_LIMIT = (
    Plant(
        _IN_DBC[0].path, _IN_DBC[0].written, CppText(_IN_DBC[0].planted + f"\n    {_BROKEN}" * 20)
    ),
)


def test_the_compilers_stop_standing_in_no_file_is_named_at_the_files_first_line(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The stop after too many errors, in no file, is named at the parsed file's first line."""
    stop = Prose("too many errors emitted, stopping now")
    found = unparsed(gate_report(monkeypatch, _PAST_LIMIT))
    # The file's first line is a comment, which the gate shows blanked.
    assert [each for each in found if each.endswith(stop)] == [
        Prose(f"cpp/src/json_parse_dbc.cpp:1: '' {UNPARSED}: {stop}")
    ]


def test_a_line_the_compiler_refuses_ends_the_gate_with_exit_2(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The gate names the refused line among what it cannot read, and exits 2."""
    plant_library(monkeypatch, _IN_DBC)
    monkeypatch.setattr("sys.argv", ["check_limits_parity"])
    assert check_limits_parity.main() == 2
    refused = _refused(_IN_DBC, Prose("cpp/src/json_parse_dbc.cpp"))
    assert f"check-limits-parity: {refused}\n" in capsys.readouterr().err


# Each string literal token and the text the compiler reads it as, None for none.
_LITERALS = [
    (CppText(written), None if read is None else LiteralText(read))
    for written, read in (
        ('"word"', "word"),
        ('"\\\' \\" \\? \\\\"', "' \" ? \\"),
        ('"\\a\\b\\f\\n\\r\\t\\v"', "\a\b\f\n\r\t\v"),
        ('"\\101"', "A"),
        ('"\\1010"', "A0"),
        ('"\\7"', "\x07"),
        ('"\\177"', "\x7f"),
        ('"\\200"', None),
        ('"\\o{101}"', "A"),
        ('"\\x41"', "A"),
        ('"\\x{41}"', "A"),
        ('"\\x7f"', "\x7f"),
        ('"\\x80"', None),
        ('"\\u0041"', "A"),
        ('"\\u{41}"', "A"),
        ('"\\U00000041"', "A"),
        ('"\\uD800"', None),
        ('"\\N{LATIN SMALL LETTER A}"', "a"),
        ('"\\N{NO SUCH CHARACTER}"', None),
        ('"\\q"', None),
        ('R"(a\\nb)"', "a\\nb"),
        ('R"d(x)")d"', 'x)"'),
        ('u8"a"', "a"),
        ('u"a"', "a"),
        ('U"a"', "a"),
        ('L"a"', "a"),
        ('LR"(a)"', "a"),
        ('"a"sv', "a"),
        ('R"(a)"sv', "a"),
        ("'a'", None),
        ("word", None),
    )
]


@pytest.mark.parametrize(("written", "read"), _LITERALS, ids=[each for each, _ in _LITERALS])
def test_a_string_literal_reads_as_the_compiler_reads_it(
    written: CppText, read: LiteralText | None
) -> None:
    """``written`` reads as ``read``, or as none when the compiler names no character for it."""
    assert string_text(written) == read
