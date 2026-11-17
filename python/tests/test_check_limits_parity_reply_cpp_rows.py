# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate names at each C++ place what its row's code reads amiss.

Each row of ``CPP_REPLY_TEXT`` holds the reader's code to one shape: a dispatch
reads its key once, with ``field_word``, and compares the word with ``==`` to
literals only, a ``field_word`` call names a literal key and
braced literal words, a table opens ``constexpr auto NAME = std::to_array<...>({``
and holds one ``{word, enumerator}`` a line, read only by its ``field_member``
calls, and one function gives each enumerator of the reply
status its word, a ``case`` of it reached nowhere else.  A set of plants breaks
one rule at each of several places, and the gate names, at each place, the rule
its code breaks; a reader
file comparing a word outside the dispatches, or looking up a table no reader
file declares, is named at its line, and a literal the compiler reads as no
word compares none there, while a dispatch's arm reads its literal's text
whatever its shape.  The cases of one set share its parse.
"""

from __future__ import annotations

import pytest
from _cpp_reply_gate import (
    Plant,
    after_signal_name,
    gate_report,
    named_at,
    planted_line,
    unparsed,
    unplaced,
)

from tools._reply_places import CppText, ReplyPlace, ReplyWord
from tools._reply_places_cpp import CPP_PARSE, CPP_PARSE_DBC, CPP_REPLY_SHAPE

from aletheia.common_types import Prose

_IN_DBC = "cpp/src/json_parse_dbc.cpp:"
_IN_JSON = "cpp/src/json_parse.cpp:"
_IN_SHAPE = "cpp/src/reply_shape.cpp:"
_TARGET_READ = CppText('"nodeMsg", "nodeSig"});\n')
_CLOSED = CppText('{"big_endian", ByteOrder::BigEndian}});')
_PRESENCE_CALL = CppText('field_word(j, path, "presence", {"always", "multiplexed"})')
_PRESENCE_HELD = CppText(
    f"auto const presence = {_PRESENCE_CALL};\n" + '    if (presence == "always")'
)
_BYTE_ORDER_READ = CppText(
    'auto const byte_order = field_member(j, path, "byteOrder", byte_order_table);'
)
_LOOKUP_LINE = CppText(
    'lookup(byte_order_table, field_string(j, path, "byteOrder")).value_or(ByteOrder::BigEndian);'
)
_COMMENT_CALL = CppText(
    'field_word(m, path, "kind", {"network", "node", "message", "signal", "envVar"})'
)
_COMMENT_HELD = CppText(f"auto const kind =\n        {_COMMENT_CALL};\n")
_ATTRIBUTE_CALL = CppText('field_word(m, path, "kind", {"definition", "default", "assignment"});')
_REDECLARED = CppText("auto status_word(ReplyStatus status) -> std::string_view;")
_SIZED = CppText("static_assert(byte_order_table.size() == 2);")
_SCOPE_SIZED = CppText("static_assert(attr_scope_table.size() == 7);")
_NAMED_X = CppText('if (name == "x") {}')
_CAST_ENTRY = CppText('{"little_endian", static_cast<ByteOrder>(0)},')
_UNREAD_WORD = CppText('{"h\\x80lds", Verdict::Holds},')
_IF = CppText("#if 1")
_ERROR_ENTRY = CppText('    {"error", IssueSeverity::Error},\n')
_SPELLED = CppText("auto const spelled = status_word(want);")

# Plants in the DBC reader breaking a dispatch's or a table's rule at each place.
_DBC_RULES = (
    Plant(
        CPP_PARSE_DBC,
        CppText('auto multiplexor = field_string(j, path, "multiplexor");'),
        CppText(f"auto multiplexor = std::string{{{_PRESENCE_CALL}}};"),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "message")\n        return DbcCommentTargetMessage'),
        CppText('if (kind != "message")\n        return DbcCommentTargetMessage'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText(f"auto const kind = {_ATTRIBUTE_CALL}"),
        CppText(f"auto kind = {_ATTRIBUTE_CALL}"),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "float")\n        return DbcAttrTypeFloat'),
        CppText('if (kind == "int")\n        return DbcAttrTypeFloat'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "enum")\n        return DbcAttrValueEnum'),
        CppText('if (kind.empty() || kind == "enum")\n        return DbcAttrValueEnum'),
    ),
    Plant(
        CPP_PARSE_DBC, _BYTE_ORDER_READ, CppText(f"auto const byte_order =\n        {_LOOKUP_LINE}")
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText("std::to_array<AttrScopeEntry>({"),
        CppText("std::to_array<AttrScopeEntry>(\n    {"),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "network")\n        return DbcAttrTargetNetwork{};'),
        CppText('if (kind == std::string_view{"network"})\n        return DbcAttrTargetNetwork{};'),
    ),
)

# More plants in the DBC reader, each breaking another rule at its place.
_DBC_MORE = (
    Plant(CPP_PARSE_DBC, _PRESENCE_HELD, CppText(f'if ({_PRESENCE_CALL} != "always")')),
    Plant(
        CPP_PARSE_DBC,
        _COMMENT_HELD,
        CppText(f"std::string_view const kind =\n        {_COMMENT_CALL};\n"),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('    {"big_endian", ByteOrder::BigEndian},\n});'),
        CppText("    " + _CLOSED),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "string")\n        return DbcAttrValueString'),
        CppText('if (kind == std::string("string"))\n        return DbcAttrValueString'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText(
            _TARGET_READ + '    if (kind == "network")\n        return DbcAttrTargetNetwork{};'
        ),
        CppText(
            _TARGET_READ
            + "    using namespace std::literals;\n"
            + '    if (kind == "network"sv)\n        return DbcAttrTargetNetwork{};'
        ),
    ),
)

# Plants in the DBC reader's tables: a reference outside a field_member call, a
# word twice.
_DBC_TABLES = (
    Plant(
        CPP_PARSE_DBC,
        CppText('    {"big_endian", ByteOrder::BigEndian},\n});\n'),
        CppText(
            '    {"big_endian", ByteOrder::BigEndian},\n});\n'
            + "/* The byte orders,\n   two. */\n"
            + f"{_SIZED} // both\n"
        ),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('{"node", DbcAttrScope::Node},'),
        CppText('{"network", DbcAttrScope::Node},'),
    ),
    Plant(CPP_PARSE_DBC, _PRESENCE_HELD, CppText(f"if ({_PRESENCE_CALL} == j.dump())")),
    after_signal_name(CppText(f"    {_NAMED_X}\n")),
)

# A plant in the DBC reader comparing a word with texts of no word, and with ab
# spelled through an escape; another reaching the scope table outside a
# field_member call.
_ESCAPED_WORD = CppText('if (name == "\\x61" "b") {}')
_DBC_SHAPES = (
    Plant(
        CPP_PARSE_DBC,
        CppText('    {"nodeSig", DbcAttrScope::NodeSig},\n});\n'),
        CppText('    {"nodeSig", DbcAttrScope::NodeSig},\n});\n' + f"{_SCOPE_SIZED}\n"),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('    auto name = field_string(j, path, "name");\n    auto const start_bit'),
        CppText(
            '    auto name = field_string(j, path, "name");\n'
            + '    if (name == "a-b") {}\n'
            + '    if (name != "-") {}\n'
            + '    if ("" == name) {}\n'
            + '    if (name == "1a") {}\n'
            + '    if (name == std::string("a-b")) {}\n'
            + f"    {_ESCAPED_WORD}\n"
            + "    auto const start_bit"
        ),
    ),
)

# Plants in the DBC reader comparing two dispatches' words with a text of no word.
_DBC_UNSHAPED = (
    Plant(
        CPP_PARSE_DBC,
        _PRESENCE_HELD,
        CppText('if (field_word(j, path, "presence", {"al-ways", "multiplexed"}) == "al-ways")'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText(f'{_COMMENT_CALL};\n    if (kind == "network")'),
        CppText(
            'field_word(m, path, "kind", {"net-work", "node", "message", "signal", "envVar"});\n'
            + '    if (kind == "net-work")'
        ),
    ),
)

# A plant in the DBC reader's tables: an entry naming no enumerator.
_DBC_ENTRIES = (
    Plant(
        CPP_PARSE_DBC,
        CppText('{"little_endian", ByteOrder::LittleEndian},'),
        _CAST_ENTRY,
    ),
)

# Plants in the response reader breaking a field_word call's, a table's and the
# status's rules, and comparing words and looking up a table outside the rows.
_JSON_RULES = (
    Plant(
        CPP_PARSE,
        CppText('field_word(reply, root, "type", {"property_batch"});'),
        CppText('field_word((reply), root, "type", {"property_batch"});'),
    ),
    Plant(
        CPP_PARSE,
        CppText('field_word(r, path, "type", {"property"});'),
        CppText('field_word(r, path, "type", {});'),
    ),
    Plant(
        CPP_PARSE,
        CppText('field_word(w, path, "kind", {"uncached_atom"});'),
        CppText('field_word(w, path, std::string_view{"kind"}, {"uncached_atom"});'),
    ),
    Plant(
        CPP_PARSE,
        CppText('    {"unresolved", Verdict::Unresolved},\n});\n'),
        CppText(
            '    {"unresolved", Verdict::Unresolved},\n});\n'
            + "static_assert(verdict_table.size() == 3);\n"
        ),
    ),
    Plant(
        CPP_PARSE,
        CppText("    auto reply = read_reply(raw);\n"),
        CppText(
            "    auto reply = read_reply(raw);\n"
            + f"    {_REDECLARED}\n"
            + f"    {_SPELLED}\n"
            + "    using enum ReplyStatus;\n"
            + "    switch (want) {\n"
            + "    case Ack:\n"
            + "        break;\n"
            + "    default:\n"
            + "        break;\n"
            + "    }\n"
            + "    (void)spelled;\n"
        ),
    ),
    Plant(
        CPP_PARSE,
        CppText('    auto detail = field_string(issue, path, "detail");\n'),
        CppText(
            '    auto detail = field_string(issue, path, "detail");\n'
            + "    if (detail ==\n"
            + '        "x") {}\n'
            + '    if (detail == std::string("y")) {}\n'
            + "    if (detail\n"
            + '            .starts_with("z")) {}\n'
            + '    if (detail.compare("w") == 0) {}\n'
            + "    {\n"
            + "        using namespace std::literals;\n"
            + '        if (detail == "v"sv) {}\n'
            + "    }\n"
            + '    if (detail.data() == "t") {}\n'
            + '    if (detail=="u") {}\n'
            + '    if (detail.ends_with("e")) {}\n'
            + "    auto const dashes = [](std::string_view of) {\n"
            + "        return std::string(of.size(), '-');\n"
            + "    };\n"
            + '    if (detail == dashes("s")) {}\n'
        ),
    ),
    Plant(CPP_PARSE, _ERROR_ENTRY, CppText(f"{_IF}\n{_ERROR_ENTRY}#endif\n")),
    Plant(
        CPP_PARSE,
        CppText("    return lookup(error_code_table, s);"),
        CppText(
            "    constexpr auto local_codes = error_code_table;\n"
            + "    return lookup(local_codes, s);"
        ),
    ),
)

# More plants in the response reader, each breaking another rule at its place.
_JSON_MORE = (
    Plant(CPP_PARSE, CppText('{"holds", Verdict::Holds},'), _UNREAD_WORD),
    Plant(
        CPP_PARSE,
        CppText('field_word(reply, root, "type", {"property_batch"});'),
        CppText('field_word(reply, root, "kind", {"property_batch"});'),
    ),
    Plant(
        CPP_PARSE,
        CppText('field_word(r, path, "type", {"property"});'),
        CppText(
            'field_word(r, path, "type", std::initializer_list<std::string_view>{"property"});'
        ),
    ),
    Plant(
        CPP_PARSE,
        CppText('field_word(w, path, "kind", {"uncached_atom"});'),
        CppText('field_word(w, path, "kind", {"uncached_atom", std::string_view{"x"}});'),
    ),
    Plant(
        CPP_PARSE,
        CppText("static auto decode_reply("),
        CppText(
            "namespace other {\nenum class ReplyStatus : int { Ack };\n} // namespace other\n\n"
            + "static auto decode_reply("
        ),
    ),
    Plant(
        CPP_PARSE,
        CppText("    auto reply = read_reply(raw);\n"),
        CppText(
            "    auto reply = read_reply(raw);\n"
            + "    auto const severity_table = 0;\n"
            + "    (void)severity_table;\n"
        ),
    ),
)

# A plant in the status's words: a return that is not one literal.
_SHAPE_RETURN = (
    Plant(
        CPP_REPLY_SHAPE,
        CppText('        return "ack";'),
        CppText('        return std::string_view{"ack"};'),
    ),
)
# A plant in the status's words: a literal returned after the switch, in no case.
_SHAPE_EXIT = (
    Plant(
        CPP_REPLY_SHAPE,
        CppText('    throw std::logic_error("unnamed reply status");'),
        CppText('    return "unnamed";'),
    ),
)
# A plant in the status's words: one word given twice.
_SHAPE_TWICE = (
    Plant(
        CPP_REPLY_SHAPE,
        CppText('        return "complete";'),
        CppText('        return "success";'),
    ),
)
# A plant in the status's words: the function they are given in renamed.
_SHAPE_RENAMED = (
    Plant(
        CPP_REPLY_SHAPE,
        CppText("auto status_word(ReplyStatus status) -> std::string_view {"),
        CppText("auto status_word_elsewhere(ReplyStatus status) -> std::string_view {"),
    ),
)
# A plant in the status's words: a case of it returning no value, in a lambda.
_SHAPE_EMPTY = (
    Plant(
        CPP_REPLY_SHAPE,
        CppText("    switch (status) {"),
        CppText(
            "    [status] {\n"
            + "        switch (status) {\n"
            + "        case ReplyStatus::Ack:\n"
            + "            return;\n"
            + "        default:\n"
            + "            break;\n"
            + "        }\n"
            + "    }();\n"
            + "    switch (status) {"
        ),
    ),
)
# A plant in the status's words: each case naming the like-named enumerator of another enum.
_STATUS_MEMBERS = ("Success", "Validation", "Complete", "Ack", "Error")
_SHAPE_SHADOWED = (
    Plant(
        CPP_REPLY_SHAPE,
        CppText("    switch (status) {"),
        CppText(
            f"    enum class Shadow {{ {', '.join(_STATUS_MEMBERS)} }};\n"
            + "    switch (static_cast<Shadow>(status)) {"
        ),
    ),
    *(
        Plant(
            CPP_REPLY_SHAPE,
            CppText(f"    case ReplyStatus::{member}:"),
            CppText(f"    case Shadow::{member}:"),
        )
        for member in _STATUS_MEMBERS
    ),
)
# A plant in the response reader: a table's std::to_array given a call, its
# braced list passed through that call.
_PASSED = CppText(
    "constexpr auto verdict_table = std::to_array<VerdictEntry>(passed<VerdictEntry>({"
)
_JSON_PASSED = (
    Plant(
        CPP_PARSE,
        CppText("// The verdicts the kernel writes.\n"),
        CppText(
            "// The verdicts the kernel writes.\n"
            + "using VerdictEntry = std::pair<std::string_view, Verdict>;\n"
            + "template <typename T, std::size_t N>\n"
            + "constexpr auto passed(T (&&given)[N]) -> T (&&)[N] {\n"
            + "    return std::move(given);\n"
            + "}\n"
        ),
    ),
    Plant(
        CPP_PARSE,
        CppText("std::to_array<std::pair<std::string_view, Verdict>>({"),
        CppText("std::to_array<VerdictEntry>(passed<VerdictEntry>({"),
    ),
    Plant(
        CPP_PARSE,
        CppText('    {"unresolved", Verdict::Unresolved},\n});\n'),
        CppText('    {"unresolved", Verdict::Unresolved},\n}));\n'),
    ),
)


def _site(plants: tuple[Plant, ...], needle: CppText) -> Prose:
    """Return the line a needle of the planted response or DBC reader starts on, as named."""
    path = plants[0].path
    shown = "cpp/src/json_parse.cpp" if path == CPP_PARSE else "cpp/src/json_parse_dbc.cpp"
    return Prose(f"{shown}:{planted_line(plants, path, needle)}: {needle.strip()!r}")


_STATUS_REACHED = Prose(
    "; ".join(
        (
            f"{_site(_JSON_RULES, _REDECLARED)} reaches status_word outside field_status",
            f"{_site(_JSON_RULES, _SPELLED)} reaches status_word outside field_status",
            f"{_site(_JSON_RULES, CppText('case Ack:'))} switches on a ReplyStatus outside "
            + "status_word, which could give it a second word",
        )
    )
)

# Each case: its set of plants, a place, and what the gate names there.
_CASES = [
    pytest.param(
        _DBC_RULES,
        "dbc/messages/signals/presence",
        _IN_DBC + "read_presence: reads 'presence' with field_word 2 times, not once",
        id="a dispatch reading its key twice",
    ),
    pytest.param(
        _DBC_RULES,
        "dbc/comments/target/kind",
        _IN_DBC
        + "read_comment_target: compares a word other than the one at 'kind' with == to a literal",
        id="a dispatch comparing its word with !=",
    ),
    pytest.param(
        _DBC_RULES,
        "dbc/attributes/kind",
        _IN_DBC
        + "read_attribute: neither holds the word at 'kind' nor compares it where it reads it",
        id="a dispatch holding its word in a variable not written auto const",
    ),
    pytest.param(
        _DBC_RULES,
        "dbc/attributes/attrType/kind",
        _IN_DBC + "read_attr_type: compares the word with one literal twice",
        id="a dispatch comparing its word with one literal twice",
    ),
    pytest.param(
        _DBC_RULES,
        "dbc/attributes/value/kind",
        _IN_DBC + "read_attr_value: uses kind other than to compare it with a literal",
        id="a dispatch using its word other than in a comparison",
    ),
    pytest.param(
        _DBC_RULES,
        "dbc/messages/signals/byteOrder",
        f"{_site(_DBC_RULES, _LOOKUP_LINE)} reaches byte_order_table outside a field_member call; "
        + _IN_DBC
        + "byte_order_table: no field_member call reads it",
        id="a member table read by a lookup defaulting to its last entry",
    ),
    pytest.param(
        _DBC_RULES,
        "dbc/attributes/scope <definition>",
        _IN_DBC
        + "attr_scope_table: 'constexpr auto attr_scope_table = std::to_array<AttrScopeEntry>(' "
        + "opens no constexpr std::to_array table",
        id="a table whose braces open on the next line",
    ),
    pytest.param(
        _JSON_PASSED,
        "results/status <property>",
        _IN_JSON + f"verdict_table: {_PASSED!r} opens no constexpr std::to_array table",
        id="a table whose std::to_array is given a call, not a braced list",
    ),
    pytest.param(
        _DBC_RULES,
        "dbc/attributes/target/kind",
        _IN_DBC
        + "read_attr_target: compares a word other than the one at 'kind' with == to a literal",
        id="a dispatch comparing its word with a string_view of a literal",
    ),
    pytest.param(
        _DBC_MORE,
        "dbc/messages/signals/presence",
        _IN_DBC
        + "read_presence: neither holds the word at 'presence' nor compares it where it reads it",
        id="a dispatch comparing its read with != where it reads it",
    ),
    pytest.param(
        _DBC_MORE,
        "dbc/comments/target/kind",
        _IN_DBC
        + "read_comment_target: neither holds the word at 'kind' nor compares it where it reads it",
        id="a dispatch holding its word in a std::string_view const",
    ),
    pytest.param(
        _DBC_MORE,
        "dbc/messages/signals/byteOrder",
        _IN_DBC
        + f"byte_order_table:{planted_line(_DBC_MORE, CPP_PARSE_DBC, _CLOSED)}: "
        + f"{_CLOSED!r} is not one {{word, enumerator}}",
        id="a table closing on its last entry's line",
    ),
    pytest.param(
        _DBC_MORE,
        "dbc/attributes/value/kind",
        _IN_DBC
        + "read_attr_value: compares a word other than the one at 'kind' with == to a literal",
        id="a dispatch comparing its word with a string made of a literal",
    ),
    pytest.param(
        _DBC_MORE,
        "dbc/attributes/target/kind",
        _IN_DBC
        + "read_attr_target: compares a word other than the one at 'kind' with == to a literal",
        id="a dispatch comparing its word with a literal given a suffix",
    ),
    pytest.param(
        _DBC_TABLES,
        "dbc/messages/signals/byteOrder",
        f"{_site(_DBC_TABLES, _SIZED)}" + " reaches byte_order_table outside a field_member call",
        id="a member table reached outside a field_member call beside comments",
    ),
    pytest.param(
        _DBC_SHAPES,
        "dbc/attributes/scope <definition>",
        f"{_site(_DBC_SHAPES, _SCOPE_SIZED)} reaches attr_scope_table outside a field_member call",
        id="a member table reached outside a field_member call after its declaration",
    ),
    pytest.param(
        _DBC_TABLES,
        "dbc/attributes/scope <definition>",
        _IN_DBC + "attr_scope_table: the table is empty or names a word twice",
        id="a table naming a word twice",
    ),
    pytest.param(
        _JSON_RULES,
        "type",
        _IN_JSON + "parse_frame_response: a field_word call holds a call of its own",
        id="a field_word call holding parentheses",
    ),
    pytest.param(
        _JSON_RULES,
        "results/type",
        _IN_JSON + 'read_verdict: field_word(r, path, "type", {}) names no literal key or no words',
        id="a field_word call awaiting no word",
    ),
    pytest.param(
        _JSON_RULES,
        "warnings/kind",
        _IN_JSON
        + 'read_stream_warning: field_word(w, path, std::string_view{"kind"}, {"uncached_atom"})'
        + " names no literal key or no words",
        id="a field_word call naming its key in a string_view",
    ),
    pytest.param(
        _JSON_RULES,
        "results/status <property>",
        f"{_site(_JSON_RULES, CppText('static_assert(verdict_table.size() == 3);'))}"
        + " reaches verdict_table outside a field_member call",
        id="a member table reached outside a field_member call",
    ),
    pytest.param(
        _JSON_RULES,
        "status",
        _STATUS_REACHED,
        id="the status's word reached and its enum switched on outside status_word",
    ),
    pytest.param(
        _JSON_MORE,
        "type",
        _IN_JSON + "parse_frame_response: no field_word call at 'type'",
        id="a function's field_word call at another key",
    ),
    pytest.param(
        _JSON_MORE,
        "results/type",
        _IN_JSON
        + 'read_verdict: field_word(r, path, "type", '
        + 'std::initializer_list<std::string_view>{"property"}) names no literal key or no words',
        id="a field_word call awaiting words made a list",
    ),
    pytest.param(
        _JSON_MORE,
        "warnings/kind",
        _IN_JSON
        + 'read_stream_warning: field_word(w, path, "kind", '
        + '{"uncached_atom", std::string_view{"x"}}) awaits a word that is not a literal',
        id="a field_word call awaiting a word not a literal",
    ),
    pytest.param(
        _JSON_MORE,
        "status",
        "ReplyStatus is not defined once, in cpp/src/detail/reply_shape.hpp",
        id="the status's enum defined twice",
    ),
    pytest.param(
        _JSON_MORE,
        "issues/severity",
        _IN_JSON + "severity_table: given a value 2 times in the library, not once",
        id="a member table's name given a value twice",
    ),
    pytest.param(
        _SHAPE_RETURN,
        "status",
        _IN_SHAPE + "status_word: a case or a return is not one enumerator returning one literal",
        id="the status's word returned not as a literal",
    ),
    pytest.param(
        _SHAPE_EXIT,
        "status",
        _IN_SHAPE + "status_word: a case or a return is not one enumerator returning one literal",
        id="the status's word returned outside its cases",
    ),
    pytest.param(
        _SHAPE_TWICE,
        "status",
        _IN_SHAPE
        + "status_word: its cases do not give each enumerator of ReplyStatus its own word",
        id="the status's word given two enumerators",
    ),
    pytest.param(
        _SHAPE_RENAMED,
        "status",
        _IN_SHAPE + "status_word is not defined",
        id="the status's words given in a function of another name",
    ),
    pytest.param(
        _SHAPE_EMPTY,
        "status",
        _IN_SHAPE + "status_word: a case or a return is not one enumerator returning one literal",
        id="a case of the status's words returning no value",
    ),
    pytest.param(
        _SHAPE_SHADOWED,
        "status",
        _IN_SHAPE + "status_word: a case or a return is not one enumerator returning one literal",
        id="the status's words given to the like-named enumerators of another enum",
    ),
    pytest.param(
        _DBC_TABLES,
        "dbc/messages/signals/presence",
        _IN_DBC
        + "read_presence: neither holds the word at 'presence' nor compares it where it reads it",
        id="a dispatch comparing its read with no literal",
    ),
    pytest.param(
        _DBC_ENTRIES,
        "dbc/messages/signals/byteOrder",
        _IN_DBC
        + f"byte_order_table:{planted_line(_DBC_ENTRIES, CPP_PARSE_DBC, _CAST_ENTRY)}: "
        + f"{_CAST_ENTRY!r} is not one {{word, enumerator}}",
        id="a table entry naming no enumerator",
    ),
    pytest.param(
        _JSON_RULES,
        "issues/severity",
        _IN_JSON
        + f"severity_table:{planted_line(_JSON_RULES, CPP_PARSE, _IF)}: "
        + f"{_IF!r} is not one {{word, enumerator}}",
        id="a table line holding no entry",
    ),
    pytest.param(
        _JSON_MORE,
        "results/status <property>",
        _IN_JSON
        + f"verdict_table:{planted_line(_JSON_MORE, CPP_PARSE, _UNREAD_WORD)}: "
        + f"{_UNREAD_WORD!r} is not one {{word, enumerator}}",
        id="a table entry whose word the compiler reads as no text",
    ),
]


@pytest.mark.parametrize(("plants", "place", "named"), _CASES)
def test_the_gate_names_at_each_place_the_rule_its_code_breaks(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...], place: ReplyPlace, named: Prose
) -> None:
    """With ``plants`` in the C++ library, the gate names ``named`` at ``place``, alone."""
    found = gate_report(monkeypatch, plants)
    assert unparsed(found) == []
    assert named_at(found, place) == [named]


_OUTSIDE = "compares a word outside the dispatches CPP_REPLY_TEXT names"


def _outside(plants: tuple[Plant, ...], lines: tuple[CppText, ...]) -> list[Prose]:
    """Return how the gate names each of ``lines`` comparing a word outside the dispatches."""
    return [Prose(f"{_site(plants, line)} {_OUTSIDE}") for line in lines]


_JSON_COMPARED = (
    CppText("if (detail ==\n"),
    CppText('if (detail == std::string("y")) {}'),
    CppText('.starts_with("z")) {}'),
    CppText('if (detail.compare("w") == 0) {}'),
    CppText('if (detail == "v"sv) {}'),
    CppText('if (detail.data() == "t") {}'),
    CppText('if (detail=="u") {}'),
    CppText('if (detail.ends_with("e")) {}'),
)
_LOOKED = planted_line(_JSON_RULES, CPP_PARSE, CppText("return lookup(local_codes, s);"))


@pytest.mark.parametrize(
    ("plants", "named"),
    [
        pytest.param(
            _JSON_RULES,
            [
                *_outside(_JSON_RULES, _JSON_COMPARED),
                Prose(
                    f"{_IN_JSON}{_LOOKED}: looks up local_codes, a table no reader file declares"
                ),
            ],
            id="the response reader",
        ),
        pytest.param(_DBC_TABLES, _outside(_DBC_TABLES, (_NAMED_X,)), id="the DBC reader"),
        pytest.param(
            _DBC_SHAPES,
            _outside(_DBC_SHAPES, (_ESCAPED_WORD,)),
            id="the DBC reader comparing texts of no word",
        ),
    ],
)
def test_a_reader_file_comparing_a_word_or_looking_up_a_table_outside_the_rows_is_named(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...], named: list[Prose]
) -> None:
    """Each comparison of a word outside the dispatches, and each undeclared lookup, at its line.

    A comparison is named at its operator, or at the name a search calls, a line
    break before the literal or after the object notwithstanding.  A word compared
    with what a call of an operator other than a literal's returns is not named,
    nor a comparison with ``==`` or ``!=`` whose literal the compiler reads as no word.
    """
    assert unplaced(gate_report(monkeypatch, plants)) == named


@pytest.mark.parametrize(
    ("place", "read", "written"),
    [
        pytest.param(
            "dbc/messages/signals/presence", "al-ways", "always", id="compared where it is read"
        ),
        pytest.param("dbc/comments/target/kind", "net-work", "network", id="held in a variable"),
    ],
)
def test_a_dispatch_reads_the_text_of_a_literal_of_no_word_its_word_is_compared_with(
    monkeypatch: pytest.MonkeyPatch, place: ReplyPlace, read: ReplyWord, written: ReplyWord
) -> None:
    """A dispatch's arm reads its literal's text whatever its shape, held to the row as any arm."""
    assert named_at(gate_report(monkeypatch, _DBC_UNSHAPED), place) == [
        Prose(f"'{read}' is in the C++ reader only"),
        Prose(f"'{written}' is in replyText only"),
    ]
