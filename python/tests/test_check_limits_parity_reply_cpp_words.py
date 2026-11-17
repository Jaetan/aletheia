# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads a C++ word place from a ``field_word`` call and the tests mapping it.

``read_presence`` reads a signal's presence with ``field_word``, which refuses
every other word, holds it in ``auto const`` and maps it through tests of it
with ``==`` against literals, each the condition of an ``if`` returning one
value built as ``NAME{...}``, the last statement returning the last arm's: the
call's words are the C++ reader's set at the place, each test names one of
them, and the last arm reads the awaited words no test names and the words of
the tests building its type, which must be one word, the row's last, or none.
A word added to the call or dropped from it, a test naming a word the call
refuses, a last arm sharing a test's type, the word read with ``field_string``,
not held, used outside its tests or compared outside an ``if``'s condition, and
a test or a return the gate cannot read as one value are each named at the place.
``read_comment_target`` reads a comment target's kind alike, ``read_attribute``
an attribute's kind, ``read_attr_type`` a definition's type kind,
``read_attr_value`` an attribute value's kind and ``read_attr_target`` an
attribute target's kind, and each is held alike.
"""

from __future__ import annotations

import pytest
from _cpp_reply_gate import Plant, gate_report, named_at, unparsed

from tools._reply_places import CppText, ReplyPlace
from tools._reply_places_cpp import CPP_PARSE_DBC

from aletheia.common_types import Prose

_PRESENCE = ReplyPlace("dbc/messages/signals/presence")
_IN_PRESENCE = "cpp/src/json_parse_dbc.cpp:read_presence: "
_WORDS = CppText('{"always", "multiplexed"}')
_CALL = CppText(f'field_word(j, path, "presence", {_WORDS})')
_HELD = CppText(f"auto const presence = {_CALL};\n" + '    if (presence == "always")')
_ALWAYS = CppText("        return AlwaysPresent{};\n")
_LAST = CppText("    return Multiplexed{.multiplexor")
_LAST_END = CppText(".multiplex_values = std::move(values)};\n}")
_TESTS = "the tests of the word at 'presence'"
_COMMENT = ReplyPlace("dbc/comments/target/kind")
_IN_COMMENT = "cpp/src/json_parse_dbc.cpp:read_comment_target: "
_KINDS = CppText('{"network", "node", "message", "signal", "envVar"}')
_KIND_HELD = CppText(f'auto const kind =\n        field_word(m, path, "kind", {_KINDS});')
_ATTRIBUTE = ReplyPlace("dbc/attributes/kind")
_IN_ATTRIBUTE = "cpp/src/json_parse_dbc.cpp:read_attribute: "
_ATTRIBUTE_KINDS = CppText('{"definition", "default", "assignment"}')
_ATTRIBUTE_HELD = CppText(f'auto const kind = field_word(m, path, "kind", {_ATTRIBUTE_KINDS});')
_TYPE = ReplyPlace("dbc/attributes/attrType/kind")
_IN_TYPE = "cpp/src/json_parse_dbc.cpp:read_attr_type: "
_TYPE_HEAD = CppText('DbcAttrType {\n    auto const kind = field_word(m, path, "kind", ')
_TYPE_HELD = CppText(_TYPE_HEAD + '{"int", "float", "string", "enum", "hex"});')
_VALUE = ReplyPlace("dbc/attributes/value/kind")
_IN_VALUE = "cpp/src/json_parse_dbc.cpp:read_attr_value: "
_VALUE_HEAD = CppText('DbcAttrValue {\n    auto const kind = field_word(m, path, "kind", ')
_VALUE_HELD = CppText(_VALUE_HEAD + '{"int", "float", "string", "enum", "hex"});')
_TARGET = ReplyPlace("dbc/attributes/target/kind")
_IN_TARGET = "cpp/src/json_parse_dbc.cpp:read_attr_target: "
_TARGET_HEAD = CppText(
    'DbcAttrTarget {\n    auto const kind = field_word(\n        m, path, "kind", '
)
_TARGET_KINDS = CppText('{"network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig"}')
_TARGET_HELD = CppText(_TARGET_HEAD + _TARGET_KINDS + ");")


def _plant(written: CppText, planted: CppText, *more: CppText) -> tuple[Plant, ...]:
    """Return the plants writing ``written`` as ``planted``, and each pair after."""
    pairs = (written, planted, *more)
    return tuple(
        Plant(CPP_PARSE_DBC, old, new) for old, new in zip(pairs[::2], pairs[1::2], strict=True)
    )


# Each case: its plant, and what the gate names at the presence.
_CASES = [
    pytest.param(_plant(_HELD, _HELD), [], id="presence as written"),
    pytest.param(
        _plant(_HELD, CppText(f'if ({_CALL} == "always")')), [], id="presence compared where read"
    ),
    pytest.param(
        _plant(_WORDS, CppText('{"always"}')),
        [Prose("'multiplexed' is in replyText only")],
        id="multiplexed dropped from the call",
    ),
    pytest.param(
        _plant(_WORDS, CppText('{"always", "multiplexed", "sometimes"}')),
        [Prose(_IN_PRESENCE + f"the code after {_TESTS} reads 'multiplexed', 'sometimes' alike")],
        id="a word added to the call",
    ),
    pytest.param(
        _plant(
            _ALWAYS,
            CppText("        return Multiplexed{.multiplexor = SignalName{std::string{}}};\n"),
        ),
        [Prose(_IN_PRESENCE + f"the code after {_TESTS} reads 'always', 'multiplexed' alike")],
        id="the last arm building the type the always test builds",
    ),
    pytest.param(
        _plant(CppText('if (presence == "always")'), CppText('if (presence == "sometimes")')),
        [
            Prose(
                _IN_PRESENCE
                + f"{_TESTS} names 'sometimes', which no field_word call at 'presence' awaits"
            )
        ],
        id="a test naming a word the call refuses",
    ),
    pytest.param(
        _plant(_HELD, CppText('if (field_string(j, path, "presence") == "always")')),
        [Prose(_IN_PRESENCE + "no field_word call at 'presence'")],
        id="the word read with field_string",
    ),
    pytest.param(
        _plant(
            _HELD, CppText(f"{_CALL};\n" + '    if (field_string(j, path, "presence") == "always")')
        ),
        [
            Prose(
                _IN_PRESENCE
                + "neither holds the word at 'presence' nor compares it where it reads it"
            )
        ],
        id="the word not held",
    ),
    pytest.param(
        _plant(_ALWAYS, CppText(_ALWAYS + "    (void)presence;\n")),
        [Prose(_IN_PRESENCE + "uses presence other than to compare it with a literal")],
        id="the word used outside its tests",
    ),
    pytest.param(
        _plant(_ALWAYS, CppText(_ALWAYS + '    (void)(presence == "multiplexed");\n')),
        [Prose(_IN_PRESENCE + "compares the word other than as the condition of an if")],
        id="the word compared outside the condition of an if",
    ),
    pytest.param(
        _plant(
            _ALWAYS,
            CppText(
                "    {\n        auto always = AlwaysPresent{};\n        return always;\n    }\n"
            ),
        ),
        [Prose(_IN_PRESENCE + "the test of 'always' returns no one value built as NAME{...}")],
        id="a test returning a value it holds",
    ),
    pytest.param(
        _plant(
            _ALWAYS,
            CppText(
                _ALWAYS
                + "    else\n"
                + "        return Multiplexed{.multiplexor = SignalName{std::string{}}};\n"
            ),
        ),
        [Prose(_IN_PRESENCE + "the test of 'always' returns no one value built as NAME{...}")],
        id="a test with an else",
    ),
    pytest.param(
        _plant(
            _LAST,
            CppText("    SignalPresence const out = Multiplexed{.multiplexor"),
            _LAST_END,
            CppText(".multiplex_values = std::move(values)};\n    return out;\n}"),
        ),
        [Prose(_IN_PRESENCE + "its last statement returns no one value built as NAME{...}")],
        id="the last arm built outside the return",
    ),
    pytest.param(
        _plant(_ALWAYS, CppText(_ALWAYS + "    if (j.empty())\n        return AlwaysPresent{};\n")),
        [Prose(_IN_PRESENCE + "returns other than in its tests and its last statement")],
        id="a return outside the tests",
    ),
    pytest.param(_plant(_ALWAYS, CppText("    {\n" + _ALWAYS + "    }\n")), [], id="a test braced"),
    pytest.param(
        _plant(_ALWAYS, CppText("        return static_cast<SignalPresence>(AlwaysPresent{});\n")),
        [Prose(_IN_PRESENCE + "the test of 'always' returns no one value built as NAME{...}")],
        id="a test returning a cast",
    ),
    pytest.param(
        _plant(_ALWAYS, CppText("        return aletheia::AlwaysPresent{};\n")),
        [Prose(_IN_PRESENCE + "the test of 'always' returns no one value built as NAME{...}")],
        id="a test building a type named through its namespace",
    ),
]


@pytest.mark.parametrize(("plants", "named"), _CASES)
def test_the_gate_names_at_the_presence_what_its_tests_read_amiss(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...], named: list[Prose]
) -> None:
    """With ``plants`` in the DBC reader, the gate names ``named`` at the presence."""
    found = gate_report(monkeypatch, plants)
    assert unparsed(found) == []
    assert named_at(found, _PRESENCE) == named


# Each case: its plant, and what the gate names at the comment target's kind.
_COMMENT_CASES = [
    pytest.param(_plant(_KIND_HELD, _KIND_HELD), [], id="the kind as written"),
    pytest.param(
        _plant(_KINDS, CppText('{"network", "node", "message", "signal"}')),
        [Prose("'envVar' is in replyText only")],
        id="envVar dropped from the call",
    ),
    pytest.param(
        _plant(
            CppText("return DbcCommentTargetNetwork{};"),
            CppText("return DbcCommentTargetEnvVar{};"),
        ),
        [
            Prose(
                _IN_COMMENT
                + "the code after the tests of the word at 'kind' reads 'envVar', 'network' alike"
            )
        ],
        id="the network test building the last arm's type",
    ),
    pytest.param(
        _plant(_KIND_HELD, CppText('auto const kind = field_string(m, path, "kind");')),
        [Prose(_IN_COMMENT + "no field_word call at 'kind'")],
        id="the kind read with field_string",
    ),
]


@pytest.mark.parametrize(("plants", "named"), _COMMENT_CASES)
def test_the_gate_names_at_the_comment_target_kind_what_its_tests_read_amiss(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...], named: list[Prose]
) -> None:
    """With ``plants`` in the DBC reader, the gate names ``named`` at the comment target's kind."""
    found = gate_report(monkeypatch, plants)
    assert unparsed(found) == []
    assert named_at(found, _COMMENT) == named


# Each case: its plant, and what the gate names at the attribute's kind.
_ATTRIBUTE_CASES = [
    pytest.param(_plant(_ATTRIBUTE_HELD, _ATTRIBUTE_HELD), [], id="the kind as written"),
    pytest.param(
        _plant(_ATTRIBUTE_KINDS, CppText('{"definition", "default"}')),
        [Prose("'assignment' is in replyText only")],
        id="assignment dropped from the call",
    ),
    pytest.param(
        _plant(CppText("return DbcAttrDefault{"), CppText("return DbcAttrAssign{")),
        [
            Prose(
                _IN_ATTRIBUTE
                + "the code after the tests of the word at 'kind' reads 'assignment', 'default'"
                + " alike"
            )
        ],
        id="the default test building the last arm's type",
    ),
    pytest.param(
        _plant(_ATTRIBUTE_HELD, CppText('auto const kind = field_string(m, path, "kind");')),
        [Prose(_IN_ATTRIBUTE + "no field_word call at 'kind'")],
        id="the kind read with field_string",
    ),
]


@pytest.mark.parametrize(("plants", "named"), _ATTRIBUTE_CASES)
def test_the_gate_names_at_the_attribute_kind_what_its_tests_read_amiss(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...], named: list[Prose]
) -> None:
    """With ``plants`` in the DBC reader, the gate names ``named`` at the attribute's kind."""
    found = gate_report(monkeypatch, plants)
    assert unparsed(found) == []
    assert named_at(found, _ATTRIBUTE) == named


# Each case: its plant, and what the gate names at a definition's type kind.
_TYPE_CASES = [
    pytest.param(_plant(_TYPE_HELD, _TYPE_HELD), [], id="the kind as written"),
    pytest.param(
        _plant(_TYPE_HELD, CppText(_TYPE_HEAD + '{"int", "float", "string", "enum"});')),
        [Prose("'hex' is in replyText only")],
        id="hex dropped from the call",
    ),
    pytest.param(
        _plant(CppText("return DbcAttrTypeInt{"), CppText("return DbcAttrTypeHex{")),
        [
            Prose(
                _IN_TYPE + "the code after the tests of the word at 'kind' reads 'hex', 'int' alike"
            )
        ],
        id="the int test building the last arm's type",
    ),
    pytest.param(
        _plant(
            _TYPE_HELD,
            CppText('DbcAttrType {\n    auto const kind = field_string(m, path, "kind");'),
        ),
        [Prose(_IN_TYPE + "no field_word call at 'kind'")],
        id="the kind read with field_string",
    ),
]


@pytest.mark.parametrize(("plants", "named"), _TYPE_CASES)
def test_the_gate_names_at_the_type_kind_what_its_tests_read_amiss(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...], named: list[Prose]
) -> None:
    """With ``plants`` in the DBC reader, the gate names ``named`` at a definition's type kind."""
    found = gate_report(monkeypatch, plants)
    assert unparsed(found) == []
    assert named_at(found, _TYPE) == named


# Each case: its plant, and what the gate names at an attribute value's kind.
_VALUE_CASES = [
    pytest.param(_plant(_VALUE_HELD, _VALUE_HELD), [], id="the kind as written"),
    pytest.param(
        _plant(_VALUE_HELD, CppText(_VALUE_HEAD + '{"int", "float", "string", "enum"});')),
        [Prose("'hex' is in replyText only")],
        id="hex dropped from the call",
    ),
    pytest.param(
        _plant(CppText("return DbcAttrValueInt{"), CppText("return DbcAttrValueHex{")),
        [
            Prose(
                _IN_VALUE
                + "the code after the tests of the word at 'kind' reads 'hex', 'int' alike"
            )
        ],
        id="the int test building the last arm's type",
    ),
    pytest.param(
        _plant(
            _VALUE_HELD,
            CppText('DbcAttrValue {\n    auto const kind = field_string(m, path, "kind");'),
        ),
        [Prose(_IN_VALUE + "no field_word call at 'kind'")],
        id="the kind read with field_string",
    ),
]


@pytest.mark.parametrize(("plants", "named"), _VALUE_CASES)
def test_the_gate_names_at_the_value_kind_what_its_tests_read_amiss(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...], named: list[Prose]
) -> None:
    """With ``plants`` in the DBC reader, the gate names ``named`` at an attribute value's kind."""
    found = gate_report(monkeypatch, plants)
    assert unparsed(found) == []
    assert named_at(found, _VALUE) == named


# Each case: its plant, and what the gate names at an attribute target's kind.
_TARGET_CASES = [
    pytest.param(_plant(_TARGET_HELD, _TARGET_HELD), [], id="the kind as written"),
    pytest.param(
        _plant(
            _TARGET_KINDS, CppText('{"network", "node", "message", "signal", "envVar", "nodeMsg"}')
        ),
        [Prose("'nodeSig' is in replyText only")],
        id="nodeSig dropped from the call",
    ),
    pytest.param(
        _plant(CppText("return DbcAttrTargetNodeMsg{"), CppText("return DbcAttrTargetNodeSig{")),
        [
            Prose(
                _IN_TARGET
                + "the code after the tests of the word at 'kind' reads 'nodeMsg', 'nodeSig' alike"
            )
        ],
        id="the nodeMsg test building the last arm's type",
    ),
    pytest.param(
        _plant(
            _TARGET_HELD,
            CppText('DbcAttrTarget {\n    auto const kind = field_string(m, path, "kind");'),
        ),
        [Prose(_IN_TARGET + "no field_word call at 'kind'")],
        id="the kind read with field_string",
    ),
]


@pytest.mark.parametrize(("plants", "named"), _TARGET_CASES)
def test_the_gate_names_at_the_target_kind_what_its_tests_read_amiss(
    monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...], named: list[Prose]
) -> None:
    """With ``plants`` in the DBC reader, the gate names ``named`` at an attribute target's kind."""
    found = gate_report(monkeypatch, plants)
    assert unparsed(found) == []
    assert named_at(found, _TARGET) == named
