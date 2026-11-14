# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads a Go DBC place from its reader's call and the switch on its word.

``readByteOrder``, ``parseSignalPresence``, ``parseCommentTarget``,
``parseAttribute``, ``readAttrScope``, ``parseAttrType``, ``parseAttrValue``
and ``parseAttrTarget`` hand their place's key to one ``fieldWord`` call and
dispatch the word it binds in a ``switch`` ending in ``default``.  An arm gives
one value, an exported name or a composite literal of an exported type, the
type standing for it, returned with a nil error after statements whose every
return returns an error; the ``default`` reads the awaited words no other arm
names and the words of the arms giving its value.  A word dropped from a call
or added to it, a ``default`` reading another word or several, a case whose
literal is written with an escape, and an arm giving no one value are named at
the place.
"""

from __future__ import annotations

import pytest
from _go_reply_gate import named_in

from tools._reply_places import GoText, ReplyPlace
from tools._reply_places_go import GO_DBC

from aletheia.common_types import Prose

_BYTE_ORDER = ReplyPlace("dbc/messages/signals/byteOrder")
_PRESENCE = ReplyPlace("dbc/messages/signals/presence")
_COMMENT = ReplyPlace("dbc/comments/target/kind")
_ATTRIBUTE = ReplyPlace("dbc/attributes/kind")
_SCOPE = ReplyPlace("dbc/attributes/scope <definition>")
_ATTR_TYPE = ReplyPlace("dbc/attributes/attrType/kind")
_VALUE = ReplyPlace("dbc/attributes/value/kind")
_TARGET = ReplyPlace("dbc/attributes/target/kind")
_IN_ORDER = "go/aletheia/json_dbc.go:readByteOrder: "
_IN_PRESENCE = "go/aletheia/json_dbc.go:parseSignalPresence: "
_IN_COMMENT = "go/aletheia/json_dbc.go:parseCommentTarget: "
_IN_ATTRIBUTE = "go/aletheia/json_dbc.go:parseAttribute: "
_IN_SCOPE = "go/aletheia/json_dbc.go:readAttrScope: "
_IN_ATTR_TYPE = "go/aletheia/json_dbc.go:parseAttrType: "
_IN_VALUE = "go/aletheia/json_dbc.go:parseAttrValue: "
_IN_TARGET = "go/aletheia/json_dbc.go:parseAttrTarget: "
_ORDER_CALL = GoText('fieldWord(j, path, "byteOrder", "little_endian", "big_endian")')
_BIG = GoText("\tdefault:\n\t\treturn BigEndian, nil\n")
_ALWAYS = GoText("\t\treturn AlwaysPresent{}, nil\n")
_NODE_RETURN = GoText("return DBCCommentTargetNode{Node: NodeName(node)}, nil")
_NODE_BODY = (
    'node, err := fieldString(m, path, "node")\n\t\t'
    + "if err != nil {\n\t\t\treturn nil, err\n\t\t}\n\t\t"
    + _NODE_RETURN
)
_NODE_ARM = GoText(f'\tcase "node":\n\t\t{_NODE_BODY}\n')
_ENV_VAR = GoText("\t\treturn DBCCommentTargetEnvVar{EnvVar: envVar}, nil\n")
_ATTRIBUTE_CALL = GoText('fieldWord(m, path, "kind", "definition", "default", "assignment")')
_SCOPES = '"network", "node", "message", "signal", "envVar", "nodeMsg"'
_SCOPE_CALL = GoText(f'fieldWord(m, path, "scope", {_SCOPES}, "nodeSig")')
_NODE_SIG = GoText("\tdefault:\n\t\treturn DBCAttrScopeNodeSig, nil\n")
_KINDS = 'fieldWord(m, path, "kind", "int", "float", "string", "enum"'
# A type's and a value's kind are read by one call, told apart by the result before it.
_TYPE_HEAD = "(DBCAttrType, error) {\n\tkind, err := "
_VALUE_HEAD = "(DBCAttrValue, error) {\n\tkind, err := "
_TYPE_CALL = GoText(f'{_TYPE_HEAD}{_KINDS}, "hex")')
_HEX = GoText("\t\treturn DBCAttrTypeHex{Min: minV, Max: maxV}, nil\n")
_VALUE_CALL = GoText(f'{_VALUE_HEAD}{_KINDS}, "hex")')
_HEX_VALUE = GoText("\t\treturn DBCAttrValueHex{Value: v}, nil\n")
_INT_READ = '\n\t\tv, err := fieldInt64(m, path, "value")'
_INT_VALUE = GoText(f'\tcase "int":{_INT_READ}')
_TARGET_CALL = GoText(f'fieldWord(m, path, "kind", {_SCOPES}, "nodeSig")')
_NODE_SIG_TARGET = GoText(
    "\t\treturn DBCAttrTargetNodeSig{Node: NodeName(node), ID: id, "
    + "Signal: SignalName(signal)}, nil\n"
)


def _node_planted(old: GoText, new: GoText) -> tuple[GoText, list[Prose]]:
    """Return the node arm with ``old`` of its code planted as ``new``, and the gate's refusal."""
    body = _NODE_BODY.replace(old, new)
    return GoText(f'\tcase "node":\n\t\t{body}\n'), [
        Prose(f"{_IN_COMMENT}{body!r} gives no one value")
    ]


# Each case: the place it reads, the source it plants over, the plant, and what
# the gate names at the place.
_CASES = [
    pytest.param(_BYTE_ORDER, _ORDER_CALL, _ORDER_CALL, [], id="byte order as written"),
    pytest.param(
        _BYTE_ORDER,
        _ORDER_CALL,
        GoText('fieldWord(j, path, "byteOrder", "little_endian")'),
        [Prose("'big_endian' is in replyText only")],
        id="byte order with big_endian dropped from fieldWord",
    ),
    pytest.param(
        _BYTE_ORDER,
        _BIG,
        GoText("\tdefault:\n\t\treturn LittleEndian, nil\n"),
        [
            Prose(
                _IN_ORDER
                + "the default of the switch on name reads 'big_endian', 'little_endian' alike"
            )
        ],
        id="byte order with a default sharing the little_endian case's value",
    ),
    pytest.param(
        _BYTE_ORDER,
        _BIG,
        GoText("\tdefault:\n\t\treturn ByteOrder(1), nil\n"),
        [Prose(_IN_ORDER + "'return ByteOrder(1), nil' gives no one value")],
        id="byte order with a default returning a conversion",
    ),
    pytest.param(_PRESENCE, _ALWAYS, _ALWAYS, [], id="presence as written"),
    pytest.param(
        _PRESENCE,
        _ALWAYS,
        GoText("\t\treturn alwaysPresent{}, nil\n"),
        [Prose(_IN_PRESENCE + "'return alwaysPresent{}, nil' gives no one value")],
        id="presence with an arm building an unexported type",
    ),
    pytest.param(
        _PRESENCE,
        _ALWAYS,
        GoText("\t\treturn ÄlwaysPresent{}, nil\n"),
        [Prose(_IN_PRESENCE + "'return ÄlwaysPresent{}, nil' gives no one value")],
        id="presence with an arm building a type opening with a capital outside ASCII",
    ),
    pytest.param(
        _PRESENCE,
        _ALWAYS,
        GoText("\t\treturn AlwaysPresent[int]{}, nil\n"),
        [Prose(_IN_PRESENCE + "'return AlwaysPresent[int]{}, nil' gives no one value")],
        id="presence with an arm building an instance of a generic type",
    ),
    pytest.param(_COMMENT, _NODE_ARM, _NODE_ARM, [], id="comment target as written"),
    pytest.param(
        _COMMENT,
        _NODE_ARM,
        *_node_planted(GoText("return nil, err"), GoText("return DBCCommentTargetNetwork{}, nil")),
        id="comment target with an arm returning a value before its last statement",
    ),
    pytest.param(
        _COMMENT,
        _NODE_ARM,
        *_node_planted(GoText("return nil, err"), GoText("return")),
        id="comment target with an arm returning nothing before its last statement",
    ),
    pytest.param(
        _COMMENT,
        _NODE_ARM,
        *_node_planted(_NODE_RETURN, GoText("return")),
        id="comment target with an arm ending in a return of nothing",
    ),
    pytest.param(
        _COMMENT,
        _ENV_VAR,
        GoText("\t\treturn DBCCommentTargetNode{Node: NodeName(envVar)}, nil\n"),
        [Prose(_IN_COMMENT + "the default of the switch on kind reads 'envVar', 'node' alike")],
        id="comment target with a default building the node case's type",
    ),
    pytest.param(_ATTRIBUTE, _ATTRIBUTE_CALL, _ATTRIBUTE_CALL, [], id="attribute as written"),
    pytest.param(
        _ATTRIBUTE,
        _ATTRIBUTE_CALL,
        GoText('fieldWord(m, path, "kind", "definition", "default")'),
        [Prose("'assignment' is in replyText only")],
        id="attribute with assignment dropped from fieldWord",
    ),
    pytest.param(
        _ATTRIBUTE,
        _ATTRIBUTE_CALL,
        GoText('fieldWord(m, path, "kind", "definition", "default", "assignment", "bogus")'),
        [
            Prose(
                _IN_ATTRIBUTE
                + "the default of the switch on kind reads 'assignment', 'bogus' alike"
            )
        ],
        id="attribute with a word added to fieldWord",
    ),
    pytest.param(_SCOPE, _SCOPE_CALL, _SCOPE_CALL, [], id="scope as written"),
    pytest.param(
        _SCOPE,
        _SCOPE_CALL,
        GoText(f'fieldWord(m, path, "scope", {_SCOPES})'),
        [Prose("'nodeSig' is in replyText only")],
        id="scope with nodeSig dropped from fieldWord",
    ),
    pytest.param(
        _SCOPE,
        _NODE_SIG,
        GoText("\tdefault:\n\t\treturn DBCAttrScopeNodeMsg, nil\n"),
        [Prose(_IN_SCOPE + "the default of the switch on scope reads 'nodeMsg', 'nodeSig' alike")],
        id="scope with a default sharing the nodeMsg case's value",
    ),
    pytest.param(_ATTR_TYPE, _TYPE_CALL, _TYPE_CALL, [], id="attribute type as written"),
    pytest.param(
        _ATTR_TYPE,
        _TYPE_CALL,
        GoText(f"{_TYPE_HEAD}{_KINDS})"),
        [Prose("'hex' is in replyText only")],
        id="attribute type with hex dropped from fieldWord",
    ),
    pytest.param(
        _ATTR_TYPE,
        _HEX,
        GoText("\t\treturn DBCAttrTypeInt{Min: minV, Max: maxV}, nil\n"),
        [Prose(_IN_ATTR_TYPE + "the default of the switch on kind reads 'hex', 'int' alike")],
        id="attribute type with a default building the int case's type",
    ),
    pytest.param(_VALUE, _VALUE_CALL, _VALUE_CALL, [], id="attribute value as written"),
    pytest.param(
        _VALUE,
        _VALUE_CALL,
        GoText(f"{_VALUE_HEAD}{_KINDS})"),
        [Prose("'hex' is in replyText only")],
        id="attribute value with hex dropped from fieldWord",
    ),
    pytest.param(
        _VALUE,
        _HEX_VALUE,
        GoText("\t\treturn DBCAttrValueInt{Value: v}, nil\n"),
        [Prose(_IN_VALUE + "the default of the switch on kind reads 'hex', 'int' alike")],
        id="attribute value with a default building the int case's type",
    ),
    pytest.param(
        _VALUE,
        _INT_VALUE,
        GoText(f'\tcase "in\\x74":{_INT_READ}'),
        [
            Prose(
                _IN_VALUE
                + repr('case "in\\x74":')
                + " is not a case of string literals on one line"
            )
        ],
        id="attribute value with a case naming a literal written with an escape",
    ),
    pytest.param(_TARGET, _TARGET_CALL, _TARGET_CALL, [], id="attribute target as written"),
    pytest.param(
        _TARGET,
        _TARGET_CALL,
        GoText(f'fieldWord(m, path, "kind", {_SCOPES})'),
        [Prose("'nodeSig' is in replyText only")],
        id="attribute target with nodeSig dropped from fieldWord",
    ),
    pytest.param(
        _TARGET,
        _NODE_SIG_TARGET,
        GoText("\t\treturn DBCAttrTargetNodeMsg{Node: NodeName(node), ID: id}, nil\n"),
        [Prose(_IN_TARGET + "the default of the switch on kind reads 'nodeMsg', 'nodeSig' alike")],
        id="attribute target with a default building the nodeMsg case's type",
    ),
]


@pytest.mark.parametrize(("place", "written", "planted", "named"), _CASES)
def test_the_gate_names_at_a_dbc_place_what_its_call_and_dispatch_read_amiss(
    monkeypatch: pytest.MonkeyPatch,
    place: ReplyPlace,
    written: GoText,
    planted: GoText,
    named: list[Prose],
) -> None:
    """With ``written`` planted as ``planted``, the gate names ``named`` at ``place``."""
    assert named_in(monkeypatch, GO_DBC, (written, planted), place) == named
