# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads an attribute's scope and its type, value and target kinds from a call.

``attribute`` hands a definition's scope to ``field_word``, which refuses
every other word, and maps the word through ``attr_scope``; ``read_attr_type``,
``read_attr_value`` and ``read_attr_target`` read a kind into a ``let`` they
hand to ``attr_type``, ``attr_value`` and ``attr_target``.  The call's words
are the Rust reader's set at its place, and the mapping's ``_`` arm reads the
one awaited word no literal arm names: a word dropped from the call, a last arm
sharing another arm's variant, a word handed in another position, or a refusal
the caller reads as a word is named at the place.
"""

from __future__ import annotations

import pytest
from _rust_reply_gate import named_at

from tools._reply_places import ReplyPlace
from tools._reply_places_rust import RUST_DECODE, RustText

from aletheia.common_types import Prose

_SCOPE = ReplyPlace("dbc/attributes/scope <definition>")
_TYPE_KIND = ReplyPlace("dbc/attributes/attrType/kind")
_VALUE_KIND = ReplyPlace("dbc/attributes/value/kind")
_TARGET_KIND = ReplyPlace("dbc/attributes/target/kind")
_SCOPE_WORDS = RustText('"nodeMsg", "nodeSig",\n                ],\n            )?),')
_SCOPE_HANDED = RustText(")?),\n            attr_type: field_object_of(")
_TYPE_WORDS = RustText('"enum", "hex"],\n    )?;\n    attr_type(')
_TYPE_HANDED = RustText("attr_type(kind, type_entry, path)")
_VALUE_WORDS = RustText('"enum", "hex"],\n    )?;\n    attr_value(')
_VALUE_HANDED = RustText("attr_value(kind, value, path)")
_TARGET_WORDS = RustText('"nodeMsg", "nodeSig",\n        ],\n    )?;\n    attr_target(')
_TARGET_HANDED = RustText("attr_target(kind, target, path)")
_IN_ATTRIBUTE = "rust/src/dbc/decode.rs:attribute: "
_IN_TYPE = "rust/src/dbc/decode.rs:read_attr_type: "
_IN_VALUE = "rust/src/dbc/decode.rs:read_attr_value: "
_IN_TARGET = "rust/src/dbc/decode.rs:read_attr_target: "


@pytest.mark.parametrize(
    ("place", "written", "planted", "named"),
    [
        pytest.param(_SCOPE, _SCOPE_WORDS, _SCOPE_WORDS, [], id="scope"),
        pytest.param(
            _SCOPE,
            _SCOPE_WORDS,
            RustText('"nodeMsg",\n                ],\n            )?),'),
            [Prose("'nodeSig' is in replyText only")],
            id="scope with nodeSig dropped from the call",
        ),
        pytest.param(
            _SCOPE,
            RustText('"envVar" => AttrScope::EnvVar,\n        "nodeMsg" => AttrScope::NodeMsg,'),
            RustText(
                '"envVar" => AttrScope::NodeSig,\n'
                + '        "nodeMsg" | "nodeSig" => AttrScope::NodeSig,'
            ),
            [
                Prose(
                    _IN_ATTRIBUTE
                    + "the _ arm of attr_scope reads 'envVar', 'nodeMsg', 'nodeSig' alike"
                )
            ],
            id="scope with its last arm sharing the variant of two arms",
        ),
        pytest.param(
            _SCOPE,
            _SCOPE_HANDED,
            RustText(
                ')\n            .unwrap_or("nodeSig")),\n            attr_type: field_object_of('
            ),
            [
                Prose(
                    _IN_ATTRIBUTE
                    + "does not hand the word field_word reads at 'scope' to attr_scope, "
                    + "as its first argument or through a let"
                )
            ],
            id="scope with its refusal read as nodeSig",
        ),
        pytest.param(_TYPE_KIND, _TYPE_HANDED, _TYPE_HANDED, [], id="type kind"),
        pytest.param(
            _TYPE_KIND,
            _TYPE_WORDS,
            RustText('"enum"],\n    )?;\n    attr_type('),
            [Prose("'hex' is in replyText only")],
            id="type kind with hex dropped from the call",
        ),
        pytest.param(
            _TYPE_KIND,
            RustText('"string" => Ok(AttrType::String),'),
            RustText('"string" => Ok(AttrType::Hex { min: 0, max: 0 }),'),
            [Prose(_IN_TYPE + "the _ arm of attr_type reads 'hex', 'string' alike")],
            id="type kind with its last arm sharing the string arm's variant",
        ),
        pytest.param(
            _TYPE_KIND,
            _TYPE_HANDED,
            RustText("attr_type(type_entry, kind, path)"),
            [Prose(_IN_TYPE + "uses kind other than once, as the first argument of attr_type")],
            id="type kind handed second",
        ),
        pytest.param(
            _TYPE_KIND,
            RustText(")?;\n    attr_type(kind, type_entry, path)"),
            RustText(')\n    .unwrap_or("hex");\n    attr_type(kind, type_entry, path)'),
            [
                Prose(
                    _IN_TYPE
                    + "does not hand the word field_word reads at 'kind' to attr_type, "
                    + "as its first argument or through a let"
                )
            ],
            id="type kind with its refusal read as hex",
        ),
    ],
)
def test_a_definition_word_reaches_its_mapping(
    monkeypatch: pytest.MonkeyPatch,
    place: ReplyPlace,
    written: RustText,
    planted: RustText,
    named: list[Prose],
) -> None:
    """With ``written`` planted as ``planted`` in the DBC decoder, the gate names ``named``.

    The scope is handed to ``attr_scope`` as its first argument and the type
    kind through a ``let``; a ``_`` arm reading two words or more, as one
    sharing a variant with other arms does, is refused like every shared last
    arm.
    """
    assert named_at(monkeypatch, (written, planted), place, RUST_DECODE) == named


@pytest.mark.parametrize(
    ("place", "written", "planted", "named"),
    [
        pytest.param(_VALUE_KIND, _VALUE_HANDED, _VALUE_HANDED, [], id="value kind"),
        pytest.param(
            _VALUE_KIND,
            _VALUE_WORDS,
            RustText('"enum"],\n    )?;\n    attr_value('),
            [Prose("'hex' is in replyText only")],
            id="value kind with hex dropped from the call",
        ),
        pytest.param(
            _VALUE_KIND,
            RustText('"enum" => Ok(AttrValue::Enum(field_i64(value, path, "value")?)),'),
            RustText('"enum" => Ok(AttrValue::Hex(field_i64(value, path, "value")?)),'),
            [Prose(_IN_VALUE + "the _ arm of attr_value reads 'enum', 'hex' alike")],
            id="value kind with its last arm sharing the enum arm's variant",
        ),
        pytest.param(
            _VALUE_KIND,
            _VALUE_HANDED,
            RustText("attr_value(value, kind, path)"),
            [Prose(_IN_VALUE + "uses kind other than once, as the first argument of attr_value")],
            id="value kind handed second",
        ),
        pytest.param(
            _VALUE_KIND,
            RustText(")?;\n    attr_value(kind, value, path)"),
            RustText(')\n    .unwrap_or("hex");\n    attr_value(kind, value, path)'),
            [
                Prose(
                    _IN_VALUE
                    + "does not hand the word field_word reads at 'kind' to attr_value, "
                    + "as its first argument or through a let"
                )
            ],
            id="value kind with its refusal read as hex",
        ),
        pytest.param(_TARGET_KIND, _TARGET_HANDED, _TARGET_HANDED, [], id="target kind"),
        pytest.param(
            _TARGET_KIND,
            _TARGET_WORDS,
            RustText('"nodeMsg",\n        ],\n    )?;\n    attr_target('),
            [Prose("'nodeSig' is in replyText only")],
            id="target kind with nodeSig dropped from the call",
        ),
        pytest.param(
            _TARGET_KIND,
            RustText('"network" => Ok(AttrTarget::Network),'),
            RustText('"network" => Ok(AttrTarget::NodeSig),'),
            [Prose(_IN_TARGET + "the _ arm of attr_target reads 'network', 'nodeSig' alike")],
            id="target kind with its last arm sharing the network arm's variant",
        ),
        pytest.param(
            _TARGET_KIND,
            _TARGET_HANDED,
            RustText("attr_target(target, kind, path)"),
            [Prose(_IN_TARGET + "uses kind other than once, as the first argument of attr_target")],
            id="target kind handed second",
        ),
        pytest.param(
            _TARGET_KIND,
            RustText(")?;\n    attr_target(kind, target, path)"),
            RustText(')\n    .unwrap_or("nodeSig");\n    attr_target(kind, target, path)'),
            [
                Prose(
                    _IN_TARGET
                    + "does not hand the word field_word reads at 'kind' to attr_target, "
                    + "as its first argument or through a let"
                )
            ],
            id="target kind with its refusal read as nodeSig",
        ),
    ],
)
def test_an_attribute_value_or_target_word_reaches_its_mapping(
    monkeypatch: pytest.MonkeyPatch,
    place: ReplyPlace,
    written: RustText,
    planted: RustText,
    named: list[Prose],
) -> None:
    """With ``written`` planted as ``planted`` in the DBC decoder, the gate names ``named``.

    A value's kind and a target's kind are each handed through a ``let``; a
    ``_`` arm reading two words or more, as one sharing a variant with another
    arm does, is refused like every shared last arm.
    """
    assert named_at(monkeypatch, (written, planted), place, RUST_DECODE) == named
