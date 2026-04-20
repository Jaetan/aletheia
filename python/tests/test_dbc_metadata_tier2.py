"""Structural roundtrip tests for Tier 2 DBC metadata.

Tier 2 widens the DBC wire shape with the three tagged-union arrays introduced
by the Agda core extension (B.1.x): ``nodes`` (BU_), ``comments`` (CM_) and
``attributes`` (BA_DEF_ / BA_DEF_DEF_ / BA_ with their BA_REL_ siblings). Each
tagged object uses ``"kind"`` as the first-field discriminator so the Agda
parser can dispatch without separate arrays.

These tests drive ``parse_dbc`` → ``format_dbc`` through the real FFI (same
pattern as the Tier 1 suite) to prove every variant is reconstructed by the
Agda core on the return trip. Numeric bounds survive as ``Fraction`` — the
same ℚ-precision guarantee the rest of the wire carries — so the fixture
pins one non-trivial rational (``Fraction(-1, 2)`` / ``Fraction(22, 7)``)
to fail loudly if a future refactor ever drops to ``float``.
"""

from __future__ import annotations

from fractions import Fraction

import pytest

from _dbc_helpers import message, signal

from aletheia import AletheiaClient
from aletheia.protocols import (
    DBCAttrAssign,
    DBCAttrDef,
    DBCAttrDefault,
    DBCAttribute,
    DBCComment,
    DBCDefinition,
    DBCNode,
)


# ---------------------------------------------------------------------------
# Fixture builders
# ---------------------------------------------------------------------------


_MSG_ID = 0x123
_MSG_NAME = "Engine"
_SIG_NAME = "Rpm"


def _msg_one_signal() -> dict:
    return message(
        _MSG_ID,
        _MSG_NAME,
        [signal(_SIG_NAME, length=16, maximum=8000.0, unit="rpm")],
    )


def _all_comments() -> list[DBCComment]:
    """One comment per ``CommentTarget`` variant (5/5)."""
    return [
        {"target": {"kind": "network"}, "text": "network-scope comment"},
        {"target": {"kind": "node", "node": "ECU_A"}, "text": "node comment"},
        {"target": {"kind": "message", "id": _MSG_ID}, "text": "message comment"},
        {
            "target": {"kind": "signal", "id": _MSG_ID, "signal": _SIG_NAME},
            "text": "signal comment",
        },
        {"target": {"kind": "envVar", "envVar": "AmbientTemp"}, "text": "env-var comment"},
    ]


def _all_attributes() -> list[DBCAttribute]:
    """Every attribute shape the Agda core accepts.

    Covers all 5 ``DBCAttrType`` variants, all 5 ``DBCAttrValue`` variants,
    and all 7 ``DBCAttrTarget`` variants. The float bounds use a non-trivial
    rational so the ℚ-precision guarantee has teeth.
    """
    defs: list[DBCAttribute] = [
        # 5 attrType variants — scopes chosen to cover the simple ones.
        {
            "kind": "definition", "name": "IntAttr", "scope": "network",
            "attrType": {"kind": "int", "min": 0, "max": 100},
        },
        {
            "kind": "definition", "name": "FloatAttr", "scope": "message",
            "attrType": {
                "kind": "float",
                "min": Fraction(-1, 2),
                "max": Fraction(22, 7),
            },
        },
        {
            "kind": "definition", "name": "StringAttr", "scope": "signal",
            "attrType": {"kind": "string"},
        },
        {
            "kind": "definition", "name": "EnumAttr", "scope": "node",
            "attrType": {"kind": "enum", "values": ["low", "medium", "high"]},
        },
        {
            "kind": "definition", "name": "HexAttr", "scope": "envVar",
            "attrType": {"kind": "hex", "min": 0, "max": 255},
        },
        # Relational definition scopes cover the remaining two AttrScope values.
        {
            "kind": "definition", "name": "RelMsgAttr", "scope": "nodeMsg",
            "attrType": {"kind": "int", "min": 0, "max": 10},
        },
        {
            "kind": "definition", "name": "RelSigAttr", "scope": "nodeSig",
            "attrType": {"kind": "int", "min": 0, "max": 5},
        },
    ]
    defaults: list[DBCAttribute] = [
        # 5 attrValue variants.
        {"kind": "default", "name": "IntAttr", "value": {"kind": "int", "value": 42}},
        {
            "kind": "default", "name": "FloatAttr",
            "value": {"kind": "float", "value": Fraction(1, 3)},
        },
        {
            "kind": "default", "name": "StringAttr",
            "value": {"kind": "string", "value": "hello"},
        },
        {"kind": "default", "name": "EnumAttr", "value": {"kind": "enum", "value": 1}},
        {"kind": "default", "name": "HexAttr", "value": {"kind": "hex", "value": 0xFF}},
    ]
    assigns: list[DBCAttribute] = [
        # 7 attrTarget variants. Value kinds are reused — the target is the
        # axis under test here, not the value.
        {
            "kind": "assignment", "name": "IntAttr",
            "target": {"kind": "network"},
            "value": {"kind": "int", "value": 1},
        },
        {
            "kind": "assignment", "name": "IntAttr",
            "target": {"kind": "node", "node": "ECU_A"},
            "value": {"kind": "int", "value": 2},
        },
        {
            "kind": "assignment", "name": "IntAttr",
            "target": {"kind": "message", "id": _MSG_ID},
            "value": {"kind": "int", "value": 3},
        },
        {
            "kind": "assignment", "name": "IntAttr",
            "target": {"kind": "signal", "id": _MSG_ID, "signal": _SIG_NAME},
            "value": {"kind": "int", "value": 4},
        },
        {
            "kind": "assignment", "name": "IntAttr",
            "target": {"kind": "envVar", "envVar": "AmbientTemp"},
            "value": {"kind": "int", "value": 5},
        },
        {
            "kind": "assignment", "name": "RelMsgAttr",
            "target": {"kind": "nodeMsg", "node": "ECU_A", "id": _MSG_ID},
            "value": {"kind": "int", "value": 6},
        },
        {
            "kind": "assignment", "name": "RelSigAttr",
            "target": {
                "kind": "nodeSig",
                "node": "ECU_A",
                "id": _MSG_ID,
                "signal": _SIG_NAME,
            },
            "value": {"kind": "int", "value": 7},
        },
    ]
    return defs + defaults + assigns


def _full_dbc() -> DBCDefinition:
    """DBC with every Tier 2 variant exercised."""
    nodes: list[DBCNode] = [{"name": "ECU_A"}, {"name": "ECU_B"}]
    return {
        "version": "1.0",
        "messages": [_msg_one_signal()],
        "nodes": nodes,
        "comments": _all_comments(),
        "attributes": _all_attributes(),
    }


def _empty_metadata_dbc() -> DBCDefinition:
    """Explicit empty arrays — the empty case has to survive the wire too."""
    return {
        "version": "1.0",
        "messages": [_msg_one_signal()],
        "nodes": [],
        "comments": [],
        "attributes": [],
    }


def _no_tier2_keys_dbc() -> DBCDefinition:
    """Pre-Tier-2 shape — no NotRequired Tier 2 keys. Parser treats absent as
    empty; formatter still emits the arrays."""
    return {"version": "1.0", "messages": [_msg_one_signal()]}


# ---------------------------------------------------------------------------
# Roundtrip tests
# ---------------------------------------------------------------------------


class TestDBCMetadataTier2Roundtrip:
    """parse_dbc → format_dbc preserves every Tier 2 variant."""

    def test_full_metadata_survives(self) -> None:
        """Every node / comment / attribute round-trips structurally."""
        original = _full_dbc()
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        assert formatted["nodes"] == original["nodes"]
        assert formatted["comments"] == original["comments"]
        assert formatted["attributes"] == original["attributes"]

    def test_empty_metadata_survives(self) -> None:
        """Explicit empty Tier 2 arrays round-trip as empty arrays."""
        original = _empty_metadata_dbc()
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        assert formatted["nodes"] == []
        assert formatted["comments"] == []
        assert formatted["attributes"] == []

    def test_absent_tier2_keys_default_to_empty(self) -> None:
        """Pre-Tier-2 input (no NotRequired keys) is accepted; formatter emits
        empty arrays. Hand-written fixtures remain valid."""
        original = _no_tier2_keys_dbc()
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        assert formatted["nodes"] == []
        assert formatted["comments"] == []
        assert formatted["attributes"] == []

    def test_float_attr_bounds_are_exact_rationals(self) -> None:
        """Float ``min`` / ``max`` / ``value`` survive as ``Fraction`` — the
        ℚ-precision guarantee that keeps the wire lossless (R14-A7)."""
        original = _full_dbc()
        with AletheiaClient() as client:
            client.parse_dbc(original)
            formatted = client.format_dbc()

        attrs = formatted["attributes"]
        float_def = next(
            a for a in attrs
            if a["kind"] == "definition" and a["name"] == "FloatAttr"
        )
        assert isinstance(float_def, dict) and float_def["kind"] == "definition"
        float_def_typed: DBCAttrDef = float_def
        ftype = float_def_typed["attrType"]
        assert ftype["kind"] == "float"
        assert ftype["min"] == Fraction(-1, 2)
        assert ftype["max"] == Fraction(22, 7)
        assert isinstance(ftype["min"], Fraction)
        assert isinstance(ftype["max"], Fraction)

        float_default = next(
            a for a in attrs
            if a["kind"] == "default" and a["name"] == "FloatAttr"
        )
        float_default_typed: DBCAttrDefault = float_default  # type: ignore[assignment]
        fval = float_default_typed["value"]
        assert fval["kind"] == "float"
        assert fval["value"] == Fraction(1, 3)
        assert isinstance(fval["value"], Fraction)

    def test_every_comment_target_kind_preserved(self) -> None:
        """All 5 ``CommentTarget`` kinds survive the round-trip in order."""
        original = _full_dbc()
        with AletheiaClient() as client:
            client.parse_dbc(original)
            formatted = client.format_dbc()

        kinds = [c["target"]["kind"] for c in formatted["comments"]]
        assert kinds == ["network", "node", "message", "signal", "envVar"]

    def test_every_attribute_target_kind_preserved(self) -> None:
        """All 7 ``AttrTarget`` kinds survive the round-trip in order."""
        original = _full_dbc()
        with AletheiaClient() as client:
            client.parse_dbc(original)
            formatted = client.format_dbc()

        assignments = [a for a in formatted["attributes"] if a["kind"] == "assignment"]
        kinds = [cast_assign(a)["target"]["kind"] for a in assignments]
        assert kinds == [
            "network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig",
        ]


def cast_assign(a: DBCAttribute) -> DBCAttrAssign:
    """Narrow a ``DBCAttribute`` to ``DBCAttrAssign`` for field access; raises
    if the ``kind`` discriminator disagrees."""
    assert a["kind"] == "assignment"
    return a  # type: ignore[return-value]


# ---------------------------------------------------------------------------
# Rejection tests
# ---------------------------------------------------------------------------


class TestDBCMetadataTier2Rejects:
    """Malformed Tier 2 payloads must be rejected by the Agda parser."""

    def test_unknown_comment_target_kind_rejected(self) -> None:
        """A ``CommentTarget`` with a bogus ``kind`` is rejected at parse time."""
        bad: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_one_signal()],
            "comments": [
                {
                    "target": {"kind": "bogus"},  # type: ignore[typeddict-item]
                    "text": "x",
                },
            ],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(bad)
        assert result["status"] == "error", result

    def test_unknown_attribute_kind_rejected(self) -> None:
        """A ``DBCAttribute`` with a bogus ``kind`` is rejected at parse time."""
        bad: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_one_signal()],
            "attributes": [
                {
                    "kind": "nonsense",  # type: ignore[typeddict-item]
                    "name": "X",
                },
            ],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(bad)
        assert result["status"] == "error", result


# ---------------------------------------------------------------------------
# Single comment string preservation
# ---------------------------------------------------------------------------


def test_comment_text_with_special_chars() -> None:
    """Embedded spaces, quotes, and punctuation survive the round-trip
    untouched — the parser doesn't re-interpret comment bodies."""
    spacey: DBCDefinition = {
        "version": "1.0",
        "messages": [_msg_one_signal()],
        "comments": [
            {
                "target": {"kind": "network"},
                "text": "multi-word: with ' and , punctuation",
            },
        ],
    }
    with AletheiaClient() as client:
        result = client.parse_dbc(spacey)
        if result["status"] != "success":
            pytest.fail(f"expected success, got {result}")
        formatted = client.format_dbc()

    assert formatted["comments"] == spacey["comments"]
