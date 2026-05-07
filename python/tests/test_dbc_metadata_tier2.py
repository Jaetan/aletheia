"""Structural roundtrip tests for Tier 2 DBC metadata.

Tier 2 widens the DBC wire shape with the three tagged-union arrays introduced
by the Agda core extension (B.1.x): ``nodes`` (BU_), ``comments`` (CM_) and
``attributes`` (BA_DEF_ / BA_DEF_DEF_ / BA_ with their BA_REL_ siblings). Each
tagged object uses ``"kind"`` as the first-field discriminator so the Agda
parser can dispatch without separate arrays.

These tests drive ``parse_dbc`` → ``format_dbc`` through the real FFI (same
pattern as the Tier 1 suite) to prove every variant is reconstructed by the
Agda core on the return trip. Numeric bounds survive as ``Fraction`` — the
same decimal-precision guarantee the rest of the wire carries — so the
fixture pins non-trivial DBC-representable rationals (``Fraction(-1, 2)``
/ ``Fraction(1025, 1000)``) to fail loudly if a future refactor ever drops
to ``float``.  DBC attribute bounds are stored as ``DecRat`` (Commit
5/6), so values must have a terminating decimal expansion
(denominator = 2^a · 5^b); rationals like ``22/7`` are rejected with
``parse_non_terminating_rational``.
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
                "max": Fraction(1025, 1000),
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
            "value": {"kind": "float", "value": Fraction(1, 8)},
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
        assert ftype["max"] == Fraction(1025, 1000)
        assert isinstance(ftype["min"], Fraction)
        assert isinstance(ftype["max"], Fraction)

        float_default = next(
            a for a in attrs
            if a["kind"] == "default" and a["name"] == "FloatAttr"
        )
        float_default_typed: DBCAttrDefault = float_default  # type: ignore[assignment]
        fval = float_default_typed["value"]
        assert fval["kind"] == "float"
        assert fval["value"] == Fraction(1, 8)
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

    @pytest.mark.parametrize("field", ["min", "max"])
    def test_float_attr_bound_non_terminating_rejected(self, field: str) -> None:
        """``ATFloat`` min / max must have terminating decimal expansions
        (Commit 5/6).  ``Fraction(22, 7)`` — 3.142857… repeating — gets
        rejected by ``fromℚ?`` with ``parse_non_terminating_rational``."""
        attr_type: dict = {
            "kind": "float",
            "min": Fraction(0),
            "max": Fraction(1),
        }
        attr_type[field] = Fraction(22, 7)
        bad: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_one_signal()],
            "attributes": [
                {
                    "kind": "definition",
                    "name": "FloatAttr",
                    "scope": "network",
                    "attrType": attr_type,  # type: ignore[typeddict-item]
                },
            ],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(bad)
        assert result["status"] == "error"
        assert result["code"] == "parse_non_terminating_rational"
        assert field in result["message"]

    def test_float_attr_value_non_terminating_rejected(self) -> None:
        """``AVFloat`` default value must also have a terminating decimal
        expansion (mirrors ATFloat min/max at the value layer)."""
        bad: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_one_signal()],
            "attributes": [
                {
                    "kind": "definition",
                    "name": "FloatAttr",
                    "scope": "network",
                    "attrType": {
                        "kind": "float",
                        "min": Fraction(0),
                        "max": Fraction(1),
                    },
                },
                {
                    "kind": "default",
                    "name": "FloatAttr",
                    "value": {"kind": "float", "value": Fraction(1, 3)},
                },
            ],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(bad)
        assert result["status"] == "error"
        assert result["code"] == "parse_non_terminating_rational"
        assert "value" in result["message"]


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


# ---------------------------------------------------------------------------
# Signal receivers (SG_ trailing node list)
# ---------------------------------------------------------------------------


def _msg_with_signal_receivers(receivers: list[str]) -> dict:
    return message(
        _MSG_ID,
        _MSG_NAME,
        [signal(_SIG_NAME, length=16, maximum=8000.0, unit="rpm",
                receivers=receivers)],
    )


class TestDBCSignalReceivers:
    """The SG_ trailing receiver list round-trips through the Agda core."""

    def test_named_receivers_preserved(self) -> None:
        """A signal with explicit receiver nodes round-trips untouched."""
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_signal_receivers(["ECU_A", "ECU_B"])],
            "nodes": [{"name": "ECU_A"}, {"name": "ECU_B"}],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        sig = formatted["messages"][0]["signals"][0]
        assert sig["receivers"] == ["ECU_A", "ECU_B"]

    def test_empty_receivers_default(self) -> None:
        """Absent receivers default to an empty list — no receiver node
        referenced, the field still round-trips as present."""
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_signal_receivers([])],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        sig = formatted["messages"][0]["signals"][0]
        assert sig["receivers"] == []

    def test_unknown_receiver_reported_as_warning(self) -> None:
        """A receiver that isn't a declared BU_ node surfaces a warning.

        The Agda validator's `UnknownSignalReceiver` check compares each
        receiver name against the declared node list.
        """
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_signal_receivers(["GhostECU"])],
            "nodes": [{"name": "ECU_A"}],
        }
        with AletheiaClient() as client:
            validation = client.validate_dbc(original)

        codes = {issue["code"] for issue in validation["issues"]}
        assert "unknown_signal_receiver" in codes


# ---------------------------------------------------------------------------
# Additional message senders (BO_TX_BU_ lines)
# ---------------------------------------------------------------------------


def _msg_with_additional_senders(
    primary: str,
    additional: list[str],
) -> dict:
    return message(
        _MSG_ID,
        _MSG_NAME,
        [signal(_SIG_NAME, length=16, maximum=8000.0, unit="rpm")],
        sender=primary,
        senders=additional,
    )


class TestDBCMessageSenders:
    """The BO_TX_BU_ additional-transmitter list round-trips through the core.

    ``sender`` carries the singular BO_ primary; ``senders`` carries only the
    BO_TX_BU_ extras. The two vocabularies stay separate so the Agda validator
    can report unknown additional transmitters without shadowing the primary
    sender's own check.
    """

    def test_additional_senders_preserved(self) -> None:
        """Explicit additional transmitters round-trip untouched."""
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_additional_senders("ECU_A", ["ECU_B", "ECU_C"])],
            "nodes": [{"name": "ECU_A"}, {"name": "ECU_B"}, {"name": "ECU_C"}],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        msg = formatted["messages"][0]
        assert msg["sender"] == "ECU_A"
        assert msg["senders"] == ["ECU_B", "ECU_C"]

    def test_empty_senders_default(self) -> None:
        """Absent BO_TX_BU_ line round-trips as an empty ``senders`` list."""
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_additional_senders("ECU_A", [])],
            "nodes": [{"name": "ECU_A"}],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        msg = formatted["messages"][0]
        assert msg["sender"] == "ECU_A"
        assert msg["senders"] == []

    def test_unknown_additional_sender_reported_as_warning(self) -> None:
        """An additional sender not in BU_ surfaces an ``unknown_message_sender``
        warning, disambiguated by the "additional sender" phrasing.

        The Agda validator reuses ``UnknownMessageSender`` for both the primary
        ``sender`` and each BO_TX_BU_ entry — same conceptual check ("node
        referenced but not declared"), single wire code.
        """
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_additional_senders("ECU_A", ["GhostECU"])],
            "nodes": [{"name": "ECU_A"}],
        }
        with AletheiaClient() as client:
            validation = client.validate_dbc(original)

        matching = [
            issue for issue in validation["issues"]
            if issue["code"] == "unknown_message_sender"
            and "additional sender" in issue["detail"]
            and "GhostECU" in issue["detail"]
        ]
        assert matching, validation["issues"]


# ---------------------------------------------------------------------------
# Per-signal VAL_ value descriptions (Phase E)
# ---------------------------------------------------------------------------


def _msg_with_signal_value_descriptions(entries: list[dict]) -> dict:
    sig = signal(_SIG_NAME, length=16, maximum=8000.0, unit="rpm")
    sig["valueDescriptions"] = entries
    return message(_MSG_ID, _MSG_NAME, [sig])


class TestDBCSignalValueDescriptions:
    """Phase E — VAL_ entries land on DBCSignal.valueDescriptions and round-trip
    through the Agda core both at the JSON and at the .dbc text wire."""

    def test_value_descriptions_preserved(self) -> None:
        """A non-empty per-signal valueDescriptions list survives parse_dbc →
        format_dbc round-trip with order and content intact."""
        entries = [
            {"value": 0, "description": "Off"},
            {"value": 1, "description": "On"},
            {"value": 2, "description": "Standby"},
        ]
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_signal_value_descriptions(entries)],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        sig = formatted["messages"][0]["signals"][0]
        assert sig["valueDescriptions"] == entries

    def test_empty_value_descriptions_default(self) -> None:
        """Absent valueDescriptions round-trips as an empty list — the field is
        always present on the wire even when no VAL_ block applies."""
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_signal_value_descriptions([])],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            formatted = client.format_dbc()

        sig = formatted["messages"][0]["signals"][0]
        assert sig["valueDescriptions"] == []

    def test_format_dbc_text_emits_val_block(self) -> None:
        """format_dbc_text emits a VAL_ line when a signal carries
        valueDescriptions, with entries in declaration order."""
        entries = [
            {"value": 0, "description": "Off"},
            {"value": 1, "description": "On"},
        ]
        original: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_with_signal_value_descriptions(entries)],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success", result
            text = client.format_dbc_text(original)

        assert f"VAL_ {_MSG_ID} {_SIG_NAME} 0 \"Off\" 1 \"On\" ;" in text

    def test_unknown_value_description_target_warning(self) -> None:
        """A VAL_ line pointing at a (message-id, signal-name) pair not declared
        in BO_/SG_ surfaces an ``unknown_value_description_target`` warning.

        CHECK 23 walks ``DBC.unresolvedValueDescs`` populated only by
        ``parseText``; the warning is delivered on ``ParsedDBCResponse.warnings``.
        """
        text = (
            'VERSION ""\n\n'
            'NS_ :\n\n'
            'BS_:\n\n'
            'BU_: ECU\n\n'
            'BO_ 256 Engine: 8 ECU\n'
            ' SG_ Rpm : 0|16@1+ (1,0) [0|8000] "rpm" Vector__XXX\n\n'
            'VAL_ 999 GhostSignal 0 "Off" 1 "On" ;\n'
        )
        with AletheiaClient() as client:
            resp = client.parse_dbc_text(text)

        assert resp["status"] == "success", resp
        codes = {issue["code"] for issue in resp["warnings"]}
        assert "unknown_value_description_target" in codes
