"""Structural roundtrip tests for Tier 1 DBC metadata.

Tier 1 covers the three metadata arrays already modeled by the Agda ``DBC``
record but previously dropped by all three bindings: ``signalGroups``,
``environmentVars``, ``valueTables``. Tier 2 (nodes / comments / attributes /
receivers requiring Agda core extension) is tracked separately as B.1.x.

Each test drives ``parse_dbc`` → ``format_dbc`` through the real FFI to prove
the Agda core reconstructs the metadata on the return trip. Equality is
structural, not byte-identical — numeric fields normalise to ``Fraction`` on
the way out, which matches the rest of the Python wire surface.
"""

from __future__ import annotations

from fractions import Fraction

import pytest

from _dbc_helpers import message, signal

from aletheia import AletheiaClient
from aletheia.protocols import (
    DBCDefinition,
    DBCEnvironmentVar,
    DBCSignalGroup,
    DBCValueEntry,
    DBCValueTable,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


def _msg_two_signals() -> dict:
    return message(
        0x100,
        "Engine",
        [
            signal("Rpm", length=16, maximum=8000.0, unit="rpm"),
            signal("Temp", start_bit=16, length=8, maximum=255.0, unit="C"),
        ],
    )


def _full_dbc() -> DBCDefinition:
    """DBC populated with one item of each metadata kind."""
    groups: list[DBCSignalGroup] = [
        {"name": "EngineGroup", "signals": ["Rpm", "Temp"]},
    ]
    env_vars: list[DBCEnvironmentVar] = [
        {
            "name": "AmbientTemp",
            "varType": 1,
            "initial": Fraction(0),
            "minimum": Fraction(-40),
            "maximum": Fraction(120),
        },
    ]
    value_tables: list[DBCValueTable] = [
        {
            "name": "GearStates",
            "entries": [
                {"value": 0, "description": "Park"},
                {"value": 1, "description": "Reverse"},
                {"value": 2, "description": "Neutral"},
                {"value": 3, "description": "Drive"},
            ],
        },
    ]
    return {
        "version": "1.0",
        "messages": [_msg_two_signals()],
        "signalGroups": groups,
        "environmentVars": env_vars,
        "valueTables": value_tables,
    }


def _empty_metadata_dbc() -> DBCDefinition:
    """DBC with explicit empty metadata arrays — proves the empty case
    survives the wire even when keys are supplied."""
    return {
        "version": "1.0",
        "messages": [_msg_two_signals()],
        "signalGroups": [],
        "environmentVars": [],
        "valueTables": [],
    }


def _no_metadata_keys_dbc() -> DBCDefinition:
    """Pre-Tier-1 shape — no NotRequired keys at all. The parser has to treat
    absent keys as empty and ``format_dbc`` has to still emit the arrays."""
    return {
        "version": "1.0",
        "messages": [_msg_two_signals()],
    }


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class TestDBCMetadataTier1Roundtrip:
    """parse_dbc → format_dbc preserves all three Tier 1 metadata arrays."""

    def test_full_metadata_survives(self) -> None:
        """Every populated metadata entry round-trips structurally."""
        original = _full_dbc()
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success"
            formatted = client.format_dbc()

        groups = formatted["signalGroups"]
        assert groups == original["signalGroups"]

        env_vars = formatted["environmentVars"]
        assert env_vars == original["environmentVars"]

        value_tables = formatted["valueTables"]
        assert value_tables == original["valueTables"]

    def test_empty_metadata_survives(self) -> None:
        """Explicit empty arrays round-trip as empty arrays, not missing keys."""
        original = _empty_metadata_dbc()
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success"
            formatted = client.format_dbc()

        assert formatted["signalGroups"] == []
        assert formatted["environmentVars"] == []
        assert formatted["valueTables"] == []

    def test_absent_metadata_keys_default_to_empty(self) -> None:
        """A pre-Tier-1 input (no NotRequired keys) is accepted and produces
        empty arrays on the way out — the widened shape is backward-compatible
        with hand-written fixtures."""
        original = _no_metadata_keys_dbc()
        with AletheiaClient() as client:
            result = client.parse_dbc(original)
            assert result["status"] == "success"
            formatted = client.format_dbc()

        assert formatted["signalGroups"] == []
        assert formatted["environmentVars"] == []
        assert formatted["valueTables"] == []

    def test_numeric_env_var_fields_are_fractions(self) -> None:
        """Environment-variable numeric fields use ``Fraction`` on the way out,
        matching the ``DBCSignal`` wire contract (exact rational precision)."""
        original = _full_dbc()
        with AletheiaClient() as client:
            client.parse_dbc(original)
            formatted = client.format_dbc()

        ev = formatted["environmentVars"][0]
        assert isinstance(ev["initial"], Fraction)
        assert isinstance(ev["minimum"], Fraction)
        assert isinstance(ev["maximum"], Fraction)
        assert ev["varType"] == 1

    def test_value_table_entries_preserved_in_order(self) -> None:
        """Value-table entries round-trip in insertion order (DBC source order)."""
        original = _full_dbc()
        with AletheiaClient() as client:
            client.parse_dbc(original)
            formatted = client.format_dbc()

        entries = formatted["valueTables"][0]["entries"]
        assert [e["value"] for e in entries] == [0, 1, 2, 3]
        assert [e["description"] for e in entries] == [
            "Park",
            "Reverse",
            "Neutral",
            "Drive",
        ]


# ---------------------------------------------------------------------------
# Negative / edge cases
# ---------------------------------------------------------------------------


class TestDBCMetadataTier1Rejects:
    """Malformed metadata values should be rejected by the Agda parser."""

    def test_invalid_var_type_rejected(self) -> None:
        """``varType`` outside {0, 1, 2} must be rejected by the Agda parser."""
        bad: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_two_signals()],
            "environmentVars": [
                {
                    "name": "Bad",
                    "varType": 7,  # type: ignore[typeddict-item]  # intentional wire violation
                    "initial": Fraction(0),
                    "minimum": Fraction(0),
                    "maximum": Fraction(1),
                },
            ],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(bad)
        assert result["status"] == "error"

    def test_signal_group_referring_to_unknown_signal_accepted(self) -> None:
        """The Agda parser does not cross-check group signal references against
        message signals — the field is opaque, so dangling references round-
        trip unchanged. (Validation of references, if added later, is a
        validator concern, not a parser concern.)"""
        dangling: DBCDefinition = {
            "version": "1.0",
            "messages": [_msg_two_signals()],
            "signalGroups": [
                {"name": "Dangling", "signals": ["NotARealSignal"]},
            ],
        }
        with AletheiaClient() as client:
            result = client.parse_dbc(dangling)
            if result["status"] != "success":
                pytest.fail(
                    f"Expected opaque acceptance, got error: {result}"
                )
            formatted = client.format_dbc()

        assert formatted["signalGroups"] == dangling["signalGroups"]


# ---------------------------------------------------------------------------
# Value entries with special characters
# ---------------------------------------------------------------------------


def test_value_table_description_with_spaces() -> None:
    """Spaces in descriptions round-trip as-is.

    Value-table descriptions in DBC are single-word tokens in the source
    format but cantools exposes them as arbitrary strings — our wire contract
    preserves whatever cantools produced.
    """
    spacey: DBCDefinition = {
        "version": "1.0",
        "messages": [_msg_two_signals()],
        "valueTables": [
            {
                "name": "Verbose",
                "entries": [
                    {"value": 0, "description": "off with trailing"},
                    {"value": 1, "description": "on"},
                ],
            },
        ],
    }
    with AletheiaClient() as client:
        client.parse_dbc(spacey)
        formatted = client.format_dbc()

    entries: list[DBCValueEntry] = formatted["valueTables"][0]["entries"]
    assert entries[0]["description"] == "off with trailing"
    assert entries[1]["description"] == "on"
