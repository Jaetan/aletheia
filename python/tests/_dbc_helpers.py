"""Compact DBC builders used by test modules to avoid duplicate-code.

The JSON shape of a DBC signal is verbose (11 required fields). When every
test module inlines its own literals, pylint R0801 flags the repetition and
the real differences between tests (signal names, bit layouts) get lost in
the boilerplate. These three helpers collapse the boilerplate into keyword
overrides without changing the wire format.
"""

from __future__ import annotations

from typing import Any

from aletheia.protocols import DBCDefinition


def signal(name: str, **overrides: Any) -> dict:
    """Build a DBC signal dict with sensible defaults; kwargs override."""
    return {
        "name": name,
        "startBit": overrides.get("start_bit", 0),
        "length": overrides.get("length", 16),
        "byteOrder": overrides.get("byte_order", "little_endian"),
        "signed": overrides.get("signed", False),
        "factor": overrides.get("factor", 1.0),
        "offset": overrides.get("offset", 0.0),
        "minimum": overrides.get("minimum", 0.0),
        "maximum": overrides.get("maximum", 65535.0),
        "unit": overrides.get("unit", ""),
        "presence": overrides.get("presence", "always"),
        "receivers": overrides.get("receivers", []),
    }


def message(msg_id: int, name: str, signals: list[dict], **overrides: Any) -> dict:
    """Build a DBC message dict wrapping the given signals."""
    return {
        "id": msg_id,
        "name": name,
        "dlc": overrides.get("dlc", 8),
        "sender": overrides.get("sender", "ECU"),
        "signals": signals,
    }


def dbc(messages: list[dict], version: str = "1.0") -> DBCDefinition:
    """Wrap the given messages in a minimal DBC definition."""
    return {"version": version, "messages": messages}
