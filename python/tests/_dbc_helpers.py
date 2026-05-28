"""Compact DBC builders used by test modules to avoid duplicate-code.

The JSON shape of a DBC signal is verbose (11 required fields). When every
test module inlines its own literals, pylint R0801 flags the repetition and
the real differences between tests (signal names, bit layouts) get lost in
the boilerplate. These three helpers collapse the boilerplate into keyword
overrides without changing the wire format.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from aletheia import AletheiaClient

if TYPE_CHECKING:
    from aletheia.protocols import DBCDefinition


def signal(name: str, **overrides: object) -> dict:
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


def message(msg_id: int, name: str, signals: list[dict], **overrides: object) -> dict:
    """Build a DBC message dict wrapping the given signals."""
    msg: dict = {
        "id": msg_id,
        "name": name,
        "dlc": overrides.get("dlc", 8),
        "sender": overrides.get("sender", "ECU"),
        "signals": signals,
    }
    if "senders" in overrides:
        msg["senders"] = overrides["senders"]
    return msg


def dbc(messages: list[dict], version: str = "1.0") -> DBCDefinition:
    """Wrap the given messages in a minimal DBC definition."""
    return {"version": version, "messages": messages}


def assert_non_terminating_rational(bad: DBCDefinition, field: str) -> None:
    """Parse ``bad`` and assert it raises the non-terminating-rational error.

    Tier 1 (SG_/EV_) and Tier 2 (BA_/BA_DEF_) tests both exercise the
    ``parse_non_terminating_rational`` rejection path with the same
    parse-result-shape assertion.  Inlining the block in two places trips
    pylint's R0801 duplicate-code; this helper keeps the assertion contract
    in one place.
    """
    with AletheiaClient() as client:
        result = client.parse_dbc(bad)
    assert result["status"] == "error"
    assert result["code"] == "parse_non_terminating_rational"
    assert field in result["message"]
