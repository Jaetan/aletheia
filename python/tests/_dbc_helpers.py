# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Compact DBC builders used by test modules to avoid duplicate-code.

The JSON shape of a DBC signal is verbose (11 required fields). When every
test module inlines its own literals, pylint R0801 flags the repetition and
the real differences between tests (signal names, bit layouts) get lost in
the boilerplate. These three helpers collapse the boilerplate into keyword
overrides without changing the wire format.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, TypedDict

from aletheia import AletheiaClient
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.protocols import DLCByteCount, to_signal_fraction

if TYPE_CHECKING:
    from fractions import Fraction
    from typing import Unpack

    from aletheia._dbc_types import ByteOrder, SignalPresence
    from aletheia.protocols import DBCDefinition, DBCMessage, DBCSignal, DBCSignalMultiplexed


class SignalOverrides(TypedDict, total=False):
    """Optional keyword overrides for :func:`signal` (all default if absent).

    Public so sibling test modules that wrap :func:`signal` with their own
    defaults can type their forwarding ``**kwargs`` as ``Unpack[SignalOverrides]``
    (e.g. ``test_dbc_validator._make_signal``).
    """

    start_bit: int
    length: int
    byte_order: ByteOrder
    signed: bool
    factor: float | Fraction
    offset: float | Fraction
    minimum: float | Fraction
    maximum: float | Fraction
    unit: str
    presence: SignalPresence
    receivers: list[str]


class _MessageOverrides(TypedDict, total=False):
    """Optional keyword overrides for :func:`message` (all default if absent)."""

    dlc: int
    sender: str
    senders: list[str]


class MuxSignalOverrides(TypedDict, total=False):
    """Optional keyword overrides for :func:`mux_signal` (presence is fixed)."""

    start_bit: int
    length: int
    byte_order: ByteOrder
    signed: bool
    factor: float | Fraction
    offset: float | Fraction
    minimum: float | Fraction
    maximum: float | Fraction
    unit: str
    receivers: list[str]


def signal(name: str, **overrides: Unpack[SignalOverrides]) -> DBCSignal:
    """Build a DBC signal dict with sensible defaults; kwargs override.

    Numeric fields are converted to :class:`Fraction` via
    :func:`to_signal_fraction` to match ``DBCSignalAlways`` exactly (the
    Agda core's exact-rational representation).
    """
    return {
        "name": name,
        "startBit": overrides.get("start_bit", 0),
        "length": overrides.get("length", 16),
        "byteOrder": overrides.get("byte_order", "little_endian"),
        "signed": overrides.get("signed", False),
        "factor": to_signal_fraction(overrides.get("factor", 1)),
        "offset": to_signal_fraction(overrides.get("offset", 0)),
        "minimum": to_signal_fraction(overrides.get("minimum", 0)),
        "maximum": to_signal_fraction(overrides.get("maximum", 65535)),
        "unit": overrides.get("unit", ""),
        "presence": overrides.get("presence", "always"),
        "receivers": overrides.get("receivers", []),
    }


def mux_signal(
    name: str,
    multiplexor: str,
    mux_values: list[int],
    **overrides: Unpack[MuxSignalOverrides],
) -> DBCSignalMultiplexed:
    """Build a multiplexed DBC signal dict (``presence='multiplexed'``).

    The canonical multiplexed wire form carries ``presence='multiplexed'`` plus
    the ``multiplexor`` / ``multiplex_values`` pair.  Centralising the
    constructor here keeps the verbose field block in one place (pylint R0801)
    and mirrors :func:`signal` (defaults + ``to_signal_fraction`` numerics).
    """
    return {
        "name": name,
        "startBit": overrides.get("start_bit", 0),
        "length": overrides.get("length", 8),
        "byteOrder": overrides.get("byte_order", "little_endian"),
        "signed": overrides.get("signed", False),
        "factor": to_signal_fraction(overrides.get("factor", 1)),
        "offset": to_signal_fraction(overrides.get("offset", 0)),
        "minimum": to_signal_fraction(overrides.get("minimum", 0)),
        "maximum": to_signal_fraction(overrides.get("maximum", 255)),
        "unit": overrides.get("unit", ""),
        "presence": "multiplexed",
        "multiplexor": multiplexor,
        "multiplex_values": mux_values,
        "receivers": overrides.get("receivers", []),
    }


def message(
    msg_id: int,
    name: str,
    signals: list[DBCSignal],
    **overrides: Unpack[_MessageOverrides],
) -> DBCMessage:
    """Build a DBC message dict wrapping the given signals."""
    msg: DBCMessage = {
        "id": msg_id,
        "name": name,
        "dlc": DLCByteCount(overrides.get("dlc", 8)),
        "sender": overrides.get("sender", "ECU"),
        "signals": signals,
    }
    if "senders" in overrides:
        msg["senders"] = overrides["senders"]
    return msg


def dbc(messages: list[DBCMessage], version: str = "1.0") -> DBCDefinition:
    """Wrap the given messages in a minimal DBC definition."""
    return {"version": version, "messages": messages, **empty_dbc_tier2()}


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
