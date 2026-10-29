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

import json
from fractions import Fraction
from typing import TYPE_CHECKING, NewType, TypedDict

from aletheia import AletheiaClient
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.types import DLCByteCount, DLCCode, JSONValue

if TYPE_CHECKING:
    from typing import Unpack

    from aletheia import SignalExtractionResult
    from aletheia._dbc_types import ByteOrder, SignalName, SignalPresence
    from aletheia.types import DBCDefinition, DBCMessage, DBCSignal, DBCSignalMultiplexed


# A kernel reply's bytes, as a stand-in backend answers a command with them.
KernelReply = NewType("KernelReply", bytes)


class SignalOverrides(TypedDict, total=False):
    """Optional keyword overrides for :func:`signal` (all default if absent).

    Public so sibling test modules that wrap :func:`signal` with their own
    defaults can type their forwarding ``**kwargs`` as ``Unpack[SignalOverrides]``
    (e.g. ``_validator_helpers.make_signal``).
    """

    start_bit: int
    length: int
    byte_order: ByteOrder
    signed: bool
    factor: int | Fraction
    offset: int | Fraction
    minimum: int | Fraction
    maximum: int | Fraction
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
    factor: int | Fraction
    offset: int | Fraction
    minimum: int | Fraction
    maximum: int | Fraction
    unit: str
    receivers: list[str]


def signal(name: str, **overrides: Unpack[SignalOverrides]) -> DBCSignal:
    """Build a DBC signal dict with sensible defaults; kwargs override.

    Numeric override fields are exact ``int``/``Fraction`` inputs (the float
    principle); they are wrapped in :class:`Fraction` to match
    ``DBCSignalAlways`` exactly (the Agda core's exact-rational representation).
    """
    return {
        "name": name,
        "startBit": overrides.get("start_bit", 0),
        "length": overrides.get("length", 16),
        "byteOrder": overrides.get("byte_order", "little_endian"),
        "signed": overrides.get("signed", False),
        "factor": Fraction(overrides.get("factor", 1)),
        "offset": Fraction(overrides.get("offset", 0)),
        "minimum": Fraction(overrides.get("minimum", 0)),
        "maximum": Fraction(overrides.get("maximum", 65535)),
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
    and mirrors :func:`signal` (defaults + exact ``Fraction`` numerics).
    """
    return {
        "name": name,
        "startBit": overrides.get("start_bit", 0),
        "length": overrides.get("length", 8),
        "byteOrder": overrides.get("byte_order", "little_endian"),
        "signed": overrides.get("signed", False),
        "factor": Fraction(overrides.get("factor", 1)),
        "offset": Fraction(overrides.get("offset", 0)),
        "minimum": Fraction(overrides.get("minimum", 0)),
        "maximum": Fraction(overrides.get("maximum", 255)),
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


def kernel_signal(name: SignalName) -> JSONValue:
    """Return an always-present 8-bit signal as the kernel's reply writes one."""
    return {
        "name": name,
        "startBit": 0,
        "length": 8,
        "factor": 1,
        "offset": 0,
        "minimum": 0,
        "maximum": 255,
        "presence": "always",
    }


def parse_dbc_reply(*messages: JSONValue) -> KernelReply:
    """Return the kernel's parseDBC success reply holding ``messages``, every other list empty."""
    body: JSONValue = {
        "version": "",
        "messages": list(messages),
        **{key: list[JSONValue]() for key in empty_dbc_tier2()},
    }
    reply: JSONValue = {"status": "success", "dbc": body, "warnings": list[JSONValue]()}
    return KernelReply(json.dumps(reply).encode())


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


# A CAN-FD frame's 64 data bytes, read as one little-endian number.
FrameNumber = NewType("FrameNumber", int)


def extract_fd(sig: DBCSignal, frame: FrameNumber) -> SignalExtractionResult:
    """Load one 64-byte CAN-FD message 0x300 holding ``sig`` and extract it from ``frame``."""
    with AletheiaClient() as client:
        parsed = client.parse_dbc(dbc([message(0x300, "Fd", [sig], dlc=64)]))
        assert parsed["status"] == "success", parsed
        return client.extract_signals(
            can_id=0x300, dlc=DLCCode(15), data=bytearray(frame.to_bytes(64, "little"))
        )
