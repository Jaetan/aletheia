"""Multiplexing query helpers and DBC definition lookup utilities.

These functions operate on the DBCMessage / DBCDefinition TypedDicts
from :mod:`aletheia.protocols` and provide the same functionality as the
Go ``DbcMessage`` methods (``IsMultiplexed``, ``AlwaysPresentSignals``, etc.).
"""

from __future__ import annotations

from typing import cast

from .protocols import DBCDefinition, DBCMessage, DBCSignal, DBCSignalMultiplexed


def is_multiplexed(msg: DBCMessage) -> bool:
    """Return True if the message contains any multiplexed signals."""
    return any(
        s.get("multiplexor") is not None for s in msg["signals"]
    )


def always_present_signals(msg: DBCMessage) -> list[DBCSignal]:
    """Return signals that are present in every frame (not multiplexed)."""
    return [s for s in msg["signals"] if s.get("multiplexor") is None]


def multiplexed_signals(msg: DBCMessage) -> list[DBCSignal]:
    """Return signals that are conditionally present (multiplexed)."""
    return [s for s in msg["signals"] if s.get("multiplexor") is not None]


def multiplexor_names(msg: DBCMessage) -> list[str]:
    """Return distinct multiplexor signal names, in order of first occurrence."""
    seen: set[str] = set()
    out: list[str] = []
    for s in msg["signals"]:
        mux = s.get("multiplexor")
        if mux is not None and mux not in seen:
            seen.add(mux)
            out.append(mux)
    return out


def mux_values(msg: DBCMessage, multiplexor: str) -> list[int]:
    """Return all multiplex values for the given multiplexor, in order of first occurrence."""
    seen: set[int] = set()
    out: list[int] = []
    for s in msg["signals"]:
        if s.get("multiplexor") == multiplexor:
            v = cast(DBCSignalMultiplexed, s)["multiplex_value"]
            if v not in seen:
                seen.add(v)
                out.append(v)
    return out


def signals_for_mux_value(
    msg: DBCMessage, multiplexor: str, value: int
) -> list[DBCSignal]:
    """Return signals present when the multiplexor has the given value.

    Includes all always-present signals plus multiplexed signals matching
    the multiplexor and value.
    """
    out: list[DBCSignal] = []
    for s in msg["signals"]:
        mux = s.get("multiplexor")
        if mux is None:
            out.append(s)
        elif mux == multiplexor and cast(DBCSignalMultiplexed, s)["multiplex_value"] == value:
            out.append(s)
    return out


def message_by_id(
    dbc: DBCDefinition, can_id: int, *, extended: bool = False
) -> DBCMessage | None:
    """Return the first message with the given CAN ID, or None if not found."""
    for msg in dbc["messages"]:
        if msg["id"] == can_id and msg.get("extended", False) == extended:
            return msg
    return None


def message_by_name(dbc: DBCDefinition, name: str) -> DBCMessage | None:
    """Return the first message with the given name, or None if not found."""
    for msg in dbc["messages"]:
        if msg["name"] == name:
            return msg
    return None


def signal_by_name(msg: DBCMessage, name: str) -> DBCSignal | None:
    """Return the first signal with the given name, or None if not found."""
    for s in msg["signals"]:
        if s["name"] == name:
            return s
    return None
