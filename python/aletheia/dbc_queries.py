"""Multiplexing query helpers and DBC definition lookup utilities.

These functions operate on the DBCMessage / DBCDefinition TypedDicts
from :mod:`aletheia.protocols` and provide the same functionality as the
Go ``DBCMessage`` methods (``IsMultiplexed``, ``AlwaysPresentSignals``, etc.).
"""

from typing import TYPE_CHECKING, cast

from aletheia.protocols import DBCDefinition, DBCMessage, DBCSignal

if TYPE_CHECKING:
    from aletheia.protocols import DBCSignalMultiplexed


def is_multiplexed(msg: DBCMessage) -> bool:
    """Return ``True`` when *msg* contains any multiplexed signals.

    A multiplexed signal is one whose presence in a frame depends on the
    value of a multiplexor signal (DBC ``M`` / ``m<value>`` annotations).
    """
    return any(s.get("multiplexor") is not None for s in msg["signals"])


def always_present_signals(msg: DBCMessage) -> list[DBCSignal]:
    """Return the signals that are present in every frame of *msg*.

    Always-present signals have no ``multiplexor`` field — they appear in
    the message body regardless of any multiplexor value.  Complements
    :func:`multiplexed_signals`; their union is ``msg["signals"]``.
    """
    return [s for s in msg["signals"] if s.get("multiplexor") is None]


def multiplexed_signals(msg: DBCMessage) -> list[DBCSignal]:
    """Return the signals whose presence is conditional on a multiplexor.

    A signal is multiplexed when its dict carries a ``multiplexor`` field
    naming the controlling signal and a ``multiplex_values`` list of the
    values that activate it.  Complements :func:`always_present_signals`.
    """
    return [s for s in msg["signals"] if s.get("multiplexor") is not None]


def multiplexor_names(msg: DBCMessage) -> list[str]:
    """Return the distinct multiplexor signal names referenced by *msg*.

    Order is by first occurrence in ``msg["signals"]`` — stable across
    repeated calls and matches the Go binding's ``DBCMessage.
    MultiplexorNames`` output for the same DBC.
    """
    seen: set[str] = set()
    out: list[str] = []
    for s in msg["signals"]:
        mux = s.get("multiplexor")
        if mux is not None and mux not in seen:
            seen.add(mux)
            out.append(mux)
    return out


def mux_values(msg: DBCMessage, multiplexor: str) -> list[int]:
    """Return the multiplex values associated with *multiplexor* in *msg*.

    Values are deduplicated and returned in order of first occurrence
    across the multiplexed signals.  Returns an empty list when no
    multiplexed signal references the named multiplexor.
    """
    seen: set[int] = set()
    out: list[int] = []
    for s in msg["signals"]:
        if s.get("multiplexor") == multiplexor:
            for v in cast("DBCSignalMultiplexed", s)["multiplex_values"]:
                if v not in seen:
                    seen.add(v)
                    out.append(v)
    return out


def signals_for_mux_value(msg: DBCMessage, multiplexor: str, value: int) -> list[DBCSignal]:
    """Return the signals present when *multiplexor* has *value*.

    Includes every always-present signal plus the multiplexed signals
    whose ``multiplex_values`` list contains *value* and whose
    ``multiplexor`` field equals the supplied name.  Mirrors Go's
    ``DBCMessage.SignalsForMuxValue``.
    """
    out: list[DBCSignal] = []
    for s in msg["signals"]:
        mux = s.get("multiplexor")
        if mux is None or (
            mux == multiplexor and value in cast("DBCSignalMultiplexed", s)["multiplex_values"]
        ):
            out.append(s)
    return out


def message_by_id(dbc: DBCDefinition, can_id: int, *, extended: bool = False) -> DBCMessage | None:
    """Look up a message by its CAN ID + extended flag.

    Returns the first matching ``DBCMessage`` dict by linear scan, or
    ``None`` when no message in *dbc* has both ``id == can_id`` and the
    requested extended flag.  Unlike the Go binding the returned dict
    is a reference into *dbc*'s ``messages`` list — mutating it mutates
    the underlying definition.
    """
    for msg in dbc["messages"]:
        if msg["id"] == can_id and msg.get("extended", False) == extended:
            return msg
    return None


def message_by_name(dbc: DBCDefinition, name: str) -> DBCMessage | None:
    """Look up a message by its DBC ``BO_`` name.

    Returns the first matching ``DBCMessage`` dict by linear scan, or
    ``None`` when no message has ``name == name``.  The returned dict
    is a reference into *dbc*'s ``messages`` list (no copy).
    """
    for msg in dbc["messages"]:
        if msg["name"] == name:
            return msg
    return None


def signal_by_name(msg: DBCMessage, name: str) -> DBCSignal | None:
    """Look up a signal by its DBC ``SG_`` name within *msg*.

    Returns the first matching ``DBCSignal`` dict by linear scan, or
    ``None`` when no signal has ``name == name``.  The returned dict
    is a reference into *msg*'s ``signals`` list (no copy).
    """
    for s in msg["signals"]:
        if s["name"] == name:
            return s
    return None
