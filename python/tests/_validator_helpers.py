# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The DBC builders the validator tests share, with the validator's signal defaults."""

from __future__ import annotations

from typing import TYPE_CHECKING, Unpack

from _dbc_helpers import SignalOverrides, mux_signal
from _dbc_helpers import dbc as _build_dbc
from _dbc_helpers import message as _build_msg
from _dbc_helpers import signal as _build_sig

if TYPE_CHECKING:
    from aletheia import DBCDefinition
    from aletheia.types import DBCMessage, DBCSignal, DBCSignalMultiplexed

# Validator tests default to 8-bit signals ranged 0..255, matching the
# narrow signals most DBC structural-validation cases exercise.
_VALIDATOR_DEFAULTS: SignalOverrides = {"length": 8, "maximum": 255}


def make_dbc(messages: list[DBCMessage]) -> DBCDefinition:
    """Build a minimal DBC with given messages."""
    return _build_dbc(messages)


def make_message(
    msg_id: int,
    name: str,
    signals: list[DBCSignal] | None = None,
    *,
    dlc: int = 8,
    sender: str = "ECU",
) -> DBCMessage:
    """Build a DBC message."""
    return _build_msg(msg_id, name, signals or [], dlc=dlc, sender=sender)


def make_signal(name: str, **overrides: Unpack[SignalOverrides]) -> DBCSignal:
    """Build an 8-bit byte-aligned signal with validator-friendly defaults."""
    merged: SignalOverrides = {**_VALIDATOR_DEFAULTS, **overrides}
    return _build_sig(name, **merged)


def make_mux_signal(
    name: str,
    multiplexor: str,
    mux_value: int,
    *,
    start_bit: int = 0,
    length: int = 8,
) -> DBCSignalMultiplexed:
    """Build a multiplexed DBC signal."""
    return mux_signal(name, multiplexor, [mux_value], start_bit=start_bit, length=length)


def single_message_dbc(signals: list[DBCSignal], *, dlc: int = 8) -> DBCDefinition:
    """Build a DBC holding one message, ``Msg1`` at ``0x100``, carrying ``signals``."""
    return make_dbc([make_message(0x100, "Msg1", signals, dlc=dlc)])
