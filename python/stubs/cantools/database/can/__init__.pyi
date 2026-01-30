"""Type stubs for cantools.database.can module."""

from typing import Literal

class Signal:
    """CAN signal definition from a DBC file."""
    name: str
    start: int
    length: int
    byte_order: Literal["little_endian", "big_endian"]
    is_signed: bool
    scale: float
    offset: float
    minimum: float | None
    maximum: float | None
    unit: str | None
    multiplexer_ids: list[int] | None
    multiplexer_signal: str | None

class Message:
    """CAN message definition from a DBC file."""
    frame_id: int
    name: str
    length: int
    senders: list[str]
    signals: list[Signal]
    is_extended_frame: bool
