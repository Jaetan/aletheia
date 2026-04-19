"""
Convert between .dbc files, JSON, and DBC text format.

- ``dbc_to_json``: Parse .dbc file to JSON (via cantools).
- ``dbc_to_text``: Convert JSON dict back to .dbc text.
- ``convert_dbc_file``: Parse .dbc to JSON string, optionally write to file.
"""

from fractions import Fraction
from pathlib import Path
from typing import cast

import cantools
import cantools.database.can

from .client._helpers import dump_json, to_signal_fraction
from .protocols import (
    DBCSignal,
    DBCMessage,
    DBCDefinition,
)

# CAN Extended Frame Format flag — bit 31 set to distinguish 29-bit extended
# IDs from 11-bit standard IDs in .dbc file format.
_CAN_EFF_FLAG = 0x80000000


def signal_to_json(signal: cantools.database.can.Signal) -> DBCSignal:
    """Convert a cantools Signal to JSON format."""

    # Validate byte order
    byte_order = signal.byte_order
    if byte_order not in ("little_endian", "big_endian"):
        raise ValueError(
            f"Unknown byte order {byte_order!r} for signal {signal.name!r}"
        )

    # cantools uses is_signed, we use "signed" field
    is_signed = signal.is_signed

    # cantools may return None for min/max, use reasonable defaults
    min_value = signal.minimum if signal.minimum is not None else 0.0
    max_value = signal.maximum if signal.maximum is not None else 0.0

    # Base signal fields common to all signal types. Numeric fields are
    # converted to Fraction to match DBCSignal's typed contract — the Agda
    # core works in ℚ and to_signal_fraction preserves decimal intent
    # (0.1 → 1/10) rather than the IEEE-754 binary approximation.
    base_fields = {
        "name": signal.name,
        "startBit": signal.start,
        "length": signal.length,
        "byteOrder": byte_order,
        "signed": is_signed,
        "factor": to_signal_fraction(signal.scale),
        "offset": to_signal_fraction(signal.offset),
        "minimum": to_signal_fraction(min_value),
        "maximum": to_signal_fraction(max_value),
        "unit": signal.unit if signal.unit else "",
    }

    # Handle multiplexing: check if signal has multiplexer_ids
    if signal.multiplexer_ids:
        multiplexor_name = signal.multiplexer_signal if signal.multiplexer_signal else "unknown"
        return cast(DBCSignal, {
            **base_fields,
            "multiplexor": multiplexor_name,
            "multiplex_values": list(signal.multiplexer_ids)
        })

    # Default: signal is always present
    return cast(DBCSignal, {
        **base_fields,
        "presence": "always"
    })


def message_to_json(message: cantools.database.can.Message) -> DBCMessage:
    """Convert a cantools Message to JSON format."""

    message_dict: DBCMessage = {
        "id": message.frame_id,
        "name": message.name,
        "dlc": message.length,
        "sender": message.senders[0] if message.senders else "",
        "signals": [signal_to_json(sig) for sig in message.signals]
    }

    # Add extended field if this is an extended frame (29-bit ID)
    if message.is_extended_frame:
        message_dict["extended"] = True

    return message_dict


def dbc_to_json(dbc_path: str | Path) -> DBCDefinition:
    """Convert a .dbc file to JSON format.

    Args:
        dbc_path: Path to the .dbc file

    Returns:
        DBC definition in the format expected by Aletheia.DBC.JSONParser

    Raises:
        OSError: If the file cannot be read.
        ValueError: If the file is not a valid DBC.
    """
    # Load DBC file using cantools
    try:
        db = cantools.database.load_file(str(dbc_path))
    except OSError:
        raise
    except Exception as exc:
        raise ValueError(f"Failed to parse DBC file '{dbc_path}': {exc}") from exc

    # Convert to JSON structure
    dbc_def: DBCDefinition = {
        "version": db.version if db.version else "1.0",
        "messages": [message_to_json(msg) for msg in db.messages]
    }
    return dbc_def


def _format_number(value: float | Fraction) -> str:
    """Format a numeric signal field for DBC output.

    Fractions exactly representable as integers emit as ``"int"``; other
    Fractions emit as a 15-digit decimal via float conversion (DBC's text
    format is decimal-only, so exact rational preservation is impossible
    at this layer — this matches cantools' .dbc output convention).
    """
    if isinstance(value, Fraction):
        if value.denominator == 1:
            return str(value.numerator)
        return f"{float(value):.15g}"
    if value.is_integer():
        return str(int(value))
    return f"{value:.15g}"


def _signal_to_dbc_line(
    signal: DBCSignal,
    mux_signal_names: set[str] | None = None,
) -> str:
    """Format a single signal as a DBC SG_ line."""
    name = signal["name"]
    start_bit = signal["startBit"]
    length = signal["length"]

    # Byte order: 1 = little_endian, 0 = big_endian
    bo = "1" if signal["byteOrder"] == "little_endian" else "0"

    # Sign: + = unsigned, - = signed
    sign = "-" if signal["signed"] else "+"

    factor = _format_number(signal["factor"])
    offset = _format_number(signal["offset"])
    minimum = _format_number(signal["minimum"])
    maximum = _format_number(signal["maximum"])
    unit = signal["unit"]

    # Multiplexing indicator: M for multiplexor, m<val> for multiplexed
    # Standard DBC format only supports a single mux value in the SG_ line;
    # extended mux (SG_MUL_VAL_) is not emitted here. Take the first value.
    mux_indicator = ""
    if "multiplexor" in signal:
        mux_vals = signal["multiplex_values"]
        mux_indicator = f" m{mux_vals[0]}"
    elif mux_signal_names and name in mux_signal_names:
        mux_indicator = " M"

    # Vector__XXX is the DBC convention for "no specific receiver node".
    # Aletheia's signal model does not preserve receiver info from the original
    # DBC, so all exported signals use this placeholder.
    return (
        f" SG_ {name}{mux_indicator} : "
        f"{start_bit}|{length}@{bo}{sign} "
        f"({factor},{offset}) "
        f"[{minimum}|{maximum}] "
        f'"{unit}" Vector__XXX'
    )


def dbc_to_text(dbc: DBCDefinition) -> str:
    """Convert a DBC JSON dict to .dbc file text format.

    Args:
        dbc: DBC definition dict (as returned by ``dbc_to_json()``
             or ``AletheiaClient.format_dbc()``).

    Returns:
        String containing the .dbc file content.
    """
    lines: list[str] = []

    # VERSION
    version = dbc.get("version", "")
    lines.append(f'VERSION "{version}"')
    lines.append("")

    # NS_ (stub)
    lines.append("NS_ :")
    lines.append("")

    # BS_ (stub)
    lines.append("BS_:")
    lines.append("")

    # BU_ — collect unique senders from messages
    senders: list[str] = []
    seen_senders: set[str] = set()
    for msg in dbc["messages"]:
        sender = msg.get("sender", "")
        if sender and sender not in seen_senders:
            senders.append(sender)
            seen_senders.add(sender)
    lines.append("BU_: " + " ".join(senders))
    lines.append("")

    # Messages
    for msg in dbc["messages"]:
        msg_id = msg["id"]
        if msg.get("extended"):
            msg_id = msg_id | _CAN_EFF_FLAG
        msg_name = msg["name"]
        dlc = msg["dlc"]
        sender = msg.get("sender", "")

        lines.append(f"BO_ {msg_id} {msg_name}: {dlc} {sender}")

        # Collect multiplexor signal names referenced by multiplexed signals
        mux_signal_names: set[str] = set()
        for signal in msg.get("signals", []):
            if "multiplexor" in signal:
                mux_signal_names.add(signal["multiplexor"])

        for signal in msg.get("signals", []):
            lines.append(_signal_to_dbc_line(signal, mux_signal_names))

        lines.append("")

    return "\n".join(lines)


def convert_dbc_file(dbc_path: str | Path, output_path: str | Path | None = None) -> str:
    """Convert a .dbc file to JSON and optionally write to file.

    Args:
        dbc_path: Path to the .dbc file
        output_path: Optional path to write JSON output. If None, returns JSON string.

    Returns:
        JSON string representation of the DBC file
    """
    dbc_json = dbc_to_json(dbc_path)
    json_str = dump_json(dbc_json, indent=2)

    if output_path:
        _ = Path(output_path).write_text(json_str, encoding='utf-8')

    return json_str
