"""
Convert .dbc files to JSON format for Aletheia JSON streaming protocol.

Uses cantools to parse .dbc files and converts them to the JSON structure
expected by Aletheia.DBC.JSONParser.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from .protocols import (
    DBCSignal,
    DBCMessage,
    DBCDefinition,
)

import cantools
import cantools.database.can


def signal_to_json(signal: cantools.database.can.Signal) -> DBCSignal:
    """Convert a cantools Signal to JSON format."""

    # Convert byte order
    byte_order = "little_endian" if signal.byte_order == "little_endian" else "big_endian"

    # cantools uses is_signed, we use "signed" field
    is_signed = signal.is_signed

    # cantools may return None for min/max, use reasonable defaults
    min_value = signal.minimum if signal.minimum is not None else 0.0
    max_value = signal.maximum if signal.maximum is not None else 0.0

    # Base signal fields common to all signal types
    base_fields = {
        "name": signal.name,
        "startBit": signal.start,
        "length": signal.length,
        "byteOrder": byte_order,
        "signed": is_signed,
        "factor": signal.scale,
        "offset": signal.offset,
        "minimum": min_value,
        "maximum": max_value,
        "unit": signal.unit if signal.unit else "",
    }

    # Handle multiplexing: check if signal has multiplexer_ids
    if signal.multiplexer_ids is not None and len(signal.multiplexer_ids) > 0:
        # This is a multiplexed signal - use first multiplexer value
        multiplexor_name = signal.multiplexer_signal if signal.multiplexer_signal else "unknown"
        return cast(DBCSignal, {
            **base_fields,
            "multiplexor": multiplexor_name,
            "multiplex_value": signal.multiplexer_ids[0]
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
    """
    Convert a .dbc file to JSON format.

    Args:
        dbc_path: Path to the .dbc file

    Returns:
        DBC definition in the format expected by Aletheia.DBC.JSONParser
    """
    # Load DBC file using cantools
    db = cantools.database.load_file(str(dbc_path))

    # Convert to JSON structure
    dbc_def: DBCDefinition = {
        "version": db.version if db.version else "1.0",
        "messages": [message_to_json(msg) for msg in db.messages]
    }
    return dbc_def


def convert_dbc_file(dbc_path: str | Path, output_path: str | Path | None = None) -> str:
    """
    Convert a .dbc file to JSON and optionally write to file.

    Args:
        dbc_path: Path to the .dbc file
        output_path: Optional path to write JSON output. If None, returns JSON string.

    Returns:
        JSON string representation of the DBC file
    """
    dbc_json = dbc_to_json(dbc_path)
    json_str = json.dumps(dbc_json, indent=2)

    if output_path:
        _ = Path(output_path).write_text(json_str, encoding='utf-8')

    return json_str


if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Usage: python -m aletheia.dbc_converter <input.dbc> [output.json]")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None

    json_output = convert_dbc_file(input_file, output_file)

    if output_file:
        print(f"Converted {input_file} to {output_file}")
    else:
        print(json_output)
