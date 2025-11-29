"""
Convert .dbc files to JSON format for Aletheia JSON streaming protocol.

Uses cantools to parse .dbc files and converts them to the JSON structure
expected by Aletheia.DBC.JSONParser.
"""

import json
from pathlib import Path
from typing import Any, Dict, List

try:
    import cantools
except ImportError:
    raise ImportError(
        "cantools is required for DBC conversion. "
        "Install it with: pip install cantools"
    )


def signal_to_json(signal: cantools.database.can.Signal) -> Dict[str, Any]:
    """Convert a cantools Signal to JSON format."""

    # Determine signal presence (multiplexing)
    # cantools represents multiplexed signals differently
    if signal.multiplexer_ids is not None:
        # This is a multiplexed signal
        # For simplicity, use the first multiplexer value if available
        multiplex_ids = signal.multiplexer_ids
        if isinstance(multiplex_ids, list) and len(multiplex_ids) > 0:
            # Use first multiplexer value
            presence = {
                "multiplexor": signal.multiplexer_signal,
                "multiplex_value": multiplex_ids[0]
            }
        else:
            # Multiplexer but no specific value - treat as always present
            presence = {"presence": "always"}
    else:
        # Normal signal, always present
        presence = {"presence": "always"}

    # Convert byte order
    byte_order = "little_endian" if signal.byte_order == "little_endian" else "big_endian"

    # cantools uses is_signed, we use "signed" field
    is_signed = signal.is_signed

    return {
        "name": signal.name,
        "startBit": signal.start,
        "length": signal.length,
        "byteOrder": byte_order,
        "signed": is_signed,
        "factor": signal.scale,
        "offset": signal.offset,
        "minimum": signal.minimum,
        "maximum": signal.maximum,
        "unit": signal.unit if signal.unit else "",
        **presence  # Unpack presence dict
    }


def message_to_json(message: cantools.database.can.Message) -> Dict[str, Any]:
    """Convert a cantools Message to JSON format."""

    # Determine if CAN ID is extended
    is_extended = message.is_extended_frame

    msg_json = {
        "id": message.frame_id,
        "name": message.name,
        "dlc": message.length,
        "sender": message.senders[0] if message.senders else "",
        "signals": [signal_to_json(sig) for sig in message.signals]
    }

    # Add extended field if needed
    if is_extended:
        msg_json["extended"] = True

    return msg_json


def dbc_to_json(dbc_path: str | Path) -> Dict[str, Any]:
    """
    Convert a .dbc file to JSON format.

    Args:
        dbc_path: Path to the .dbc file

    Returns:
        Dictionary in the format expected by Aletheia.DBC.JSONParser
    """
    # Load DBC file using cantools
    db = cantools.database.load_file(str(dbc_path))

    # Convert to JSON structure
    return {
        "version": db.version if db.version else "1.0",
        "messages": [message_to_json(msg) for msg in db.messages]
    }


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
        Path(output_path).write_text(json_str)

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
