"""Convert between .dbc files, JSON, and DBC text format.

* ``dbc_to_json``: parse a .dbc file to the Agda wire format via the
  verified Agda text parser (no third-party Python deps).
* ``dbc_to_text``: render a JSON DBC dict back to .dbc text via the
  verified Agda formatter (FFI-delegated, Track E.10).
* ``convert_dbc_file``: ``dbc_to_json`` + write JSON to disk.

All three are thin wrappers over ``AletheiaClient`` operations; the FFI
shared library (``libaletheia-ffi.so``) is the only runtime requirement.
``dbc_to_text`` and ``dbc_to_json`` together form a verified roundtrip:
``dbc_to_json`` ∘ ``dbc_to_text`` is the identity on any well-formed DBC
(Track B.3.d / E.9a universal).
"""

from pathlib import Path

from .client import AletheiaClient
from .client._helpers import dump_json
from .protocols import DBCDefinition, ErrorResponse, ParsedDBCResponse


def dbc_to_json(dbc_path: str | Path) -> DBCDefinition:
    """Convert a .dbc file to JSON format via the verified Agda parser.

    Args:
        dbc_path: Path to the .dbc file.

    Returns:
        DBC definition in the format expected by Aletheia.DBC.JSONParser.

    Raises:
        OSError: If the file cannot be read.
        ValueError: If the file is not a valid DBC.

    Note:
        Each call starts a temporary ``AletheiaClient`` (GHC RTS init) just
        to run ``parseDBCText`` and shuts it down again — fine for ad-hoc
        conversions. For tight loops, drive ``parse_dbc_text`` on a
        long-lived ``AletheiaClient`` directly instead.
    """
    text = Path(dbc_path).read_text(encoding="utf-8")
    with AletheiaClient() as client:
        response: ParsedDBCResponse | ErrorResponse = client.parse_dbc_text(text)
    if response["status"] == "error":
        raise ValueError(
            f"Failed to parse DBC file '{dbc_path}': {response['message']}"
        )
    return response["dbc"]


def dbc_to_text(dbc: DBCDefinition) -> str:
    """Render a DBC JSON dict to .dbc text format via the verified Agda formatter.

    Inverse of :func:`dbc_to_json` at the wire level: ``dbc_to_json(dbc_to_text(d))``
    returns ``d`` byte-identical for any well-formed DBC (Track B.3.d / E.9a).

    Args:
        dbc: DBC definition dict (as returned by :func:`dbc_to_json` or
             :meth:`AletheiaClient.format_dbc`).

    Returns:
        String containing the .dbc file content.

    Note:
        Each call starts a temporary ``AletheiaClient`` (GHC RTS init) just
        to run ``formatDBCText`` and shuts it down again — fine for ad-hoc
        conversions. For tight loops, drive
        :meth:`AletheiaClient.format_dbc_text` on a long-lived
        ``AletheiaClient`` directly instead.
    """
    with AletheiaClient() as client:
        return client.format_dbc_text(dbc)


def convert_dbc_file(
    dbc_path: str | Path,
    output_path: str | Path | None = None,
) -> str:
    """Convert a .dbc file to JSON and optionally write to file.

    Args:
        dbc_path: Path to the .dbc file.
        output_path: Optional path to write JSON output. If None, returns
            JSON string.

    Returns:
        JSON string representation of the DBC file.
    """
    dbc_json = dbc_to_json(dbc_path)
    json_str = dump_json(dbc_json, indent=2)

    if output_path:
        _ = Path(output_path).write_text(json_str, encoding='utf-8')

    return json_str
