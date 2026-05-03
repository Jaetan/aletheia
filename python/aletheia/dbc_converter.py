"""Convert between .dbc files, JSON, and DBC text format.

* ``dbc_to_json``: parse a .dbc file to the Agda wire format. Defaults to
  the verified Agda text parser (``parser="agda"``); pass
  ``parser="cantools"`` (or set ``ALETHEIA_DBC_PARSER=cantools``) to fall
  back to the legacy cantools path while it remains.
* ``dbc_to_text``: convert a JSON dict back to .dbc text. Pure Python; no
  cantools.
* ``convert_dbc_file``: ``dbc_to_json`` + write JSON to disk.

The default Agda path requires the FFI shared library (``libaletheia-ffi.so``)
but no third-party Python deps. Cantools is only loaded when
``parser="cantools"`` is selected.
"""

import os
from fractions import Fraction
from pathlib import Path
from typing import Literal, cast

from .client import AletheiaClient
from .client._helpers import dump_json
from .protocols import DBCDefinition, DBCSignal, ErrorResponse, ParsedDBCResponse

# CAN Extended Frame Format flag — bit 31 set to distinguish 29-bit extended
# IDs from 11-bit standard IDs in .dbc file format.
_CAN_EFF_FLAG = 0x80000000

DBCParser = Literal["agda", "cantools"]
_VALID_PARSERS: frozenset[str] = frozenset({"agda", "cantools"})
_PARSER_ENV_VAR = "ALETHEIA_DBC_PARSER"


def _resolve_parser(explicit: DBCParser | None) -> DBCParser:
    """Resolve which parser to use (precedence: kwarg → env var → ``agda``).

    A bad env-var value raises ``ValueError`` rather than silently falling
    back, so a typo in CI config surfaces as a hard failure instead of
    routing through a different parser than the operator expects.
    """
    if explicit is not None:
        return explicit
    env_value = os.environ.get(_PARSER_ENV_VAR)
    if env_value is None:
        return "agda"
    if env_value not in _VALID_PARSERS:
        raise ValueError(
            f"{_PARSER_ENV_VAR}={env_value!r} not in {sorted(_VALID_PARSERS)}"
        )
    return cast(DBCParser, env_value)


def _dbc_to_json_agda(dbc_path: str | Path) -> DBCDefinition:
    """Parse a .dbc file via the Agda text parser (verified roundtrip).

    Each call spins up an ``AletheiaClient`` (GHC RTS init) just to run
    ``parseDBCText`` and shuts it down again. That is acceptable for ad-hoc
    conversions; if you call this in a tight loop, drive ``parse_dbc_text``
    on a long-lived ``AletheiaClient`` directly instead.
    """
    text = Path(dbc_path).read_text(encoding="utf-8")
    with AletheiaClient() as client:
        response: ParsedDBCResponse | ErrorResponse = client.parse_dbc_text(text)
    if response["status"] == "error":
        raise ValueError(
            f"Failed to parse DBC file '{dbc_path}': {response['message']}"
        )
    return response["dbc"]


def dbc_to_json(
    dbc_path: str | Path,
    *,
    parser: DBCParser | None = None,
) -> DBCDefinition:
    """Convert a .dbc file to JSON format.

    Args:
        dbc_path: Path to the .dbc file.
        parser: ``"agda"`` (default, verified) or ``"cantools"`` (legacy).
            If ``None``, the ``ALETHEIA_DBC_PARSER`` env var is consulted;
            absent that, defaults to ``"agda"``.

    Returns:
        DBC definition in the format expected by Aletheia.DBC.JSONParser.

    Raises:
        OSError: If the file cannot be read.
        ValueError: If the file is not a valid DBC, or ``parser`` /
            ``ALETHEIA_DBC_PARSER`` names an unknown backend.
        ImportError: If ``parser="cantools"`` is selected but the optional
            ``cantools`` dependency is not installed.

    Note:
        ``parser="agda"`` runs through the verified Agda text parser and
        starts a temporary ``AletheiaClient`` per call; the FFI shared
        library must be available. ``parser="cantools"`` is slated for
        removal in B.3.g.
    """
    effective = _resolve_parser(parser)
    if effective == "agda":
        return _dbc_to_json_agda(dbc_path)
    # parser="cantools" — import lazily so the cantools dep is only
    # required by callers who explicitly opt in.
    from . import _dbc_to_json_cantools  # pylint: disable=import-outside-toplevel
    return _dbc_to_json_cantools.dbc_to_json_cantools(dbc_path)


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

    # Trailing receiver list. Vector__XXX is the DBC convention for "no
    # specific receiver", used when the per-signal receivers field is empty.
    receivers_text = ",".join(signal.get("receivers") or ()) or "Vector__XXX"
    return (
        f" SG_ {name}{mux_indicator} : "
        f"{start_bit}|{length}@{bo}{sign} "
        f"({factor},{offset}) "
        f"[{minimum}|{maximum}] "
        f'"{unit}" {receivers_text}'
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


def convert_dbc_file(
    dbc_path: str | Path,
    output_path: str | Path | None = None,
    *,
    parser: DBCParser | None = None,
) -> str:
    """Convert a .dbc file to JSON and optionally write to file.

    Args:
        dbc_path: Path to the .dbc file.
        output_path: Optional path to write JSON output. If None, returns
            JSON string.
        parser: Forwarded to :func:`dbc_to_json`.

    Returns:
        JSON string representation of the DBC file.
    """
    dbc_json = dbc_to_json(dbc_path, parser=parser)
    json_str = dump_json(dbc_json, indent=2)

    if output_path:
        _ = Path(output_path).write_text(json_str, encoding='utf-8')

    return json_str
