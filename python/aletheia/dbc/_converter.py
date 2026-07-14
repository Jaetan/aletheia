# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Convert between .dbc files, JSON, and DBC text format.

* ``dbc_to_json``: parse a .dbc file to the Agda wire format via the
  verified Agda text parser (no third-party Python deps).
* ``dbc_to_text``: render a JSON DBC dict back to .dbc text via the
  verified Agda formatter (FFI-delegated).
* ``convert_dbc_file``: ``dbc_to_json`` + write JSON to disk.

All three are thin wrappers over ``AletheiaClient`` operations; the FFI
shared library (``libaletheia-ffi.so``) is the only runtime requirement.
``dbc_to_text`` and ``dbc_to_json`` together form a verified roundtrip:
writing ``dbc_to_text(d)`` to a file and running ``dbc_to_json`` on that
file returns ``d`` for any well-formed DBC.
"""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from aletheia.client._client import AletheiaClient
from aletheia.client._response_parsers import raise_if_dbc_validation_failed
from aletheia.client._types import (
    ValidationError,
    check_dbc_text_size_bound,
)
from aletheia.types import DBCDefinition, ErrorResponse, ParsedDBCResponse, dump_json

if TYPE_CHECKING:
    from aletheia.codes import ValidationIssue


def dbc_and_warnings_from_response(
    response: ParsedDBCResponse | ErrorResponse,
    source: str,
) -> tuple[DBCDefinition, list[ValidationIssue]]:
    """Extract ``(dbc, warnings)`` from a parse response, raising on error.

    The single decision point for turning a ``parseDBCText`` / ``parseDBC``
    wire response into either a parsed DBC (with its warning list) or the
    appropriate typed exception — shared by :func:`dbc_to_json` and the
    CLI's load path so the error semantics cannot drift between them. The
    ``warnings`` list is the parse's non-error issues; because the kernel's
    parse epilogue runs full validation, it is the complete validation
    result for a DBC that passed every error-severity check.

    Args:
        response: The wire response from a parse command.
        source: Human-readable origin (a file path) for the error message.

    Raises:
        DBCValidationFailedError: The DBC parsed but failed validation with
            a structured issue list (``handler_validation_failed``).
        ValidationError: The error envelope carries no structured issue
            list (e.g. a syntactic parse failure).

    """
    if response["status"] == "error":
        msg = f"Failed to parse DBC file '{source}': {response['message']}"
        # One rule decides liftability — the shared helper the client's
        # validate_dbc uses (gated on the wire code); no local re-implementation.
        raise_if_dbc_validation_failed(response, msg)
        raise ValidationError(msg)
    return response["dbc"], response["warnings"]


def dbc_to_json(dbc_path: str | Path) -> DBCDefinition:
    """Convert a .dbc file to JSON format via the verified Agda parser.

    Args:
        dbc_path: Path to the .dbc file.

    Returns:
        DBC definition in the format expected by Aletheia.DBC.JSONParser.

    Raises:
        OSError: If the file cannot be read.
        DBCValidationFailedError: If the DBC parsed but failed validation
            with a structured issue list (``handler_validation_failed``).
        ValidationError: If the file is not a valid DBC and the error
            envelope carries no structured issue list (e.g. a syntactic
            parse failure).
        InputBoundExceededError: If the file is larger than
            :data:`aletheia.limits.MAX_DBC_TEXT_BYTES` (64 MiB).

    Note:
        Each call starts a temporary ``AletheiaClient`` (GHC RTS init) just
        to run ``parseDBCText`` and shuts it down again — fine for ad-hoc
        conversions. For tight loops, drive ``parse_dbc_text`` on a
        long-lived ``AletheiaClient`` directly instead.

    """
    path = Path(dbc_path)
    check_dbc_text_size_bound(path.stat().st_size)
    # read_text's encoding is NOT droppable (default is the locale, not utf-8);
    # "UTF-8" is a codec-name alias of "utf-8" → both the case and the None
    # mutant are runtime-equivalent here (pragma).
    text = path.read_text(encoding="utf-8")  # pragma: no mutate
    with AletheiaClient() as client:
        response: ParsedDBCResponse | ErrorResponse = client.parse_dbc_text(text)
    dbc, _ = dbc_and_warnings_from_response(response, str(dbc_path))
    return dbc


def dbc_to_text(dbc: DBCDefinition) -> str:
    """Render a DBC JSON dict to .dbc text format via the verified Agda formatter.

    Inverse of :func:`dbc_to_json` at the wire level: writing this text to a
    file and running :func:`dbc_to_json` on it returns an equal ``d`` for any
    text-round-trip well-formed DBC (a stricter condition than validating
    clean — see the "well-formed DBC" entry in ``docs/GLOSSARY.md``).

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
        # This convenience returns the .dbc text only; the ``issues`` warnings
        # are available on the structured ``AletheiaClient.format_dbc_text``
        # result.  A round-trip refusal still propagates as TextRoundTripFailedError.
        return client.format_dbc_text(dbc)["text"]


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
        # write_text's encoding is NOT droppable (locale default); "UTF-8" is a
        # codec-name alias → both the case and None mutant are equivalent (pragma).
        _ = Path(output_path).write_text(json_str, encoding="utf-8")  # pragma: no mutate

    return json_str
