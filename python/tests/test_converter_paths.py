# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Mutation-killing tests for the dbc/_converter.py file wrappers.

``dbc_to_json`` / ``dbc_to_text`` / ``convert_dbc_file`` are thin wrappers over
``AletheiaClient`` + file I/O.  Their error branch (``dbc_to_json`` on a
malformed file), the ``indent=2`` serialization, and the output-file write are
only exercised here.  Run against the real FFI (each call spins a temporary
``AletheiaClient``).  The valid ``.dbc`` fixture is generated via
``dbc_to_text`` into ``tmp_path`` (an absolute path) so the tests resolve no
external files — robust under the mutmut work-tree.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, DBCValidationFailedError, ValidationError
from aletheia.dbc import (
    convert_dbc_file,
    dbc_and_warnings_from_response,
    dbc_to_json,
    dbc_to_text,
)

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.types import DBCDefinition


def _sample_dbc() -> DBCDefinition:
    """Build a minimal well-formed DBC definition."""
    return dbc([message(0x100, "Msg", [signal("Sig")])])


def _write_valid_dbc(tmp_path: Path) -> Path:
    """Render the sample DBC to .dbc text and write it into *tmp_path*."""
    path = tmp_path / "valid.dbc"
    path.write_text(dbc_to_text(_sample_dbc()), encoding="utf-8")
    return path


# Parses cleanly but fails kernel validation with one error (duplicate signal
# name 'S') and warnings (min > max on the first 'S'), so the error envelope
# carries both issue severities.
_VALIDATION_FAILING_DBC_TEXT = (
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_:\n\n'
    "BO_ 256 M: 8 ECU1\n"
    ' SG_ S : 0|8@1+ (1,0) [5|1] "" Vector__XXX\n'
    ' SG_ S : 8|8@1+ (1,0) [0|255] "" Vector__XXX\n'
)

# Parses AND validates successfully (no duplicate) but the single signal's
# range is inverted (min 5 > max 1), a warning-severity issue — so the parse
# succeeds and carries exactly one warning on its envelope.
_VALIDATION_WARNING_DBC_TEXT = (
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_:\n\n'
    "BO_ 256 M: 8 ECU1\n"
    ' SG_ S : 0|8@1+ (1,0) [5|1] "" Vector__XXX\n'
)


def test_dbc_to_json_invalid_file_raises(tmp_path: Path) -> None:
    """Reject a malformed .dbc file, naming the path in the error.

    The error embeds the path literal and reads ``response['message']``; the
    string-literal and message-key mutants change the prefix (caught by the
    startswith) or look up a missing key (raising, which fails the test).
    A syntactic parse failure carries no structured issue list, so it stays
    the generic ``ValidationError`` rather than ``DBCValidationFailedError``.
    """
    bad = tmp_path / "bad.dbc"
    bad.write_text("this is not a valid dbc file\n", encoding="utf-8")
    with pytest.raises(ValidationError) as excinfo:
        dbc_to_json(bad)
    assert str(excinfo.value).startswith(f"Failed to parse DBC file '{bad}': ")


def test_dbc_to_json_validation_failure_raises_typed(tmp_path: Path) -> None:
    """Lift a ``handler_validation_failed`` envelope into the typed exception.

    The message keeps the exact generic-path prefix, and the structured
    issue list — both severities — plus the decoded ``has_errors`` flag
    ride on the exception.
    """
    bad = tmp_path / "dup_signal.dbc"
    bad.write_text(_VALIDATION_FAILING_DBC_TEXT, encoding="utf-8")
    with pytest.raises(DBCValidationFailedError) as excinfo:
        dbc_to_json(bad)
    err = excinfo.value
    assert str(err).startswith(f"Failed to parse DBC file '{bad}': ")
    assert err.code == "handler_validation_failed"
    assert err.has_errors is True
    codes = {issue["code"] for issue in err.issues}
    assert "duplicate_signal_name" in codes
    assert "min_exceeds_max" in codes
    severities = {issue["severity"] for issue in err.issues}
    assert severities == {"error", "warning"}


def test_response_helper_returns_dbc_and_warnings() -> None:
    """A successful parse yields the DBC plus its warning list.

    The shared ``dbc_and_warnings_from_response`` (which the CLI's load path
    and ``dbc_to_json`` both delegate to) must surface the parse warnings,
    not only the DBC body — the ``validate`` subcommand reads them as the
    complete validation result without a second kernel pass. The inverted
    range on the lone signal is a warning-severity issue, so the parse
    succeeds and the returned warning list is non-empty.
    """
    with AletheiaClient() as client:
        response = client.parse_dbc_text(_VALIDATION_WARNING_DBC_TEXT)
    parsed_dbc, warnings = dbc_and_warnings_from_response(response, "warn.dbc")
    assert parsed_dbc["messages"], "the parsed DBC body must be returned"
    codes = {issue["code"] for issue in warnings}
    assert "min_exceeds_max" in codes
    assert all(issue["severity"] == "warning" for issue in warnings)


def test_dbc_to_text_renders_messages() -> None:
    """Render a DBC to .dbc text containing message (BO_) definitions."""
    text = dbc_to_text(_sample_dbc())
    assert "BO_" in text


def test_convert_returns_indent_2_json(tmp_path: Path) -> None:
    """Return indent=2 JSON carrying the real DBC content."""
    result = convert_dbc_file(_write_valid_dbc(tmp_path))
    # indent=2 → a 2-space-indented first key; indent=None (compact) or indent=3
    # would not produce exactly ``{\n  "``.
    assert result.startswith('{\n  "')
    # Real conversion output (a None dbc_json would dump to ``null``).
    assert '"messages"' in result


def test_convert_writes_output_file(tmp_path: Path) -> None:
    """Write the JSON to the output path, byte-identical to the return value."""
    out = tmp_path / "out.json"
    result = convert_dbc_file(_write_valid_dbc(tmp_path), out)
    assert out.read_text(encoding="utf-8") == result
