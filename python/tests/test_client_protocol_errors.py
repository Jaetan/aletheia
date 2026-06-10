# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Mutation-killing tests for AletheiaClient protocol error/edge paths.

``format_dbc`` / ``format_dbc_text`` / ``validate_dbc`` share a
success / error / unexpected-status response structure whose error and edge
branches are only reachable when the backend returns a non-success or
malformed response — which the real Agda backend never produces on the happy
path.  Drive each branch via ``MockBackend`` canned responses, asserting the
*exact* error-message text (equality kills both the uppercase and the
``"XX...XX"``-wrapped string-literal mutants) and the ``code`` propagation /
``isinstance`` guard.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, MockBackend, ProtocolError, StateError

if TYPE_CHECKING:
    from aletheia.types import DBCDefinition, JSONValue

_UNEXPECTED_SUCCESS = "Unexpected response status: 'weird' (expected 'success' or 'error')"
_UNEXPECTED_VALIDATION = "Unexpected response status: 'weird' (expected 'validation' or 'error')"


def _resp(obj: dict[str, JSONValue]) -> bytes:
    """Encode a canned JSON response for the MockBackend queue."""
    return json.dumps(obj).encode("utf-8")


def _sample_dbc() -> DBCDefinition:
    """Build a minimal well-formed DBC for command arguments (response is mocked)."""
    return dbc([message(0x100, "Msg", [signal("Sig")])])


class TestFormatDbcErrorPaths:
    """format_dbc (reads loaded state via format_dbc_binary)."""

    def test_not_initialized_raises_state_error(self) -> None:
        """Reject a call outside a ``with`` block with the guard StateError."""
        client = AletheiaClient(backend=MockBackend())
        with pytest.raises(StateError) as excinfo:
            client.format_dbc()
        assert str(excinfo.value) == "Client not initialized — use 'with' statement"

    def test_error_status_propagates_message_and_code(self) -> None:
        """Surface an error response's message and string code on the ProtocolError."""
        backend = MockBackend([_resp({"status": "error", "message": "boom", "code": "my_code"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc()
        assert str(excinfo.value) == "formatDBC failed: boom"
        assert excinfo.value.code == "my_code"

    def test_error_status_without_message_uses_unknown_error(self) -> None:
        """Fall back to "Unknown error" when an error response omits the message."""
        backend = MockBackend([_resp({"status": "error"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc()
        assert str(excinfo.value) == "formatDBC failed: Unknown error"

    def test_error_status_non_string_code_drops_to_none(self) -> None:
        """Drop a non-string code to None via the isinstance guard."""
        backend = MockBackend([_resp({"status": "error", "message": "boom", "code": 123})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc()
        assert str(excinfo.value) == "formatDBC failed: boom"
        assert excinfo.value.code is None

    def test_unexpected_status_raises(self) -> None:
        """Reject an unrecognized status with the unexpected-status ProtocolError."""
        backend = MockBackend([_resp({"status": "weird"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc()
        assert str(excinfo.value) == _UNEXPECTED_SUCCESS

    def test_success_missing_dbc_field(self) -> None:
        """Reject a success response that omits the ``dbc`` field."""
        backend = MockBackend([_resp({"status": "success"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc()
        assert str(excinfo.value) == "Expected 'dbc' field in formatDBC response"

    def test_success_non_dict_dbc_field(self) -> None:
        """Reject a success response whose ``dbc`` field is not a dict."""
        backend = MockBackend([_resp({"status": "success", "dbc": "notadict"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc()
        assert str(excinfo.value) == "Expected 'dbc' field in formatDBC response"


class TestFormatDbcTextErrorPaths:
    """format_dbc_text (sends formatDBCText, expects a 'text' field)."""

    def test_error_status_propagates_message_and_code(self) -> None:
        """Surface an error response's message and string code on the ProtocolError."""
        backend = MockBackend([_resp({"status": "error", "message": "boom", "code": "my_code"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc_text(_sample_dbc())
        assert str(excinfo.value) == "formatDBCText failed: boom"
        assert excinfo.value.code == "my_code"

    def test_error_status_without_message_uses_unknown_error(self) -> None:
        """Fall back to "Unknown error" when an error response omits the message."""
        backend = MockBackend([_resp({"status": "error"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc_text(_sample_dbc())
        assert str(excinfo.value) == "formatDBCText failed: Unknown error"

    def test_error_status_non_string_code_drops_to_none(self) -> None:
        """Drop a non-string code to None via the isinstance guard."""
        backend = MockBackend([_resp({"status": "error", "message": "boom", "code": 123})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc_text(_sample_dbc())
        assert str(excinfo.value) == "formatDBCText failed: boom"
        assert excinfo.value.code is None

    def test_unexpected_status_raises(self) -> None:
        """Reject an unrecognized status with the unexpected-status ProtocolError."""
        backend = MockBackend([_resp({"status": "weird"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc_text(_sample_dbc())
        assert str(excinfo.value) == _UNEXPECTED_SUCCESS

    def test_success_missing_text_field(self) -> None:
        """Reject a success response that omits the ``text`` field."""
        backend = MockBackend([_resp({"status": "success"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc_text(_sample_dbc())
        assert str(excinfo.value) == "Expected 'text' field in formatDBCText response"

    def test_success_non_string_text_field(self) -> None:
        """Reject a success response whose ``text`` field is not a string."""
        backend = MockBackend([_resp({"status": "success", "text": 123})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc_text(_sample_dbc())
        assert str(excinfo.value) == "Expected 'text' field in formatDBCText response"


class TestValidateDbcErrorPaths:
    """validate_dbc (success branch is status 'validation'; error/unexpected here)."""

    def test_error_status_propagates_message_and_code(self) -> None:
        """Surface an error response's message and string code on the ProtocolError."""
        backend = MockBackend([_resp({"status": "error", "message": "boom", "code": "my_code"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(_sample_dbc())
        assert str(excinfo.value) == "validateDBC failed: boom"
        assert excinfo.value.code == "my_code"

    def test_error_status_without_message_uses_unknown_error(self) -> None:
        """Fall back to "Unknown error" when an error response omits the message."""
        backend = MockBackend([_resp({"status": "error"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(_sample_dbc())
        assert str(excinfo.value) == "validateDBC failed: Unknown error"

    def test_error_status_non_string_code_drops_to_none(self) -> None:
        """Drop a non-string code to None via the isinstance guard."""
        backend = MockBackend([_resp({"status": "error", "message": "boom", "code": 123})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(_sample_dbc())
        assert str(excinfo.value) == "validateDBC failed: boom"
        assert excinfo.value.code is None

    def test_unexpected_status_raises(self) -> None:
        """Reject an unrecognized status with the unexpected-status ProtocolError."""
        backend = MockBackend([_resp({"status": "weird"})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(_sample_dbc())
        assert str(excinfo.value) == _UNEXPECTED_VALIDATION
