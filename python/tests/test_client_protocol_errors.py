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

from aletheia import (
    AletheiaClient,
    DBCValidationFailedError,
    InputBoundExceededError,
    MockBackend,
    ProtocolError,
    StateError,
    TextRoundTripFailedError,
)
from aletheia.limits import BOUND_KIND_INPUT_LENGTH_BYTES

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

    def test_success_returns_text_and_issues_structure(self) -> None:
        """The success arm returns the exact ``{status, text, issues}`` dict.

        Real-FFI success coverage lives in ``test_format_dbc.py``, which the
        mutation lane ignores (it reaches the ``.so``); this mock-driven test
        runs inside mutmut and pins the success arm.  A NON-EMPTY issues list
        stops a mutant that drops or rewires the ``issues`` pass-through from
        hiding behind an empty fixture, and the full-dict equality pins the
        ``status`` / ``text`` / ``issues`` keys and the ``"success"`` literal.
        """
        issues: list[JSONValue] = [
            {"severity": "warning", "code": "multi_value_mux_selector", "detail": "mux"},
            {"severity": "warning", "code": "attribute_enum_empty", "detail": "no labels"},
        ]
        backend = MockBackend(
            [_resp({"status": "success", "text": 'VERSION ""\n', "issues": issues})]
        )
        with AletheiaClient(backend=backend) as client:
            result = client.format_dbc_text(_sample_dbc())
        assert result == {"status": "success", "text": 'VERSION ""\n', "issues": issues}

    def test_success_absent_issues_defaults_empty(self) -> None:
        """A success response with no ``issues`` field defaults to an empty list."""
        backend = MockBackend([_resp({"status": "success", "text": 'VERSION ""\n'})])
        with AletheiaClient(backend=backend) as client:
            result = client.format_dbc_text(_sample_dbc())
        assert result == {"status": "success", "text": 'VERSION ""\n', "issues": []}

    def test_success_non_list_issues_field_raises(self) -> None:
        """Reject a success response whose ``issues`` field is present but not a list of objects.

        Absent issues default to empty; a present-but-ill-typed field is a
        ProtocolError (not a KeyError/TypeError crash) — the malformed-response
        contract mirrors ``parse_parsed_dbc_response``'s ``warnings`` validation.
        """
        backend = MockBackend([_resp({"status": "success", "text": 'VERSION ""\n', "issues": {}})])
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.format_dbc_text(_sample_dbc())
        assert (
            str(excinfo.value)
            == "formatDBCText success response 'issues' must be a list of objects"
        )

    def test_roundtrip_failed_envelope_lifts_to_typed_error(self) -> None:
        """A ``handler_text_roundtrip_failed`` envelope lifts to the typed error.

        Mirrors the ``validate_dbc`` ``handler_validation_failed`` lift test;
        pins the exact message, the gated wire code, the decoded ``has_errors``,
        and the issues in wire order — the mutant-killing contract of the
        ``raise_if_text_roundtrip_failed`` arm (its real-FFI coverage lives in the
        mutation-ignored ``test_format_dbc.py``).
        """
        issues: list[JSONValue] = [
            {"severity": "error", "code": "text_roundtrip_divergence", "detail": "diverges"},
            {"severity": "warning", "code": "multi_value_mux_selector", "detail": "mux"},
        ]
        backend = MockBackend(
            [
                _resp(
                    {
                        "status": "error",
                        "message": "boom",
                        "code": "handler_text_roundtrip_failed",
                        "has_errors": True,
                        "issues": issues,
                    }
                )
            ]
        )
        with (
            AletheiaClient(backend=backend) as client,
            pytest.raises(TextRoundTripFailedError) as excinfo,
        ):
            client.format_dbc_text(_sample_dbc())
        assert str(excinfo.value) == "formatDBCText failed: boom"
        assert excinfo.value.code == "handler_text_roundtrip_failed"
        assert excinfo.value.has_errors is True
        assert excinfo.value.issues == issues


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

    def test_error_with_issues_raises_typed_validation_failure(self) -> None:
        """Lift a handler_validation_failed envelope into the typed error.

        Pins every carried field: the exact message text, the gated wire
        code, the decoded (not assumed) ``has_errors``, and both issues in
        wire order — the mutant-killing contract of the lifted arm.
        """
        issues: list[JSONValue] = [
            {"severity": "error", "code": "duplicate_signal_name", "detail": "dup 'S'"},
            {"severity": "warning", "code": "offset_scale_range", "detail": "range"},
        ]
        backend = MockBackend(
            [
                _resp(
                    {
                        "status": "error",
                        "message": "boom",
                        "code": "handler_validation_failed",
                        "has_errors": True,
                        "issues": issues,
                    }
                )
            ]
        )
        with (
            AletheiaClient(backend=backend) as client,
            pytest.raises(DBCValidationFailedError) as excinfo,
        ):
            client.validate_dbc(_sample_dbc())
        assert str(excinfo.value) == "validateDBC failed: boom"
        assert excinfo.value.code == "handler_validation_failed"
        assert excinfo.value.has_errors is True
        assert excinfo.value.issues == issues

    def test_error_with_issues_but_foreign_code_stays_protocol_error(self) -> None:
        """The lift is gated on the wire code (matches the Go/C++/Rust decoders).

        A foreign error envelope that happens to carry issues-shaped keys
        must NOT be mis-lifted into a validation failure.
        """
        issues: list[JSONValue] = [
            {"severity": "error", "code": "duplicate_signal_name", "detail": "d"}
        ]
        backend = MockBackend(
            [
                _resp(
                    {
                        "status": "error",
                        "message": "boom",
                        "code": "some_other_code",
                        "has_errors": True,
                        "issues": issues,
                    }
                )
            ]
        )
        with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(_sample_dbc())
        assert str(excinfo.value) == "validateDBC failed: boom"
        assert excinfo.value.code == "some_other_code"


class TestSendCommandGuards:
    """_send_command guards: the not-initialized check and the JSON size bound.

    Driven through ``validate_dbc`` (the thinnest public method that routes
    straight through ``_send_command`` with no inner cap of its own).
    """

    def test_not_initialized_raises_state_error(self) -> None:
        """Reject a command sent before ``__enter__`` with the guard StateError."""
        client = AletheiaClient(backend=MockBackend())
        with pytest.raises(StateError) as excinfo:
            client.validate_dbc(_sample_dbc())
        assert str(excinfo.value) == "Client not initialized — use 'with' statement"

    def test_oversize_command_raises_input_bound_exceeded(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Reject a command whose JSON exceeds MAX_JSON_BYTES before the FFI call.

        Patches the limit small so a normal command trips it without building a
        64 MiB payload; asserts every structured field (kind / observed / limit /
        code) so the InputBoundExceededError construction args are all pinned.
        """
        monkeypatch.setattr("aletheia.client._client.MAX_JSON_BYTES", 50)
        backend = MockBackend()
        with AletheiaClient(backend=backend) as client:
            with pytest.raises(InputBoundExceededError) as excinfo:
                client.validate_dbc(_sample_dbc())
            err = excinfo.value
            assert err.kind == BOUND_KIND_INPUT_LENGTH_BYTES
            assert err.observed > 50
            assert err.limit == 50
            assert err.code == "input_bound_exceeded"
        # The bound short-circuits before the backend is ever consulted.
        assert not backend.inputs

    def test_command_exactly_at_limit_is_allowed(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """A command whose JSON is EXACTLY MAX_JSON_BYTES is allowed (bound is `>`, not `>=`).

        The first call (default limit) records the exact serialized command size via
        ``backend.inputs``; patching the limit to that size makes the second call sit
        precisely on the boundary, where ``> limit`` admits it but ``>= limit`` would reject.
        """
        valid = _resp({"status": "validation", "has_errors": False, "issues": []})
        sample = _sample_dbc()
        backend = MockBackend([valid, valid])
        with AletheiaClient(backend=backend) as client:
            client.validate_dbc(sample)
            exact = len(backend.inputs[0])
            monkeypatch.setattr("aletheia.client._client.MAX_JSON_BYTES", exact)
            result = client.validate_dbc(sample)
        assert result["status"] == "validation"
        assert len(backend.inputs) == 2  # the boundary command DID reach the backend
