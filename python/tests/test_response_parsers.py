"""Focused tests for ``aletheia.client._response_parsers``.

Complements the per-surface tests in ``test_unified_client*`` by
exercising edge-cases in the shared helpers directly.
"""

import pytest

from aletheia import ProtocolError
from aletheia.client._response_parsers import build_error_response


class TestBuildErrorResponse:
    """Strict-contract tests for ``build_error_response``.

    The Agda core always emits both ``status = "error"`` fields; absent
    or non-string ``code`` indicates a malformed response and must
    surface as ``ProtocolError`` rather than a silent empty string.
    """

    def test_happy_path_returns_both_fields(self) -> None:
        """Well-formed response flows through unchanged."""
        out = build_error_response(
            {"status": "error", "code": "handler_no_dbc", "message": "no DBC"}
        )
        assert out == {
            "status": "error",
            "code": "handler_no_dbc",
            "message": "no DBC",
        }

    def test_missing_code_raises(self) -> None:
        """Absent ``code`` raises — empty-string default is disallowed."""
        with pytest.raises(ProtocolError, match="missing or non-string"):
            build_error_response({"status": "error", "message": "oops"})

    def test_non_string_code_raises(self) -> None:
        """A ``code`` that isn't a string is a protocol violation."""
        with pytest.raises(ProtocolError, match="missing or non-string"):
            build_error_response({"status": "error", "code": 42, "message": "m"})

    def test_missing_message_defaults_to_empty(self) -> None:
        """``message`` is advisory — absent is OK, defaults to ``""``."""
        out = build_error_response({"status": "error", "code": "some_code"})
        assert out == {"status": "error", "code": "some_code", "message": ""}

    def test_non_string_message_defaults_to_empty(self) -> None:
        """Non-string ``message`` also defaults to ``""`` (still advisory)."""
        out = build_error_response(
            {"status": "error", "code": "some_code", "message": 123}
        )
        assert out["message"] == ""
