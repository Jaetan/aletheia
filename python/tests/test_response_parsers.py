# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Focused tests for ``aletheia.client._response_parsers``.

Complements the per-surface tests in ``test_unified_client*`` by
exercising edge-cases in the shared helpers directly.
"""

from typing import TYPE_CHECKING, cast

import pytest

from aletheia import ProtocolError
from aletheia.client._response_parsers import (
    build_error_response,
    parse_complete_warnings,
)

if TYPE_CHECKING:
    from aletheia.types import Response


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
            build_error_response(cast("Response", {"status": "error", "message": "oops"}))

    def test_non_string_code_raises(self) -> None:
        """A ``code`` that isn't a string is a protocol violation."""
        with pytest.raises(ProtocolError, match="missing or non-string"):
            build_error_response(cast("Response", {"status": "error", "code": 42, "message": "m"}))

    def test_missing_message_raises(self) -> None:
        """Absent ``message`` raises — no invented default."""
        with pytest.raises(ProtocolError, match="missing or non-string 'message'"):
            build_error_response(cast("Response", {"status": "error", "code": "some_code"}))

    def test_non_string_message_raises(self) -> None:
        """Non-string ``message`` is a protocol violation."""
        with pytest.raises(ProtocolError, match="missing or non-string 'message'"):
            build_error_response(
                cast("Response", {"status": "error", "code": "some_code", "message": 123})
            )


class TestParseCompleteWarnings:
    """Strict-contract tests for ``parse_complete_warnings``.

    The end-of-stream ``warnings`` list is untrusted FFI JSON;
    ``property_index`` must be validated via ``validate_integer_field``
    (matching the identical field in ``parse_finalization_results`` and Go's
    ``parseNumberAsInt64``) rather than blindly cast to ``int``.
    """

    def test_happy_path_plain_int(self) -> None:
        """A plain-int property_index flows through unchanged."""
        out = parse_complete_warnings(
            cast(
                "Response",
                {"warnings": [{"kind": "uncached_atom", "property_index": 2, "detail": "Speed"}]},
            )
        )
        assert out == [{"kind": "uncached_atom", "property_index": 2, "detail": "Speed"}]

    def test_rational_dict_property_index_unwrapped(self) -> None:
        """An integer arriving as ``{numerator, denominator: 1}`` is unwrapped."""
        out = parse_complete_warnings(
            cast(
                "Response",
                {
                    "warnings": [
                        {
                            "kind": "uncached_atom",
                            "property_index": {"numerator": 3, "denominator": 1},
                            "detail": "Rpm",
                        }
                    ]
                },
            )
        )
        assert out[0]["property_index"] == 3

    def test_absent_warnings_is_empty(self) -> None:
        """A response with no ``warnings`` key yields an empty list, not an error."""
        assert not parse_complete_warnings(cast("Response", {"status": "complete"}))

    def test_string_property_index_raises(self) -> None:
        """A string property_index is a protocol violation, not a silent cast."""
        with pytest.raises(ProtocolError, match="int or dict"):
            parse_complete_warnings(
                cast(
                    "Response",
                    {"warnings": [{"kind": "uncached_atom", "property_index": "2", "detail": "x"}]},
                )
            )

    def test_non_unit_denominator_raises(self) -> None:
        """A fractional property_index (denominator != 1) is rejected."""
        with pytest.raises(ProtocolError, match="denominator == 1"):
            parse_complete_warnings(
                cast(
                    "Response",
                    {
                        "warnings": [
                            {
                                "kind": "uncached_atom",
                                "property_index": {"numerator": 5, "denominator": 2},
                                "detail": "x",
                            }
                        ]
                    },
                )
            )

    def test_missing_property_index_raises(self) -> None:
        """An absent property_index is rejected — no default-0 (Go raises too)."""
        with pytest.raises(ProtocolError, match="Missing 'property_index'"):
            parse_complete_warnings(
                cast("Response", {"warnings": [{"kind": "uncached_atom", "detail": "x"}]})
            )
