# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Focused tests for ``aletheia.client._response_parsers``.

Complements the per-surface tests in ``test_unified_client*`` by
exercising edge-cases in the shared helpers directly.
"""

from typing import TYPE_CHECKING, cast

import pytest

from aletheia import InputBoundExceededError, ProtocolError
from aletheia.client._response_parsers import (
    build_error_response,
    parse_complete_warnings,
    raise_if_input_bound_exceeded,
)

if TYPE_CHECKING:
    from aletheia.common_types import PositiveInt
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

    @pytest.mark.parametrize(
        ("observed", "limit"),
        [pytest.param(65, 64, id="past-64"), pytest.param(2, 1, id="past-1")],
    )
    def test_wellformed_bound_triple_is_attached(
        self, observed: PositiveInt, limit: PositiveInt
    ) -> None:
        """A complete, well-typed input_bound_exceeded triple is lifted onto the response.

        A limit of 1 is the smallest positive one, so it pins the positivity check
        at its boundary.
        """
        out = build_error_response(
            cast(
                "Response",
                {
                    "status": "error",
                    "code": "input_bound_exceeded",
                    "message": "too deep",
                    "bound_kind": "nesting_depth",
                    "observed": observed,
                    "limit": limit,
                },
            )
        )
        assert out.get("bound_kind") == "nesting_depth"
        assert out.get("observed") == observed
        assert out.get("limit") == limit

    @pytest.mark.parametrize(
        "triple",
        [
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": "65", "limit": 64}, id="observed-string"
            ),
            pytest.param({"bound_kind": "nesting_depth", "limit": 64}, id="observed-absent"),
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": True, "limit": 64}, id="observed-bool"
            ),
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": 65, "limit": 6.5}, id="limit-float"
            ),
            pytest.param({"bound_kind": 7, "observed": 65, "limit": 64}, id="bound_kind-nonstring"),
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": 0, "limit": 64}, id="observed-zero"
            ),
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": 65, "limit": -1}, id="limit-negative"
            ),
        ],
    )
    def test_malformed_bound_triple_is_dropped(self, triple: dict[str, object]) -> None:
        """A partial or ill-typed triple degrades to no triple — never a partial one.

        Matches the C++ ``make_json_error`` degrade-to-nullopt rule: all three of
        ``bound_kind`` / ``observed`` / ``limit`` must be present and well-typed, the
        counts positive, or none is attached. Pins each guard against a mutation that
        drops one and lets a malformed triple through (the attach path stays
        line-green either way, so this is the mutation-killing companion).
        """
        out = build_error_response(
            cast(
                "Response",
                {"status": "error", "code": "input_bound_exceeded", "message": "m", **triple},
            )
        )
        assert out == {"status": "error", "code": "input_bound_exceeded", "message": "m"}

    def test_wellformed_validation_issues_are_attached(self) -> None:
        """A complete ``handler_validation_failed`` payload is lifted onto the response.

        Both issue severities ride along and ``has_errors`` echoes the wire
        value (decoded, not assumed true).
        """
        issues = [
            {"severity": "error", "code": "duplicate_signal_name", "detail": "dup 'S'"},
            {"severity": "warning", "code": "offset_scale_range", "detail": "range"},
        ]
        out = build_error_response(
            cast(
                "Response",
                {
                    "status": "error",
                    "code": "handler_validation_failed",
                    "message": "ParseDBCText: validation failed: dup 'S'",
                    "has_errors": True,
                    "issues": issues,
                },
            )
        )
        assert out.get("has_errors") is True
        assert out.get("issues") == issues

    def test_foreign_code_with_issue_shaped_payload_is_not_lifted(self) -> None:
        """The lift is gated on ``code == "handler_validation_failed"``.

        Another error envelope carrying has_errors/issues-shaped keys must
        not be mis-lifted (matches the Go/C++/Rust decoders' code gate).
        """
        out = build_error_response(
            cast(
                "Response",
                {
                    "status": "error",
                    "code": "some_future_error",
                    "message": "boom",
                    "has_errors": True,
                    "issues": [
                        {"severity": "error", "code": "duplicate_signal_name", "detail": "d"}
                    ],
                },
            )
        )
        assert "has_errors" not in out
        assert "issues" not in out

    @pytest.mark.parametrize(
        "extras",
        [
            pytest.param(
                {"issues": [{"severity": "error", "code": "c", "detail": "d"}]},
                id="has_errors-absent",
            ),
            pytest.param(
                {
                    "has_errors": 1,
                    "issues": [{"severity": "error", "code": "c", "detail": "d"}],
                },
                id="has_errors-int",
            ),
            pytest.param({"has_errors": True}, id="issues-absent"),
            pytest.param({"has_errors": True, "issues": "nope"}, id="issues-nonlist"),
            pytest.param({"has_errors": True, "issues": [42]}, id="issue-nonobject"),
            pytest.param(
                {"has_errors": True, "issues": [{"severity": "fatal", "code": "c", "detail": "d"}]},
                id="severity-unknown",
            ),
            pytest.param(
                {"has_errors": True, "issues": [{"severity": "error", "detail": "d"}]},
                id="code-absent",
            ),
            pytest.param(
                {"has_errors": True, "issues": [{"severity": "error", "code": "c", "detail": 7}]},
                id="detail-nonstring",
            ),
        ],
    )
    def test_malformed_validation_issues_are_dropped(self, extras: dict[str, object]) -> None:
        """An absent or ill-typed issues payload degrades to no payload — never partial.

        Same all-or-nothing rule as the bound triple: ``has_errors`` must be a
        bool and every issue an object with canonical severity plus string
        ``code`` / ``detail``, or neither field is attached — and the decode
        never fails harder than the pre-payload generic error.
        """
        out = build_error_response(
            cast(
                "Response",
                {"status": "error", "code": "handler_validation_failed", "message": "m", **extras},
            )
        )
        assert out == {"status": "error", "code": "handler_validation_failed", "message": "m"}


# A bound refusal envelope, past a limit of 10000, naming no field.
_BOUND_REFUSAL = {
    "status": "error",
    "code": "input_bound_exceeded",
    "message": "ParseDBC: array cardinality 10001 exceeds limit 10000",
    "bound_kind": "array_cardinality",
    "observed": 10_001,
    "limit": 10_000,
}


class TestRaiseIfInputBoundExceeded:
    """The lift of an ``input_bound_exceeded`` envelope into the typed error."""

    def test_raises_the_triple_the_field_and_the_message(self) -> None:
        """A whole triple, a string ``field`` and a string ``message`` raise the error.

        The error carries the triple and the field, and its text is the
        kernel's message as the envelope spells it.
        """
        message = "ParseDBC: senders array: array cardinality 10001 exceeds limit 10000"
        envelope = cast(
            "Response", {**_BOUND_REFUSAL, "field": "senders array", "message": message}
        )
        with pytest.raises(InputBoundExceededError) as exc_info:
            raise_if_input_bound_exceeded(envelope)
        err = exc_info.value
        assert (err.kind, err.observed, err.limit, err.field, err.code, str(err)) == (
            "array_cardinality",
            10_001,
            10_000,
            "senders array",
            "input_bound_exceeded",
            message,
        )

    def test_absent_field_is_none(self) -> None:
        """A refusal naming no field raises the error with ``field`` None and the message."""
        with pytest.raises(InputBoundExceededError) as exc_info:
            raise_if_input_bound_exceeded(cast("Response", _BOUND_REFUSAL))
        assert (exc_info.value.field, str(exc_info.value)) == (None, _BOUND_REFUSAL["message"])

    @pytest.mark.parametrize(
        "envelope",
        [
            pytest.param(cast("Response", {**_BOUND_REFUSAL, "field": 7}), id="field-nonstring"),
            pytest.param(
                cast("Response", {**_BOUND_REFUSAL, "message": 7}), id="message-nonstring"
            ),
            pytest.param(
                cast(
                    "Response",
                    {key: value for key, value in _BOUND_REFUSAL.items() if key != "message"},
                ),
                id="message-absent",
            ),
            pytest.param(cast("Response", {**_BOUND_REFUSAL, "observed": 0}), id="observed-zero"),
            pytest.param(
                cast("Response", {**_BOUND_REFUSAL, "code": "handler_validation_failed"}),
                id="other-code",
            ),
        ],
    )
    def test_degrades_to_the_caller_fallback(self, envelope: Response) -> None:
        """A non-string field or message, a malformed triple or another code raises nothing."""
        raise_if_input_bound_exceeded(envelope)


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

    def test_non_list_warnings_raises(self) -> None:
        """A non-list ``warnings`` is a typed error, not a bare TypeError."""
        with pytest.raises(ProtocolError, match="must be a list"):
            parse_complete_warnings(cast("Response", {"warnings": "nope"}))

    def test_non_object_warning_entry_raises(self) -> None:
        """A non-object warning entry is a typed error, not an AttributeError."""
        with pytest.raises(ProtocolError, match="must be an object"):
            parse_complete_warnings(cast("Response", {"warnings": [42]}))
