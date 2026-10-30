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
    from aletheia.common_types import PositiveInt, Prose
    from aletheia.types import JSONValue, Response


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

    @pytest.mark.parametrize(
        ("envelope", "text"),
        [
            pytest.param(
                {"status": "error", "message": "oops"},
                "reply code: expected string, got nothing",
                id="code-absent",
            ),
            pytest.param(
                {"status": "error", "code": 42, "message": "m"},
                "reply code: expected string, got number",
                id="code-number",
            ),
            pytest.param(
                {"status": "error", "code": "some_code"},
                "reply message: expected string, got nothing",
                id="message-absent",
            ),
            pytest.param(
                {"status": "error", "code": "some_code", "message": 123},
                "reply message: expected string, got number",
                id="message-number",
            ),
        ],
    )
    def test_code_and_message_are_strings(self, envelope: Response, text: Prose) -> None:
        """An absent or non-string ``code`` or ``message`` is refused at its place, no default."""
        with pytest.raises(ProtocolError) as exc_info:
            build_error_response(envelope)
        assert str(exc_info.value) == text

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
        ("triple", "refusal"),
        [
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": "65", "limit": 64},
                "reply observed: expected number, got string",
                id="observed-string",
            ),
            pytest.param(
                {"bound_kind": "nesting_depth", "limit": 64},
                "reply observed: expected number, got nothing",
                id="observed-absent",
            ),
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": True, "limit": 64},
                "reply observed: expected number, got boolean",
                id="observed-bool",
            ),
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": 65, "limit": 6.5},
                "reply limit: expected number, got number",
                id="limit-float",
            ),
            pytest.param(
                {"bound_kind": 7, "observed": 65, "limit": 64},
                "reply bound_kind: expected string, got number",
                id="bound_kind-nonstring",
            ),
            pytest.param(
                {"bound_kind": "nesting_depth", "observed": 65, "limit": 64, "field": 7},
                "reply field: expected string, got number",
                id="field-nonstring",
            ),
        ],
    )
    def test_a_partial_or_mistyped_bound_refusal_is_refused_at_its_place(
        self, triple: dict[str, object], refusal: Prose
    ) -> None:
        """A triple the kernel writes whole is refused at the first key out of its kind."""
        with pytest.raises(ProtocolError) as refused:
            _ = build_error_response(
                cast(
                    "Response",
                    {"status": "error", "code": "input_bound_exceeded", "message": "m", **triple},
                )
            )
        assert str(refused.value) == refusal

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
        ("envelope", "refusal"),
        [
            pytest.param(
                cast("Response", {**_BOUND_REFUSAL, "field": 7}),
                "reply field: expected string, got number",
                id="field-nonstring",
            ),
            pytest.param(
                cast("Response", {**_BOUND_REFUSAL, "message": 7}),
                "reply message: expected string, got number",
                id="message-nonstring",
            ),
            pytest.param(
                cast(
                    "Response",
                    {key: value for key, value in _BOUND_REFUSAL.items() if key != "message"},
                ),
                "reply message: expected string, got nothing",
                id="message-absent",
            ),
            pytest.param(
                cast(
                    "Response",
                    {"status": "error", "code": "input_bound_exceeded", "message": "m"},
                ),
                "reply bound_kind: expected string, got nothing",
                id="triple-absent",
            ),
        ],
    )
    def test_a_bound_refusal_out_of_its_kinds_is_refused_at_its_place(
        self, envelope: Response, refusal: Prose
    ) -> None:
        """A bound refusal's field, message and triple are read by kind."""
        with pytest.raises(ProtocolError) as refused:
            raise_if_input_bound_exceeded(envelope)
        assert str(refused.value) == refusal

    def test_another_code_raises_nothing(self) -> None:
        """An envelope of another code is left to the caller."""
        raise_if_input_bound_exceeded(
            cast("Response", {**_BOUND_REFUSAL, "code": "handler_validation_failed"})
        )


class TestParseCompleteWarnings:
    """Strict-contract tests for ``parse_complete_warnings``.

    The end-of-stream ``warnings`` list is untrusted FFI JSON: ``property_index``
    is a whole number the kernel writes as digits, refused at
    ``warnings/property_index`` as anything else rather than cast to ``int``.
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

    @pytest.mark.parametrize(
        ("property_index", "text"),
        [
            pytest.param(
                "2", "reply warnings/property_index: expected number, got string", id="string"
            ),
            pytest.param(
                True, "reply warnings/property_index: expected number, got boolean", id="boolean"
            ),
            pytest.param(
                {"numerator": 3, "denominator": 1},
                "reply warnings/property_index: expected number, got object",
                id="unit-denominator",
            ),
            pytest.param(
                {"numerator": 5, "denominator": 2},
                "reply warnings/property_index: expected number, got object",
                id="fraction",
            ),
        ],
    )
    def test_property_index_is_a_whole_number(self, property_index: JSONValue, text: Prose) -> None:
        """A property_index that is not an int, a bool or a rational object included, is refused."""
        warning = {"kind": "uncached_atom", "property_index": property_index, "detail": "x"}
        with pytest.raises(ProtocolError) as exc_info:
            parse_complete_warnings(cast("Response", {"warnings": [warning]}))
        assert str(exc_info.value) == text

    @pytest.mark.parametrize(
        ("reply", "text"),
        [
            pytest.param(
                {"status": "complete"},
                "reply warnings: expected array, got nothing",
                id="warnings-absent",
            ),
            pytest.param(
                {"warnings": "nope"},
                "reply warnings: expected array, got string",
                id="warnings-string",
            ),
            pytest.param(
                {"warnings": [42]}, "reply warnings: expected object, got number", id="entry-number"
            ),
            pytest.param(
                {"warnings": [{"kind": "uncached_atom", "detail": "x"}]},
                "reply warnings/property_index: expected number, got nothing",
                id="property_index-absent",
            ),
        ],
    )
    def test_a_broken_warnings_place_is_refused(self, reply: Response, text: Prose) -> None:
        """An absent or non-list ``warnings``, a non-object entry or no property_index is refused.

        The kernel writes each of them, so none is defaulted.
        """
        with pytest.raises(ProtocolError) as exc_info:
            parse_complete_warnings(reply)
        assert str(exc_info.value) == text
