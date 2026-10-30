# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A place the kernel always writes is refused when a reply lacks it or holds another kind.

Each reader in ``aletheia.client._response_parsers`` raises ``ProtocolError``
reading ``reply <path>: expected <what>, got <what came>`` rather than
substituting a value or dropping the field.
"""

from typing import TYPE_CHECKING, Literal, cast

import pytest

from aletheia import ProtocolError
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.client._response_parsers import (
    build_error_response,
    entry_reason,
    parse_complete_warnings,
    parse_finalization_results,
    parse_frame_response,
    parse_parsed_dbc_response,
    raise_if_dbc_validation_failed,
    raise_if_text_roundtrip_failed,
)
from aletheia.codes import ErrorCode

if TYPE_CHECKING:
    from aletheia.common_types import Prose
    from aletheia.types import PropertyResultEntry, Response

# The statuses of an end-of-stream entry that carries a reason.
type EntryStatus = Literal["fails", "unresolved"]

_ISSUE = {"severity": "error", "code": "duplicate_signal_name", "detail": "d"}

# A parsed DBC with no message.
_DBC = {"version": "1.0", "messages": [], **empty_dbc_tier2()}

# Each ill-formed issues payload, with the text of its refusal.
_MALFORMED_ISSUES = [
    pytest.param(
        {"issues": [_ISSUE]},
        "reply has_errors: expected boolean, got nothing",
        id="has_errors-absent",
    ),
    pytest.param(
        {"has_errors": 1, "issues": [_ISSUE]},
        "reply has_errors: expected boolean, got number",
        id="has_errors-int",
    ),
    pytest.param(
        {"has_errors": True}, "reply issues: expected array, got nothing", id="issues-absent"
    ),
    pytest.param(
        {"has_errors": True, "issues": "nope"},
        "reply issues: expected array, got string",
        id="issues-nonlist",
    ),
    pytest.param(
        {"has_errors": True, "issues": [42]},
        "reply issues: expected object, got number",
        id="issue-nonobject",
    ),
    pytest.param(
        {"has_errors": True, "issues": [{"severity": "error", "detail": "d"}]},
        "reply issues/code: expected string, got nothing",
        id="code-absent",
    ),
    pytest.param(
        {"has_errors": True, "issues": [{"severity": "error", "code": "c", "detail": 7}]},
        "reply issues/detail: expected string, got number",
        id="detail-nonstring",
    ),
    pytest.param(
        {"has_errors": True, "issues": [{"severity": 7, "code": "c", "detail": "d"}]},
        "reply issues/severity: expected string, got number",
        id="severity-int",
    ),
]

# Each ill-formed end-of-stream warning entry, with the text of its refusal.
_MALFORMED_WARNINGS = [
    pytest.param(
        {"property_index": 0, "detail": "Speed"},
        "reply warnings/kind: expected string, got nothing",
        id="kind-absent",
    ),
    pytest.param(
        {"kind": 7, "property_index": 0, "detail": "Speed"},
        "reply warnings/kind: expected string, got number",
        id="kind-int",
    ),
    pytest.param(
        {"kind": "uncached_atom", "property_index": 0},
        "reply warnings/detail: expected string, got nothing",
        id="detail-absent",
    ),
    pytest.param(
        {"kind": "uncached_atom", "property_index": 0, "detail": 7},
        "reply warnings/detail: expected string, got number",
        id="detail-int",
    ),
]

# Each ill-formed parseDBC or parseDBCText reply, with the text of its refusal.
_MALFORMED_PARSED_DBC = [
    pytest.param(
        {"status": "weird"},
        'reply status: expected "success" or "error", got "weird"',
        id="status-other-word",
    ),
    pytest.param(
        {"dbc": _DBC, "warnings": []},
        'reply status: expected "success" or "error", got nothing',
        id="status-absent",
    ),
    pytest.param(
        {"status": 1}, 'reply status: expected "success" or "error", got number', id="status-number"
    ),
    pytest.param(
        {"status": "success", "warnings": []},
        "reply dbc: expected object, got nothing",
        id="dbc-absent",
    ),
    pytest.param(
        {"status": "success", "dbc": [], "warnings": []},
        "reply dbc: expected object, got array",
        id="dbc-array",
    ),
    pytest.param(
        {"status": "success", "dbc": _DBC},
        "reply warnings: expected array, got nothing",
        id="warnings-absent",
    ),
    pytest.param(
        {"status": "success", "dbc": _DBC, "warnings": {}},
        "reply warnings: expected array, got object",
        id="warnings-object",
    ),
    pytest.param(
        {"status": "success", "dbc": _DBC, "warnings": [{"code": "c", "severity": 7}]},
        "reply warnings/severity: expected string, got number",
        id="severity-number",
    ),
]

# A batch's fails event as the kernel writes it but for its timestamp.
_FAILS_WITHOUT_TIMESTAMP: PropertyResultEntry = {
    "type": "property",
    "status": "fails",
    "property_index": 0,
    "reason": "r",
}


# Each ill-formed frame reply, with the text of its refusal.
_MALFORMED_FRAMES = [
    pytest.param(
        {"status": "success"},
        'reply status: expected "ack" or "error", got "success"',
        id="status-other-word",
    ),
    pytest.param(
        {"status": 0, "type": "property_batch", "results": []},
        'reply status: expected "ack" or "error", got number',
        id="status-number",
    ),
    pytest.param(
        {"status": None}, 'reply status: expected "ack" or "error", got null', id="status-null"
    ),
    pytest.param({}, 'reply type: expected "property_batch", got nothing', id="type-absent"),
    pytest.param(
        {"type": "property", "results": []},
        'reply type: expected "property_batch", got "property"',
        id="type-other-word",
    ),
    pytest.param(
        {"type": 0, "results": []},
        'reply type: expected "property_batch", got number',
        id="type-number",
    ),
    pytest.param(
        {"type": "property_batch"},
        "reply results: expected array, got nothing",
        id="results-absent",
    ),
    pytest.param(
        {"type": "property_batch", "results": {}},
        "reply results: expected array, got object",
        id="results-object",
    ),
    pytest.param(
        {"type": "property_batch", "results": [7]},
        "reply results: expected object, got number",
        id="entry-number",
    ),
    pytest.param(
        {"type": "property_batch", "results": [{"type": "property", "status": "holds"}]},
        "reply results/property_index: expected number, got nothing",
        id="property_index-absent",
    ),
    pytest.param(
        {
            "type": "property_batch",
            "results": [{"type": "property", "status": "holds", "property_index": "0"}],
        },
        "reply results/property_index: expected number, got string",
        id="property_index-string",
    ),
    pytest.param(
        {
            "type": "property_batch",
            "results": [{"type": "property", "status": "holds", "property_index": False}],
        },
        "reply results/property_index: expected number, got boolean",
        id="property_index-boolean",
    ),
    pytest.param(
        {
            "type": "property_batch",
            "results": [
                {
                    "type": "property",
                    "status": "holds",
                    "property_index": {"numerator": 1, "denominator": 1},
                }
            ],
        },
        "reply results/property_index: expected number, got object",
        id="property_index-rational",
    ),
    pytest.param(
        {"type": "property_batch", "results": [_FAILS_WITHOUT_TIMESTAMP]},
        "reply results/timestamp: expected number, got nothing",
        id="timestamp-absent",
    ),
    pytest.param(
        {"type": "property_batch", "results": [{**_FAILS_WITHOUT_TIMESTAMP, "timestamp": "1"}]},
        "reply results/timestamp: expected number, got string",
        id="timestamp-string",
    ),
    pytest.param(
        {
            "type": "property_batch",
            "results": [{**_FAILS_WITHOUT_TIMESTAMP, "timestamp": 1, "reason": 7}],
        },
        "reply results/reason: expected string, got number",
        id="reason-number",
    ),
    pytest.param(
        {"type": "property_batch", "results": [{"status": "holds", "property_index": 0}]},
        "reply results/type: expected string, got nothing",
        id="type-absent",
    ),
    pytest.param(
        {
            "type": "property_batch",
            "results": [{"type": 7, "status": "holds", "property_index": 0}],
        },
        "reply results/type: expected string, got number",
        id="type-int",
    ),
    pytest.param(
        {"type": "property_batch", "results": [{"type": "property", "property_index": 0}]},
        "reply results/status: expected string, got nothing",
        id="status-absent",
    ),
    pytest.param(
        {
            "type": "property_batch",
            "results": [{"type": "property", "status": 7, "property_index": 0}],
        },
        "reply results/status: expected string, got number",
        id="status-int",
    ),
]

# Each ill-formed end-of-stream results list, with the text of its refusal.
_MALFORMED_RESULTS = [
    pytest.param(
        {"status": "complete", "warnings": []},
        "reply results: expected array, got nothing",
        id="results-absent",
    ),
    pytest.param(
        {"status": "complete", "results": "r", "warnings": []},
        "reply results: expected array, got string",
        id="results-string",
    ),
    pytest.param(
        {"status": "complete", "results": [42], "warnings": []},
        "reply results: expected object, got number",
        id="entry-number",
    ),
    pytest.param(
        {"status": "complete", "results": [{"status": "holds"}], "warnings": []},
        "reply results/property_index: expected number, got nothing",
        id="property_index-absent",
    ),
    pytest.param(
        {
            "status": "complete",
            "results": [{"status": "holds", "property_index": {"numerator": 0, "denominator": 1}}],
            "warnings": [],
        },
        "reply results/property_index: expected number, got object",
        id="property_index-rational",
    ),
    pytest.param(
        {
            "status": "complete",
            "results": [{"status": "fails", "property_index": 0, "reason": "r"}],
            "warnings": [],
        },
        "reply results/timestamp: expected number, got nothing",
        id="fails-timestamp-absent",
    ),
    pytest.param(
        {
            "status": "complete",
            "results": [{"status": "fails", "property_index": 0, "timestamp": None, "reason": "r"}],
            "warnings": [],
        },
        "reply results/timestamp: expected number, got null",
        id="fails-timestamp-null",
    ),
    pytest.param(
        {
            "status": "complete",
            "results": [
                {"status": "unresolved", "property_index": 0, "timestamp": "1", "reason": "r"}
            ],
            "warnings": [],
        },
        "reply results/timestamp: expected number, got string",
        id="unresolved-timestamp-string",
    ),
    pytest.param(
        {
            "status": "complete",
            "results": [{"status": "fails", "property_index": 0, "timestamp": 1, "reason": 7}],
            "warnings": [],
        },
        "reply results/reason: expected string, got number",
        id="reason-number",
    ),
    pytest.param(
        {"status": "complete", "results": [{"property_index": 0}], "warnings": []},
        "reply results/status: expected string, got nothing",
        id="status-absent",
    ),
    pytest.param(
        {"status": "complete", "results": [{"status": 7, "property_index": 0}], "warnings": []},
        "reply results/status: expected string, got number",
        id="status-int",
    ),
]


def _no_enrichment(_entry: PropertyResultEntry) -> None:
    """Leave an entry as parsed."""


@pytest.mark.parametrize(("reply", "text"), _MALFORMED_PARSED_DBC)
def test_a_broken_parse_dbc_reply_is_refused_at_its_place(reply: Response, text: Prose) -> None:
    """A parseDBC reply's broken ``status``, ``dbc`` or ``warnings`` is refused at its place."""
    with pytest.raises(ProtocolError) as exc_info:
        _ = parse_parsed_dbc_response(reply)
    assert str(exc_info.value) == text


@pytest.mark.parametrize(("reply", "text"), _MALFORMED_FRAMES)
def test_a_broken_frame_reply_is_refused_at_its_place(reply: Response, text: Prose) -> None:
    """A frame reply neither ack, error nor a well-formed property batch is refused at its place.

    A reply carrying ``status`` is refused there; one without is read as a batch by its ``type``.
    """
    with pytest.raises(ProtocolError) as exc_info:
        _ = parse_frame_response(reply)
    assert str(exc_info.value) == text


@pytest.mark.parametrize(("reply", "text"), _MALFORMED_RESULTS)
def test_a_broken_end_of_stream_result_is_refused_at_its_place(
    reply: Response, text: Prose
) -> None:
    """An end-of-stream results list or entry the kernel never writes is refused at its place."""
    with pytest.raises(ProtocolError) as exc_info:
        _ = parse_finalization_results(reply, _no_enrichment)
    assert str(exc_info.value) == text


def test_an_unresolved_result_without_timestamp_is_read() -> None:
    """An end-of-stream ``unresolved`` entry may lack ``timestamp``; only ``fails`` requires it."""
    entry = {"status": "unresolved", "property_index": 0, "reason": "r"}
    reply = {"status": "complete", "results": [entry], "warnings": []}
    assert parse_finalization_results(cast("Response", reply), _no_enrichment) == [
        {"type": "property", **entry}
    ]


@pytest.mark.parametrize(("warning", "text"), _MALFORMED_WARNINGS)
def test_a_warning_kind_and_detail_are_strings(warning: Response, text: Prose) -> None:
    """An end-of-stream warning's ``kind`` or ``detail`` absent or not a string is refused."""
    reply = {"status": "complete", "results": [], "warnings": [warning]}
    with pytest.raises(ProtocolError) as exc_info:
        parse_complete_warnings(cast("Response", reply))
    assert str(exc_info.value) == text


class TestReason:
    """Every ``fails`` and ``unresolved`` entry carries ``reason``, mid-stream and at the end."""

    def test_a_frame_fails_event_without_reason_raises(self) -> None:
        """A property_batch ``fails`` event without ``reason`` is refused at ``results/reason``."""
        event = {"type": "property", "status": "fails", "property_index": 0, "timestamp": 1}
        reply = {"type": "property_batch", "results": [event]}
        with pytest.raises(ProtocolError) as exc_info:
            _ = parse_frame_response(cast("Response", reply))
        assert str(exc_info.value) == "reply results/reason: expected string, got nothing"

    @pytest.mark.parametrize("status", ["fails", "unresolved"])
    def test_an_end_of_stream_entry_without_reason_raises(self, status: EntryStatus) -> None:
        """An end-of-stream ``fails`` or ``unresolved`` entry lacking ``reason`` is refused."""
        entry = {"status": status, "property_index": 0, "timestamp": 1}
        reply = {"status": "complete", "results": [entry], "warnings": []}
        with pytest.raises(ProtocolError) as exc_info:
            _ = parse_finalization_results(cast("Response", reply), _no_enrichment)
        assert str(exc_info.value) == "reply results/reason: expected string, got nothing"


class TestEntryReason:
    """The reason a consumer of parsed entries reads is the parser's, refused when absent."""

    def test_returns_the_reason(self) -> None:
        """An entry's reason comes back as written."""
        entry = {"type": "property", "status": "fails", "property_index": 0, "reason": "r"}
        assert entry_reason(cast("PropertyResultEntry", entry)) == "r"

    def test_refuses_an_entry_built_without_one(self) -> None:
        """An entry built without the parser and lacking ``reason`` is refused at its place."""
        entry = {"type": "property", "status": "unresolved", "property_index": 0}
        with pytest.raises(ProtocolError) as exc_info:
            _ = entry_reason(cast("PropertyResultEntry", entry))
        assert str(exc_info.value) == "reply results/reason: expected string, got nothing"


class TestIssuesPayload:
    """An envelope whose code carries issues holds a well-formed ``issues`` / ``has_errors``."""

    @pytest.mark.parametrize(("extras", "text"), _MALFORMED_ISSUES)
    @pytest.mark.parametrize(
        "code", [ErrorCode.HANDLER_VALIDATION_FAILED, ErrorCode.HANDLER_TEXT_ROUNDTRIP_FAILED]
    )
    def test_build_error_response_raises(
        self, code: ErrorCode, extras: Response, text: Prose
    ) -> None:
        """An ill-formed issues payload is refused at its place rather than being dropped."""
        envelope = {"status": "error", "code": str(code), "message": "m"}
        with pytest.raises(ProtocolError) as exc_info:
            build_error_response(cast("Response", {**envelope, **extras}))
        assert str(exc_info.value) == text

    @pytest.mark.parametrize(("extras", "text"), _MALFORMED_ISSUES)
    def test_dbc_validation_lift_raises(self, extras: Response, text: Prose) -> None:
        """The validation lift refuses an ill-formed payload at its place, not returning."""
        envelope = {"status": "error", "code": "handler_validation_failed", "message": "m"}
        with pytest.raises(ProtocolError) as exc_info:
            raise_if_dbc_validation_failed(cast("Response", {**envelope, **extras}), "m")
        assert str(exc_info.value) == text

    @pytest.mark.parametrize(("extras", "text"), _MALFORMED_ISSUES)
    def test_text_roundtrip_lift_raises(self, extras: Response, text: Prose) -> None:
        """The round-trip lift refuses an ill-formed payload at its place, not returning."""
        envelope = {"status": "error", "code": "handler_text_roundtrip_failed", "message": "m"}
        with pytest.raises(ProtocolError) as exc_info:
            raise_if_text_roundtrip_failed(cast("Response", {**envelope, **extras}), "m")
        assert str(exc_info.value) == text
