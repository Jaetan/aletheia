# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A key the kernel always writes is refused when a reply lacks it.

Each reader in ``aletheia.client._response_parsers`` raises ``ProtocolError``
on such a reply rather than substituting a value or dropping the field.
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

# Each ill-formed issues payload, with the text its refusal carries.
_MALFORMED_ISSUES = [
    pytest.param({"issues": [_ISSUE]}, "Expected bool 'has_errors'", id="has_errors-absent"),
    pytest.param(
        {"has_errors": 1, "issues": [_ISSUE]}, "Expected bool 'has_errors'", id="has_errors-int"
    ),
    pytest.param({"has_errors": True}, "Expected 'issues' to be a list", id="issues-absent"),
    pytest.param(
        {"has_errors": True, "issues": "nope"},
        "Expected 'issues' to be a list",
        id="issues-nonlist",
    ),
    pytest.param(
        {"has_errors": True, "issues": [42]},
        "Expected every 'issues' entry to be an object",
        id="issue-nonobject",
    ),
    pytest.param(
        {"has_errors": True, "issues": [{"severity": "error", "detail": "d"}]},
        "Expected every 'issues' entry to be an object",
        id="code-absent",
    ),
    pytest.param(
        {"has_errors": True, "issues": [{"severity": "error", "code": "c", "detail": 7}]},
        "Expected every 'issues' entry to be an object",
        id="detail-nonstring",
    ),
    pytest.param(
        {"has_errors": True, "issues": [{"severity": "fatal", "code": "c", "detail": "d"}]},
        "Unknown validation severity",
        id="severity-unknown",
    ),
]

# Each ill-formed end-of-stream warning entry, with the text its refusal carries.
_MALFORMED_WARNINGS = [
    pytest.param(
        {"property_index": 0, "detail": "Speed"},
        "Expected string 'kind' in end-of-stream warning entry, got NoneType",
        id="kind-absent",
    ),
    pytest.param(
        {"kind": 7, "property_index": 0, "detail": "Speed"},
        "Expected string 'kind' in end-of-stream warning entry, got int",
        id="kind-int",
    ),
    pytest.param(
        {"kind": "uncached_atom", "property_index": 0},
        "Expected string 'detail' in end-of-stream warning entry, got NoneType",
        id="detail-absent",
    ),
    pytest.param(
        {"kind": "uncached_atom", "property_index": 0, "detail": 7},
        "Expected string 'detail' in end-of-stream warning entry, got int",
        id="detail-int",
    ),
]


def _no_enrichment(_entry: PropertyResultEntry) -> None:
    """Leave an entry as parsed."""


def test_a_parse_dbc_reply_without_warnings_raises() -> None:
    """A parseDBC success reply without ``warnings`` raises ``ProtocolError`` naming it."""
    dbc = {"version": "1.0", "messages": [], **empty_dbc_tier2()}
    with pytest.raises(ProtocolError, match="Expected 'warnings' in parseDBC success reply"):
        parse_parsed_dbc_response(cast("Response", {"status": "success", "dbc": dbc}))


class TestCompleteWarnings:
    """The end-of-stream complete reply carries ``warnings``, each with ``kind`` and ``detail``."""

    def test_absent_warnings_raises(self) -> None:
        """A complete reply without ``warnings`` raises ``ProtocolError`` naming it."""
        with pytest.raises(
            ProtocolError, match="Expected 'warnings' in end-of-stream complete reply"
        ):
            parse_complete_warnings(cast("Response", {"status": "complete", "results": []}))

    @pytest.mark.parametrize(("warning", "match"), _MALFORMED_WARNINGS)
    def test_kind_and_detail_are_strings(self, warning: Response, match: Prose) -> None:
        """A warning whose ``kind`` or ``detail`` is absent or not a string raises."""
        reply = {"status": "complete", "results": [], "warnings": [warning]}
        with pytest.raises(ProtocolError, match=match):
            parse_complete_warnings(cast("Response", reply))


def test_a_fails_result_without_timestamp_raises() -> None:
    """A ``fails`` result entry without ``timestamp`` raises ``ProtocolError`` naming it."""
    reply = {
        "status": "complete",
        "results": [{"status": "fails", "property_index": 0, "reason": "r"}],
        "warnings": [],
    }
    with pytest.raises(
        ProtocolError,
        match="Expected 'timestamp' in finalization result entry with status 'fails'",
    ):
        parse_finalization_results(cast("Response", reply), _no_enrichment)


class TestReason:
    """Every ``fails`` and ``unresolved`` entry carries ``reason``, mid-stream and at the end."""

    def test_a_frame_fails_event_without_reason_raises(self) -> None:
        """A property_batch ``fails`` event without ``reason`` raises naming it."""
        event = {"type": "property", "status": "fails", "property_index": 0, "timestamp": 1}
        reply = {"type": "property_batch", "results": [event]}
        with pytest.raises(
            ProtocolError, match="Expected string 'reason' in property_batch 'fails'"
        ):
            _ = parse_frame_response(cast("Response", reply))

    @pytest.mark.parametrize("status", ["fails", "unresolved"])
    def test_an_end_of_stream_entry_without_reason_raises(self, status: EntryStatus) -> None:
        """An end-of-stream ``fails`` or ``unresolved`` entry lacking ``reason`` raises."""
        entry = {"status": status, "property_index": 0, "timestamp": 1}
        reply = {"status": "complete", "results": [entry], "warnings": []}
        with pytest.raises(
            ProtocolError,
            match=f"Expected string 'reason' in finalization result entry with status '{status}'",
        ):
            _ = parse_finalization_results(cast("Response", reply), _no_enrichment)


class TestEntryReason:
    """The reason a consumer of parsed entries reads is the parser's, refused when absent."""

    def test_returns_the_reason(self) -> None:
        """An entry's reason comes back as written."""
        entry = {"type": "property", "status": "fails", "property_index": 0, "reason": "r"}
        assert entry_reason(cast("PropertyResultEntry", entry)) == "r"

    def test_refuses_an_entry_built_without_one(self) -> None:
        """An entry built without the parser and lacking ``reason`` raises naming its status."""
        entry = {"type": "property", "status": "unresolved", "property_index": 0}
        with pytest.raises(ProtocolError, match="string 'reason' in 'unresolved' result entry"):
            _ = entry_reason(cast("PropertyResultEntry", entry))


class TestIssuesPayload:
    """An envelope whose code carries issues holds a well-formed ``issues`` / ``has_errors``."""

    @pytest.mark.parametrize(("extras", "match"), _MALFORMED_ISSUES)
    @pytest.mark.parametrize(
        "code", [ErrorCode.HANDLER_VALIDATION_FAILED, ErrorCode.HANDLER_TEXT_ROUNDTRIP_FAILED]
    )
    def test_build_error_response_raises(
        self, code: ErrorCode, extras: Response, match: Prose
    ) -> None:
        """An ill-formed issues payload raises ``ProtocolError`` rather than being dropped."""
        envelope = {"status": "error", "code": str(code), "message": "m"}
        with pytest.raises(ProtocolError, match=match):
            build_error_response(cast("Response", {**envelope, **extras}))

    @pytest.mark.parametrize(("extras", "match"), _MALFORMED_ISSUES)
    def test_dbc_validation_lift_raises(self, extras: Response, match: Prose) -> None:
        """The validation lift raises ``ProtocolError`` on an ill-formed payload, not returning."""
        envelope = {"status": "error", "code": "handler_validation_failed", "message": "m"}
        with pytest.raises(ProtocolError, match=match):
            raise_if_dbc_validation_failed(cast("Response", {**envelope, **extras}), "m")

    @pytest.mark.parametrize(("extras", "match"), _MALFORMED_ISSUES)
    def test_text_roundtrip_lift_raises(self, extras: Response, match: Prose) -> None:
        """The round-trip lift raises ``ProtocolError`` on an ill-formed payload, not returning."""
        envelope = {"status": "error", "code": "handler_text_roundtrip_failed", "message": "m"}
        with pytest.raises(ProtocolError, match=match):
            raise_if_text_roundtrip_failed(cast("Response", {**envelope, **extras}), "m")
