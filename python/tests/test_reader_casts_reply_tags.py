# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The response parsers check a reply tag's kind, never its membership in the kernel's set.

The kernel proves every issue severity, every result type and status one of a
fixed set of literals, and every property batch it writes non-empty, so each
reader takes them as written: a tag outside the set passes through, a result
status other than ``fails`` and ``holds`` is read by the ``unresolved`` arm, and
an empty batch is returned empty.  A tag that is not a string, or an issue that
is not an object, is still refused.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

import pytest

from aletheia import ProtocolError
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.client._response_parsers import (
    parse_finalization_results,
    parse_frame_response,
    parse_parsed_dbc_response,
    validate_issue_severities,
)

if TYPE_CHECKING:
    from aletheia.codes import ValidationIssue
    from aletheia.common_types import Prose
    from aletheia.types import JSONValue, PropertyResultEntry, Response


def _no_enrichment(_entry: PropertyResultEntry) -> None:
    """Leave an entry as parsed."""


def test_an_issue_severity_outside_the_set_passes_as_written() -> None:
    """An issue's severity is returned as the kernel wrote it, its membership unchecked."""
    issues = cast("list[ValidationIssue]", [{"severity": "fatal", "code": "c", "detail": "d"}])
    assert validate_issue_severities(issues) == [{"severity": "fatal", "code": "c", "detail": "d"}]


@pytest.mark.parametrize(
    ("warning", "text"),
    [
        pytest.param(42, "reply warnings: expected object, got number", id="int"),
        pytest.param(
            {"code": "c", "detail": "d"},
            "reply warnings/severity: expected string, got nothing",
            id="severity-absent",
        ),
    ],
)
def test_a_parse_dbc_warning_keeps_its_kind_checks(warning: JSONValue, text: Prose) -> None:
    """A parseDBC warning that is not an object, or has no string severity, is refused there."""
    dbc = {"version": "1.0", "messages": [], **empty_dbc_tier2()}
    reply = cast("Response", {"status": "success", "dbc": dbc, "warnings": [warning]})
    with pytest.raises(ProtocolError) as exc_info:
        _ = parse_parsed_dbc_response(reply)
    assert str(exc_info.value) == text


@pytest.mark.parametrize(
    ("issue", "text"),
    [
        pytest.param("fatal", "reply issues: expected object, got string", id="string"),
        pytest.param(
            {"code": "c", "detail": "d", "severity": None},
            "reply issues/severity: expected string, got null",
            id="severity-null",
        ),
    ],
)
def test_an_issue_keeps_its_kind_checks(issue: JSONValue, text: Prose) -> None:
    """An issue that is not an object, or has no string severity, is refused at ``issues``."""
    with pytest.raises(ProtocolError) as exc_info:
        _ = validate_issue_severities(cast("list[ValidationIssue]", [issue]))
    assert str(exc_info.value) == text


def test_an_empty_property_batch_is_returned_empty() -> None:
    """A property_batch with no results is returned as written."""
    reply = cast("Response", {"type": "property_batch", "results": []})
    assert parse_frame_response(reply) == {"type": "property_batch", "results": []}


def test_a_batch_event_type_passes_as_written() -> None:
    """A property_batch event's ``type`` is cast, its membership unchecked."""
    event = {"type": "other", "status": "holds", "property_index": 0}
    reply = cast("Response", {"type": "property_batch", "results": [event]})
    assert parse_frame_response(reply) == {"type": "property_batch", "results": [event]}


def test_a_batch_event_status_outside_the_set_is_read_as_unresolved() -> None:
    """A status other than fails and holds takes the unresolved arm and passes as written."""
    event = {"type": "property", "status": "pending", "property_index": 0, "reason": "r"}
    reply = cast("Response", {"type": "property_batch", "results": [event]})
    assert parse_frame_response(reply) == {"type": "property_batch", "results": [event]}


def test_the_unresolved_arm_of_a_batch_event_requires_its_reason() -> None:
    """The unresolved arm reads ``reason`` whatever the status spells."""
    event = {"type": "property", "status": "pending", "property_index": 0}
    reply = cast("Response", {"type": "property_batch", "results": [event]})
    with pytest.raises(ProtocolError) as exc_info:
        _ = parse_frame_response(reply)
    assert str(exc_info.value) == "reply results/reason: expected string, got nothing"


def test_an_end_of_stream_status_outside_the_set_is_read_as_unresolved() -> None:
    """An end-of-stream status other than fails and holds takes the unresolved arm."""
    seen: list[PropertyResultEntry] = []
    entry = {"status": "pending", "property_index": 0, "timestamp": 7, "reason": "r"}
    reply = cast("Response", {"status": "complete", "results": [entry], "warnings": []})
    expected = {"type": "property", **entry}
    assert parse_finalization_results(reply, seen.append) == [expected]
    assert seen == [expected]


def test_the_unresolved_arm_of_an_end_of_stream_entry_requires_its_reason() -> None:
    """The unresolved arm reads ``reason`` whatever the status spells."""
    entry = {"status": "pending", "property_index": 0}
    reply = cast("Response", {"status": "complete", "results": [entry], "warnings": []})
    with pytest.raises(ProtocolError) as exc_info:
        _ = parse_finalization_results(reply, _no_enrichment)
    assert str(exc_info.value) == "reply results/reason: expected string, got nothing"
