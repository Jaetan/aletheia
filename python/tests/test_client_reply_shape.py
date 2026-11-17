# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A key the kernel writes on every reply is read as required, never defaulted.

The client's readers keep the kind checks (an array, a string, a boolean), hold
an issue's severity and code to their words, and drop the range checks the
kernel proves; a reply without a key the kernel always writes is malformed and
raises :class:`~aletheia.ProtocolError` reading ``reply <path>: expected
<what>, got <what came>``, rather than a value the binding substitutes.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, Final, Literal, NamedTuple, NewType, TypedDict, cast

import pytest
from _dbc_helpers import KernelReply, dbc

from aletheia import (
    AletheiaClient,
    AletheiaError,
    FrameResult,
    InputBoundExceededError,
    MockBackend,
    ProtocolError,
)
from aletheia.codes import IssueCode, IssueSeverity
from aletheia.common_types import Prose
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from aletheia.codes import ValidationIssue
    from aletheia.types import (
        ErrorResponse,
        JSONValue,
        ParsedDBCResponse,
        PropertyBatchResponse,
    )

type Entry = Literal["validateDBC", "formatDBC", "formatDBCText", "extractAllSignals"]
type Malformation = Literal["absent", "not-a-string"]
type ParseRoute = Literal["parseDBC", "parseDBCText"]
type ExtractionList = Literal["values", "errors", "absent"]

_DBC: Final = dbc([])

_ENVELOPES: Final = {
    "absent": '{"status": "error", "code": "handler_no_dbc"}',
    "not-a-string": '{"status": "error", "code": "handler_no_dbc", "message": 7}',
}
_MESSAGE_CAME: Final = {"absent": "nothing", "not-a-string": "number"}


def _call(client: AletheiaClient, entry: Entry) -> None:
    """Run the client method that reads *entry*'s reply."""
    match entry:
        case "validateDBC":
            client.validate_dbc(_DBC)
        case "formatDBC":
            client.format_dbc()
        case "formatDBCText":
            client.format_dbc_text(_DBC)
        case "extractAllSignals":
            client.extract_signals(0x100, DLCCode(0), b"")


def _parse(client: AletheiaClient, route: ParseRoute) -> None:
    """Load a DBC through *route*, whose reply the backend holds."""
    match route:
        case "parseDBC":
            client.parse_dbc(_DBC)
        case "parseDBCText":
            client.parse_dbc_text('VERSION ""\n')


@pytest.mark.parametrize(
    "entry", ["validateDBC", "formatDBC", "formatDBCText", "extractAllSignals"]
)
@pytest.mark.parametrize("shape", ["absent", "not-a-string"])
def test_an_error_envelope_without_a_string_message_is_refused(
    entry: Entry, shape: Malformation
) -> None:
    """An error envelope whose ``message`` is absent or not a string is refused at ``message``."""
    with (
        AletheiaClient(backend=MockBackend([_ENVELOPES[shape].encode()])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        _call(client, entry)
    assert (str(excinfo.value), excinfo.value.code) == (
        f"reply message: expected string, got {_MESSAGE_CAME[shape]}",
        None,
    )


@pytest.mark.parametrize(
    "entry", ["validateDBC", "formatDBC", "formatDBCText", "extractAllSignals"]
)
@pytest.mark.parametrize(
    ("envelope", "came"),
    [
        pytest.param(
            KernelReply(b'{"status": "error", "code": "my_code", "message": "m"}'),
            '"my_code"',
            id="unknown",
        ),
        pytest.param(KernelReply(b'{"status": "error", "message": "m"}'), "nothing", id="absent"),
        pytest.param(
            KernelReply(b'{"status": "error", "code": 7, "message": "m"}'), "number", id="number"
        ),
    ],
)
def test_an_error_code_outside_the_error_codes_is_refused(
    entry: Entry, envelope: KernelReply, came: Prose
) -> None:
    """An error envelope whose ``code`` is no error code is refused at ``code``, carrying none."""
    with (
        AletheiaClient(backend=MockBackend([envelope])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        _call(client, entry)
    assert (str(excinfo.value), excinfo.value.code) == (
        f"reply code: expected an error code, got {came}",
        None,
    )


def test_a_bound_triple_is_read_without_a_range_check() -> None:
    """A bound refusal's counts lift whatever their value: the kernel proves them positive."""
    envelope = (
        '{"status": "error", "code": "input_bound_exceeded", "message": "too deep",'
        ' "bound_kind": "nesting_depth", "observed": 0, "limit": 64}'
    )
    with (
        AletheiaClient(backend=MockBackend([envelope.encode()])) as client,
        pytest.raises(AletheiaError) as excinfo,
    ):
        client.validate_dbc(_DBC)
    assert isinstance(excinfo.value, InputBoundExceededError)
    assert (excinfo.value.kind, excinfo.value.observed, excinfo.value.limit) == (
        "nesting_depth",
        0,
        64,
    )


@pytest.mark.parametrize("route", ["parseDBC", "parseDBCText"])
def test_a_parsed_message_without_extended_is_refused(route: ParseRoute) -> None:
    """A parsed DBC message without ``extended`` raises rather than reading it as standard."""
    reply = (
        '{"status": "success", "warnings": [], "dbc": {"version": "", "messages":'
        ' [{"id": 256, "name": "Msg", "dlc": 8, "sender": "ECU", "signals": []}]}}'
    )
    with (
        AletheiaClient(backend=MockBackend([reply.encode()])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        _parse(client, route)
    assert str(excinfo.value) == "reply dbc/messages/extended: expected boolean, got nothing"


def test_a_format_dbc_text_success_without_issues_is_refused() -> None:
    """A formatDBCText success reply without ``issues`` raises rather than reading none."""
    reply = '{"status": "success", "text": "VERSION \\"\\"\\n"}'
    with (
        AletheiaClient(backend=MockBackend([reply.encode()])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        client.format_dbc_text(_DBC)
    assert str(excinfo.value) == "reply issues: expected array, got nothing"


@pytest.mark.parametrize("missing", ["values", "errors", "absent"])
def test_an_extraction_reply_without_a_list_is_refused(missing: ExtractionList) -> None:
    """An extraction reply without one of its three lists raises naming that list."""
    lists = ", ".join(f'"{key}": []' for key in ("values", "errors", "absent") if key != missing)
    reply = f'{{"status": "success", {lists}}}'
    with (
        AletheiaClient(backend=MockBackend([reply.encode()])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        client.extract_signals(0x100, DLCCode(0), b"")
    assert str(excinfo.value) == f"reply {missing}: expected array, got nothing"


@pytest.mark.parametrize("read", ["violation", "satisfactions"])
def test_a_property_batch_without_results_is_refused(
    read: Literal["violation", "satisfactions"],
) -> None:
    """A property_batch without ``results`` raises from either reader rather than reading none."""
    result = FrameResult(
        frame_index=0,
        timestamp=1000,
        can_id=0x100,
        extended=False,
        response=cast("PropertyBatchResponse", {"type": "property_batch"}),
    )
    with pytest.raises(ProtocolError) as excinfo:
        _ = result.violation if read == "violation" else result.satisfactions
    assert str(excinfo.value) == "reply results: expected array, got nothing"


_BOUND: Final = {"status": "error", "code": "input_bound_exceeded", "message": "too deep"}


class _BoundTriple(TypedDict, total=False):
    """The part of a bound refusal's triple a case writes."""

    bound_kind: JSONValue
    observed: JSONValue
    limit: JSONValue


@pytest.mark.parametrize(
    ("triple", "said"),
    [
        (
            {"observed": 70, "limit": 64},
            Prose("reply bound_kind: expected string, got nothing"),
        ),
        (
            {"bound_kind": 7, "observed": 70, "limit": 64},
            Prose("reply bound_kind: expected string, got number"),
        ),
        (
            {"bound_kind": "nesting_depth", "limit": 64},
            Prose("reply observed: expected number, got nothing"),
        ),
        (
            {"bound_kind": "nesting_depth", "observed": True, "limit": 64},
            Prose("reply observed: expected number, got boolean"),
        ),
        (
            {"bound_kind": "nesting_depth", "observed": 70},
            Prose("reply limit: expected number, got nothing"),
        ),
        (
            {"bound_kind": "nesting_depth", "observed": 70, "limit": "64"},
            Prose("reply limit: expected number, got string"),
        ),
    ],
    ids=[
        "no-kind",
        "number-kind",
        "no-observed",
        "boolean-observed",
        "no-limit",
        "string-limit",
    ],
)
def test_a_partial_bound_triple_is_refused_at_its_broken_key(
    triple: _BoundTriple, said: Prose
) -> None:
    """A bound refusal carrying part of its triple is refused at the key that is broken."""
    envelope = json.dumps({**_BOUND, **triple}).encode()
    with (
        AletheiaClient(backend=MockBackend([envelope])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        client.validate_dbc(_DBC)
    assert (str(excinfo.value), excinfo.value.code) == (said, None)


class _ExtractionChange(TypedDict, total=False):
    """The keys of an extraction reply a case writes over a well-formed one."""

    status: JSONValue
    values: JSONValue
    errors: JSONValue
    absent: JSONValue


_EXTRACTION: Final[_ExtractionChange] = {
    "status": "success",
    "values": [],
    "errors": [],
    "absent": [],
}


@pytest.mark.parametrize(
    ("change", "said"),
    [
        ({"status": "weird"}, Prose('reply status: expected "success" or "error", got "weird"')),
        ({"status": 0}, Prose('reply status: expected "success" or "error", got number')),
        ({"values": 0}, Prose("reply values: expected array, got number")),
        ({"values": [3]}, Prose("reply values: expected object, got number")),
        ({"values": [{"value": 1}]}, Prose("reply values/name: expected string, got nothing")),
        (
            {"values": [{"name": "S"}]},
            Prose("reply values/value: expected a rational, got nothing"),
        ),
        (
            {"values": [{"name": "S", "value": "x"}]},
            Prose("reply values/value: expected a rational, got string"),
        ),
        ({"errors": [3]}, Prose("reply errors: expected object, got number")),
        ({"errors": [{"error": "e"}]}, Prose("reply errors/name: expected string, got nothing")),
        (
            {"errors": [{"name": "S", "error": 0}]},
            Prose("reply errors/error: expected string, got number"),
        ),
        ({"absent": [0]}, Prose("reply absent: expected string, got number")),
    ],
    ids=[
        "status-word",
        "status-number",
        "values-number",
        "value-entry-number",
        "value-no-name",
        "value-no-value",
        "value-string",
        "error-entry-number",
        "error-no-name",
        "error-number-error",
        "absent-entry-number",
    ],
)
def test_an_extraction_reply_place_is_refused(change: _ExtractionChange, said: Prose) -> None:
    """A broken place of an extraction reply is refused naming that place."""
    reply = json.dumps({**_EXTRACTION, **change}).encode()
    with (
        AletheiaClient(backend=MockBackend([reply])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        client.extract_signals(0x100, DLCCode(0), b"")
    assert str(excinfo.value) == said


def test_an_extraction_reply_without_status_is_refused() -> None:
    """An extraction reply without ``status`` is refused at the status word."""
    reply = json.dumps({"values": [], "errors": [], "absent": []}).encode()
    with (
        AletheiaClient(backend=MockBackend([reply])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        client.extract_signals(0x100, DLCCode(0), b"")
    assert str(excinfo.value) == 'reply status: expected "success" or "error", got nothing'


def test_an_end_of_stream_reply_with_another_status_is_refused() -> None:
    """An end-of-stream reply whose status is neither word it carries is refused."""
    with (
        AletheiaClient(backend=MockBackend([b'{"status": "weird"}'])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        _ = client.end_stream()
    assert str(excinfo.value) == 'reply status: expected "complete" or "error", got "weird"'


type IssueRoute = Literal["validateDBC", "formatDBCText", "parseDBC", "parseDBCText", "refusal"]
type IssuePlace = Literal["issues", "warnings"]
type IssueKey = Literal["code", "detail", "severity"]

# A reply's JSON text with ``{}`` where its one issue goes.
ReplyTemplate = NewType("ReplyTemplate", str)


class _IssueReply(NamedTuple):
    """A route's reply around its one issue, and the place of its issue list."""

    template: ReplyTemplate
    place: IssuePlace


_PARSED: Final = ReplyTemplate(
    '{{"status": "success", "dbc": {{"version": "", "messages": [], "signalGroups": [],'
    + ' "environmentVars": [], "valueTables": [], "nodes": [], "comments": [],'
    + ' "attributes": [], "unresolvedValueDescs": []}}, "warnings": [{}]}}'
)
# Every route whose reply carries issues: the validation reply, the text of a
# DBC with its round-trip issues, a parsed DBC's warnings on either load route,
# and a load's refusal carrying its validation issues.
_ISSUE_REPLIES: Final[dict[IssueRoute, _IssueReply]] = {
    "validateDBC": _IssueReply(
        ReplyTemplate('{{"status": "validation", "has_errors": false, "issues": [{}]}}'), "issues"
    ),
    "formatDBCText": _IssueReply(
        ReplyTemplate('{{"status": "success", "text": "", "issues": [{}]}}'), "issues"
    ),
    "parseDBC": _IssueReply(_PARSED, "warnings"),
    "parseDBCText": _IssueReply(_PARSED, "warnings"),
    "refusal": _IssueReply(
        ReplyTemplate(
            '{{"status": "error", "code": "handler_validation_failed", "message": "m",'
            + ' "has_errors": true, "issues": [{}]}}'
        ),
        "issues",
    ),
}
_ISSUE_ROUTES: Final = tuple(_ISSUE_REPLIES)


def _issues_of(reply: ParsedDBCResponse | ErrorResponse) -> list[ValidationIssue]:
    """Name the issues a DBC load answered: its warnings, or the issues of its refusal."""
    if reply["status"] == "success":
        return reply["warnings"]
    assert "issues" in reply, reply
    return reply["issues"]


def _read_issues(route: IssueRoute, issue: JSONValue) -> list[ValidationIssue]:
    """Read *issue* through *route*, the backend answering with the route's reply around it."""
    reply = _ISSUE_REPLIES[route].template.format(json.dumps(issue))
    with AletheiaClient(backend=MockBackend([reply.encode()])) as client:
        match route:
            case "validateDBC":
                return client.validate_dbc(_DBC)["issues"]
            case "formatDBCText":
                return client.format_dbc_text(_DBC)["issues"]
            case "parseDBC" | "refusal":
                return _issues_of(client.parse_dbc(_DBC))
            case "parseDBCText":
                return _issues_of(client.parse_dbc_text('VERSION ""\n'))


def _refusal(route: IssueRoute, issue: JSONValue) -> Prose:
    """Read *issue* through *route*, and return the text of the refusal it raises."""
    with pytest.raises(ProtocolError) as excinfo:
        _ = _read_issues(route, issue)
    return Prose(str(excinfo.value))


@pytest.mark.parametrize("route", _ISSUE_ROUTES)
@pytest.mark.parametrize(
    ("severity", "code"),
    [
        (IssueSeverity.ERROR, IssueCode.FACTOR_ZERO),
        (IssueSeverity.WARNING, IssueCode.EMPTY_MESSAGE),
    ],
)
def test_an_issue_is_read_as_the_members_its_words_name(
    route: IssueRoute, severity: IssueSeverity, code: IssueCode
) -> None:
    """An issue's severity and code are read as the members their words name."""
    issue: JSONValue = {"code": code.value, "detail": "d", "severity": severity.value}
    [read] = _read_issues(route, issue)
    assert read == {"severity": severity, "code": code, "detail": "d"}
    assert (type(read["severity"]), type(read["code"])) == (IssueSeverity, IssueCode)


@pytest.mark.parametrize("route", _ISSUE_ROUTES)
def test_an_issue_not_an_object_is_refused(route: IssueRoute) -> None:
    """An issue that is not an object is refused at its list's place."""
    place = _ISSUE_REPLIES[route].place
    assert _refusal(route, "fatal") == f"reply {place}: expected object, got string"


@pytest.mark.parametrize("route", _ISSUE_ROUTES)
@pytest.mark.parametrize(
    ("issue", "came"),
    [
        pytest.param({"code": "factor_zero", "severity": "warning"}, "nothing", id="absent"),
        pytest.param(
            {"code": "factor_zero", "detail": 0, "severity": "warning"}, "number", id="number"
        ),
    ],
)
def test_an_issue_detail_not_a_string_is_refused(
    route: IssueRoute, issue: JSONValue, came: Prose
) -> None:
    """An issue whose ``detail`` is absent or a number is refused at its place."""
    place = _ISSUE_REPLIES[route].place
    assert _refusal(route, issue) == f"reply {place}/detail: expected string, got {came}"


@pytest.mark.parametrize("route", _ISSUE_ROUTES)
@pytest.mark.parametrize(
    ("issue", "came"),
    [
        pytest.param(
            {"code": "factor_zero", "detail": "d", "severity": "fatal"}, '"fatal"', id="unknown"
        ),
        pytest.param({"code": "factor_zero", "detail": "d"}, "nothing", id="absent"),
        pytest.param({"code": "factor_zero", "detail": "d", "severity": 0}, "number", id="number"),
    ],
)
def test_an_issue_severity_outside_its_words_is_refused(
    route: IssueRoute, issue: JSONValue, came: Prose
) -> None:
    """An issue's severity is ``error`` or ``warning``; anything else is refused at its place."""
    place = _ISSUE_REPLIES[route].place
    assert _refusal(route, issue) == (
        f'reply {place}/severity: expected "error" or "warning", got {came}'
    )


@pytest.mark.parametrize("route", _ISSUE_ROUTES)
@pytest.mark.parametrize(
    ("issue", "came"),
    [
        pytest.param(
            {"code": "some_future_code", "detail": "d", "severity": "warning"},
            '"some_future_code"',
            id="unknown",
        ),
        pytest.param({"detail": "d", "severity": "warning"}, "nothing", id="absent"),
        pytest.param({"code": 0, "detail": "d", "severity": "warning"}, "number", id="number"),
    ],
)
def test_an_issue_code_outside_the_issue_codes_is_refused(
    route: IssueRoute, issue: JSONValue, came: Prose
) -> None:
    """An issue's code is one of the ``IssueCode`` words; anything else is refused at its place."""
    place = _ISSUE_REPLIES[route].place
    assert _refusal(route, issue) == f"reply {place}/code: expected an issue code, got {came}"


@pytest.mark.parametrize("route", _ISSUE_ROUTES)
@pytest.mark.parametrize(
    ("issue", "key", "expected"),
    [
        pytest.param({}, "code", "an issue code", id="code"),
        pytest.param({"code": "factor_zero"}, "detail", "string", id="detail"),
    ],
)
def test_an_issue_is_refused_at_its_first_broken_place(
    route: IssueRoute, issue: JSONValue, key: IssueKey, expected: Prose
) -> None:
    """An issue's code is read first, then its detail, then its severity."""
    place = _ISSUE_REPLIES[route].place
    assert _refusal(route, issue) == f"reply {place}/{key}: expected {expected}, got nothing"
