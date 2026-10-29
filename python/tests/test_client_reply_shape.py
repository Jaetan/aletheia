# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A key the kernel writes on every reply is read as required, never defaulted.

The client's readers keep the kind checks (a list, a string, a bool) and drop
the range checks the kernel proves; a reply without a key the kernel always
writes is malformed and raises :class:`~aletheia.ProtocolError` naming the key
and the reply, rather than a value the binding substitutes.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, Literal, cast

import pytest
from _dbc_helpers import dbc

from aletheia import (
    AletheiaClient,
    AletheiaError,
    FrameResult,
    InputBoundExceededError,
    MockBackend,
    ProtocolError,
)
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from aletheia.types import PropertyBatchResponse

type Entry = Literal["validateDBC", "formatDBC", "formatDBCText", "extractAllSignals"]
type Malformation = Literal["absent", "not-a-string"]
type ParseRoute = Literal["parseDBC", "parseDBCText"]
type ExtractionList = Literal["values", "errors", "absent"]

_DBC: Final = dbc([])

_ENVELOPES: Final = {
    "absent": '{"status": "error", "code": "my_code"}',
    "not-a-string": '{"status": "error", "code": "my_code", "message": 7}',
}


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
    """An error envelope whose ``message`` is absent or not a string raises naming the key."""
    with (
        AletheiaClient(backend=MockBackend([_ENVELOPES[shape].encode()])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        _call(client, entry)
    assert (str(excinfo.value), excinfo.value.code) == (
        f"Expected 'message' field in {entry} error response",
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
        pytest.raises(ProtocolError, match="'extended'"),
    ):
        _parse(client, route)


def test_a_format_dbc_text_success_without_issues_is_refused() -> None:
    """A formatDBCText success reply without ``issues`` raises rather than reading none."""
    reply = '{"status": "success", "text": "VERSION \\"\\"\\n"}'
    with (
        AletheiaClient(backend=MockBackend([reply.encode()])) as client,
        pytest.raises(ProtocolError) as excinfo,
    ):
        client.format_dbc_text(_DBC)
    assert str(excinfo.value) == "Expected 'issues' field in formatDBCText response"


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
    assert str(excinfo.value) == f"Expected '{missing}' list field in extractAllSignals response"


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
    assert str(excinfo.value) == "Expected 'results' field in property_batch response"
