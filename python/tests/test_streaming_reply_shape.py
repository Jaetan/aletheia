# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The streaming reader refuses a reply missing what the kernel always writes.

``send_frame`` and ``end_stream`` enrich every fails or unresolved entry with
the kernel's ``reason`` and the signals of the last frames.  The kernel writes
``reason`` on each such entry and answers every extraction of a streamed
frame, so an entry without its reason, or an extraction reply the reader
refuses, raises ``ProtocolError`` from the call that read it.  ``MockBackend``
serves the canned replies; with no DBC loaded, each extraction reads the next
queued JSON reply.
"""

from __future__ import annotations

import json
import logging
from typing import TYPE_CHECKING, Literal

import pytest

from aletheia import AletheiaClient, MockBackend, ProtocolError, Signal
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from _dbc_helpers import KernelReply

    from aletheia.common_types import Prose

# ``set_properties`` renders each formula's threshold through the kernel.
pytestmark = pytest.mark.usefixtures("rts_up")

_SUCCESS_REPLY = b'{"status":"success"}'
_ACK_REPLY = b'{"status":"ack"}'
_REASON = "Atomic: predicate failed"
# The kernel's fails event for property 0, at timestamp 0.
_FAILS_EVENT = {"type": "property", "status": "fails", "property_index": 0, "timestamp": 0}
_FAILS_BATCH_REPLY = json.dumps(
    {"type": "property_batch", "results": [{**_FAILS_EVENT, "reason": _REASON}]}
).encode()
_REFUSED_EXTRACTION_REPLY = json.dumps(
    {"status": "success", "values": "SigA", "errors": [], "absent": []}
).encode()


def _queue_session(backend: MockBackend) -> None:
    """Queue the setProperties and startStream replies, in order."""
    for reply in (_SUCCESS_REPLY, _SUCCESS_REPLY):
        backend.queue_response(reply)


def _start(client: AletheiaClient) -> None:
    """Register one property over SigA and start the stream."""
    client.set_properties([Signal("SigA").greater_than(10).eventually().to_dict()])
    client.start_stream()


def test_a_send_frame_fails_event_without_its_reason_is_refused() -> None:
    """A property_batch fails event carrying no reason raises ProtocolError naming it."""
    backend = MockBackend()
    _queue_session(backend)
    backend.queue_response(
        json.dumps({"type": "property_batch", "results": [_FAILS_EVENT]}).encode()
    )
    with AletheiaClient(backend=backend) as client:
        _start(client)
        with pytest.raises(ProtocolError) as exc_info:
            client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        assert str(exc_info.value) == "reply results/reason: expected string, got nothing"


@pytest.mark.parametrize("status", ["fails", "unresolved"])
def test_an_end_stream_entry_without_its_reason_is_refused(
    status: Literal["fails", "unresolved"],
) -> None:
    """A fails or unresolved finalization entry carrying no reason raises ProtocolError."""
    backend = MockBackend()
    _queue_session(backend)
    backend.queue_response(
        json.dumps(
            {
                "status": "complete",
                "results": [
                    {"type": "property", "status": status, "property_index": 0, "timestamp": 0}
                    if status == "fails"
                    else {"type": "property", "status": status, "property_index": 0}
                ],
                "warnings": [],
            }
        ).encode()
    )
    with AletheiaClient(backend=backend) as client:
        _start(client)
        with pytest.raises(ProtocolError) as exc_info:
            client.end_stream()
        assert str(exc_info.value) == "reply results/reason: expected string, got nothing"


def test_a_send_frame_error_reply_logs_its_own_status(caplog: pytest.LogCaptureFixture) -> None:
    """The DEBUG frame.processed event of an error reply names the reply's status."""
    backend = MockBackend()
    _queue_session(backend)
    backend.queue_response(
        json.dumps(
            {
                "status": "error",
                "code": "handler_non_monotonic_timestamp",
                "message": "Timestamp went backwards",
            }
        ).encode()
    )
    with (
        caplog.at_level(logging.DEBUG, logger="aletheia"),
        AletheiaClient(backend=backend) as client,
    ):
        _start(client)
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
    processed = [
        record.getMessage()
        for record in caplog.records
        if record.getMessage().startswith("frame.processed")
    ]
    assert processed == ["frame.processed ts=0 canId=256 extended=false response=error"]


def test_a_send_frame_extraction_reply_the_reader_refuses_raises() -> None:
    """A per-frame enrichment's extraction reply the reader refuses raises from send_frame."""
    backend = MockBackend()
    _queue_session(backend)
    backend.queue_response(_FAILS_BATCH_REPLY)
    backend.queue_response(_REFUSED_EXTRACTION_REPLY)
    with AletheiaClient(backend=backend) as client:
        _start(client)
        with pytest.raises(ProtocolError) as exc_info:
            client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        assert str(exc_info.value) == "reply values: expected array, got string"


def test_an_end_stream_extraction_reply_the_reader_refuses_raises() -> None:
    """An end-of-stream enrichment's extraction reply the reader refuses raises from end_stream."""
    backend = MockBackend()
    _queue_session(backend)
    backend.queue_response(_ACK_REPLY)
    backend.queue_response(
        json.dumps(
            {
                "status": "complete",
                "results": [
                    {
                        "type": "property",
                        "status": "fails",
                        "property_index": 0,
                        "timestamp": 0,
                        "reason": _REASON,
                    }
                ],
                "warnings": [],
            }
        ).encode()
    )
    backend.queue_response(_REFUSED_EXTRACTION_REPLY)
    with AletheiaClient(backend=backend) as client:
        _start(client)
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        with pytest.raises(ProtocolError) as exc_info:
            client.end_stream()
        assert str(exc_info.value) == "reply values: expected array, got string"


@pytest.mark.parametrize(
    ("reply", "text"),
    [
        pytest.param(
            b'{"status":"weird"}',
            'reply status: expected "success" or "error", got "weird"',
            id="other-word",
        ),
        pytest.param(
            b"{}", 'reply status: expected "success" or "error", got nothing', id="absent"
        ),
    ],
)
def test_a_start_stream_reply_neither_success_nor_error_is_refused(
    reply: KernelReply, text: Prose
) -> None:
    """A startStream reply whose status is another word or absent is refused at ``status``."""
    backend = MockBackend()
    backend.queue_response(reply)
    with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as exc_info:
        _ = client.start_stream()
    assert str(exc_info.value) == text


def test_an_error_event_reply_neither_ack_nor_error_is_refused() -> None:
    """A sendError reply whose status is another word is refused at ``status``."""
    backend = MockBackend()
    backend.queue_response(_SUCCESS_REPLY)
    with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as exc_info:
        _ = client.send_error(0)
    assert str(exc_info.value) == 'reply status: expected "ack" or "error", got "success"'


def test_a_remote_event_reply_without_a_word_status_is_refused() -> None:
    """A sendRemote reply whose status is not a string is refused at ``status``."""
    backend = MockBackend()
    backend.queue_response(b'{"status":1}')
    with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as exc_info:
        _ = client.send_remote(0, 0x100)
    assert str(exc_info.value) == 'reply status: expected "ack" or "error", got number'
