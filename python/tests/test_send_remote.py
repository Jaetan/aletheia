# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What ``send_remote`` refuses outside a session and what it logs of a remote frame.

A client not entered refuses a remote frame with the guard ``StateError`` and
calls no backend. An entered client logs the DEBUG ``remote_event.sent`` event
of each remote frame the kernel acknowledges: the byte-exact ack logs the
frame's timestamp, identifier and extended bit, and a kernel error logs the
frame's timestamp and the error's code before it is raised. ``MockBackend``
serves the canned replies.
"""

from __future__ import annotations

import logging

import pytest
from _send_logging import (
    ACK_REPLY,
    REFUSAL_CODE,
    REFUSAL_MESSAGE,
    REFUSAL_REPLY,
    EventName,
    debug_session,
    logged,
)
from _stream_helpers import refused_outside_a_session

from aletheia import MockBackend, ProtocolError

# A 29-bit identifier past the 11-bit range, which only an extended frame carries.
_EXTENDED_ID = 0x18FEF100
_EVENT = EventName("remote_event.sent")


def test_a_remote_frame_outside_a_session_is_refused_with_the_guard_message() -> None:
    """A client not entered refuses with the guard StateError and calls no backend."""
    refused, backend = refused_outside_a_session(lambda client: client.send_remote(0, 0x100))
    assert str(refused) == "Client not initialized \N{EM DASH} use 'with' statement"
    assert not backend.inputs


def test_an_acknowledged_remote_frame_logs_its_timestamp_identifier_and_extended_bit(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """The kernel's byte-exact ack logs one DEBUG remote_event.sent carrying the frame whole."""
    with debug_session(caplog, MockBackend([ACK_REPLY])) as client:
        answered = client.send_remote(1000, _EXTENDED_ID, extended=True)
    assert answered == {"status": "ack"}
    assert logged(caplog, _EVENT) == [
        (
            logging.DEBUG,
            f"remote_event.sent ts=1000 canId={_EXTENDED_ID} extended=true response=ack",
        )
    ]


def test_a_refused_remote_frame_logs_its_timestamp_and_raises_the_kernel_error(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """A kernel error logs the frame's timestamp and code, then raises its message verbatim."""
    with (
        debug_session(caplog, MockBackend([REFUSAL_REPLY])) as client,
        pytest.raises(ProtocolError) as refused,
    ):
        client.send_remote(1000, 0x100)
    assert str(refused.value) == REFUSAL_MESSAGE
    assert refused.value.code == REFUSAL_CODE
    assert logged(caplog, _EVENT) == [
        (
            logging.DEBUG,
            f"remote_event.sent ts=1000 response=error code={REFUSAL_CODE}",
        )
    ]
