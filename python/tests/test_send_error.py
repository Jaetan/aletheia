# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What ``send_error`` refuses outside a session and what it logs of an error event.

A client not entered refuses an error event with the guard ``StateError`` and
calls no backend. An entered client logs the DEBUG ``error_event.sent`` event
of each error event the kernel answers: the byte-exact ack logs the event's
timestamp, and a kernel error logs the event's timestamp and the error's code
before it is raised. ``MockBackend`` serves the canned replies.
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

_EVENT = EventName("error_event.sent")


def test_an_error_event_outside_a_session_is_refused_with_the_guard_message() -> None:
    """A client not entered refuses with the guard StateError and calls no backend."""
    refused, backend = refused_outside_a_session(lambda client: client.send_error(0))
    assert str(refused) == "Client not initialized \N{EM DASH} use 'with' statement"
    assert not backend.inputs


def test_an_acknowledged_error_event_logs_its_timestamp(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """The kernel's byte-exact ack logs one DEBUG error_event.sent carrying the timestamp."""
    with debug_session(caplog, MockBackend([ACK_REPLY])) as client:
        answered = client.send_error(1000)
    assert answered == {"status": "ack"}
    assert logged(caplog, _EVENT) == [(logging.DEBUG, "error_event.sent ts=1000 response=ack")]


def test_a_refused_error_event_logs_its_timestamp_and_raises_the_kernel_error(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """A kernel error logs the event's timestamp and code, then raises its message verbatim."""
    with (
        debug_session(caplog, MockBackend([REFUSAL_REPLY])) as client,
        pytest.raises(ProtocolError) as refused,
    ):
        client.send_error(1000)
    assert str(refused.value) == REFUSAL_MESSAGE
    assert refused.value.code == REFUSAL_CODE
    assert logged(caplog, _EVENT) == [
        (logging.DEBUG, f"error_event.sent ts=1000 response=error code={REFUSAL_CODE}")
    ]
