# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The canned replies, the DEBUG session and the logged events of the event-send tests.

``send_error`` and ``send_remote`` log alike what the kernel answers, so their
tests enter one client over a ``MockBackend`` serving the reply under test, with
the ``aletheia`` logger captured at DEBUG, and read back the level and message
of each record of the event the send logs.
"""

from __future__ import annotations

import json
import logging
from contextlib import contextmanager
from typing import TYPE_CHECKING, Final, NamedTuple, NewType

from aletheia import AletheiaClient
from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Generator

    import pytest

    from aletheia import MockBackend

ACK_REPLY: Final = b'{"status":"ack"}'
REFUSAL_CODE: Final = "handler_non_monotonic_timestamp"
REFUSAL_MESSAGE: Final = "Timestamp went backwards"
REFUSAL_REPLY: Final = json.dumps(
    {"status": "error", "code": REFUSAL_CODE, "message": REFUSAL_MESSAGE}
).encode()

# A record's level, as ``logging`` numbers it.
LogLevel = NewType("LogLevel", int)
# A log event's name, as docs/LOG_EVENTS.yaml writes it and its records open.
EventName = NewType("EventName", str)


class Logged(NamedTuple):
    """The level and message of one captured record."""

    level: LogLevel
    message: Prose


@contextmanager
def debug_session(
    caplog: pytest.LogCaptureFixture, backend: MockBackend
) -> Generator[AletheiaClient]:
    """Yield a client entered over ``backend``, the ``aletheia`` logger captured at DEBUG."""
    with (
        caplog.at_level(logging.DEBUG, logger="aletheia"),
        AletheiaClient(backend=backend) as client,
    ):
        yield client


def logged(caplog: pytest.LogCaptureFixture, event: EventName) -> list[Logged]:
    """Return the level and message of each captured record of ``event``, in order."""
    return [
        Logged(LogLevel(record.levelno), Prose(record.getMessage()))
        for record in caplog.records
        if record.getMessage().startswith(event)
    ]
