# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What ``end_stream`` refuses outside a session and what its ``stream.ended`` record counts.

A client not entered refuses to end a stream with the guard ``StateError`` and
calls no backend. An entered client logs one INFO ``stream.ended`` event per
``complete`` reply, carrying the number of results, of ``fails`` results, of
``unresolved`` results and of warnings, after one WARNING
``endstream.uncached_atom`` event per warning. ``MockBackend`` serves the
canned reply.
"""

from __future__ import annotations

import json
import logging
from typing import TYPE_CHECKING

from _stream_helpers import refused_outside_a_session

from aletheia import AletheiaClient, MockBackend

if TYPE_CHECKING:
    import pytest

# Three holds, two fails and one unresolved: each count differs from the others
# and from the total, so a count read from the wrong status shows.
_RESULTS = [
    {"type": "property", "status": "holds", "property_index": 0},
    {
        "type": "property",
        "status": "fails",
        "property_index": 1,
        "timestamp": 1000,
        "reason": "violated",
    },
    {"type": "property", "status": "holds", "property_index": 2},
    {"type": "property", "status": "unresolved", "property_index": 3, "reason": "never observed"},
    {
        "type": "property",
        "status": "fails",
        "property_index": 4,
        "timestamp": 2000,
        "reason": "violated",
    },
    {"type": "property", "status": "holds", "property_index": 5},
]
_WARNINGS = [
    {"kind": "uncached_atom", "property_index": 3, "detail": "Speed"},
    {"kind": "uncached_atom", "property_index": 5, "detail": "Rpm"},
]
_COMPLETE_REPLY = json.dumps(
    {"status": "complete", "results": _RESULTS, "warnings": _WARNINGS}
).encode()


def test_an_end_outside_a_session_is_refused_with_the_guard_message() -> None:
    """A client not entered refuses with the guard StateError and calls no backend."""
    refused, backend = refused_outside_a_session(lambda client: client.end_stream())
    assert str(refused) == "Client not initialized \N{EM DASH} use 'with' statement"
    assert not backend.inputs


def test_a_complete_reply_logs_each_count_of_its_results_and_warnings(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """stream.ended counts the results, the fails, the unresolved and the warnings."""
    backend = MockBackend([_COMPLETE_REPLY])
    with (
        caplog.at_level(logging.INFO, logger="aletheia"),
        AletheiaClient(backend=backend) as client,
    ):
        client.end_stream()
    assert [
        (record.levelno, record.getMessage())
        for record in caplog.records
        if record.getMessage().startswith(("stream.ended", "endstream."))
    ] == [
        (logging.WARNING, "endstream.uncached_atom property_index=3 detail=Speed"),
        (logging.WARNING, "endstream.uncached_atom property_index=5 detail=Rpm"),
        (logging.INFO, "stream.ended numResults=6 numFails=2 numUnresolved=1 numWarnings=2"),
    ]
