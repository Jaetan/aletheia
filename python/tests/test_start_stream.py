# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What ``start_stream`` refuses outside a session.

A client not entered refuses to start a stream with the guard ``StateError``
and calls no backend. ``MockBackend`` stands in for the kernel.
"""

from __future__ import annotations

from _stream_helpers import refused_outside_a_session


def test_a_stream_outside_a_session_is_refused_with_the_guard_message() -> None:
    """A client not entered refuses with the guard StateError and calls no backend."""
    refused, backend = refused_outside_a_session(lambda client: client.start_stream())
    assert str(refused) == "Client not initialized \N{EM DASH} use 'with' statement"
    assert not backend.inputs
