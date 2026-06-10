# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Mutation-killing tests for AletheiaClient lifecycle / guard paths.

The init/close/re-enter lifecycle and the not-initialized guards are only
partly exercised by the happy-path suite, leaving mutants on the initial state,
the close() cleanup logic, and the pre-__enter__ send-frame stub.  These tests
pin each branch via observable behaviour (is_closed, re-enter, a close-recording
backend, the directly-callable stub) rather than reaching into private state.
"""

from __future__ import annotations

import json
import logging
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, MockBackend, StateError

# The pre-__enter__ send-frame stub lives in the internal _client module; a
# direct call is the only way to exercise its defensive raise (send_frame's own
# _state guard shadows it on the public path).
from aletheia.client._client import send_frame_unbound
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from aletheia.types import JSONValue


class _RecordingBackend(MockBackend):
    """MockBackend that records the state handed to each close() call."""

    def __init__(self) -> None:
        super().__init__()
        self.close_calls: list[int] = []

    def close(self, state: int) -> None:
        self.close_calls.append(state)


def _resp(obj: dict[str, JSONValue]) -> bytes:
    """Encode a canned JSON response for the MockBackend queue."""
    return json.dumps(obj).encode()


def test_is_closed_true_before_enter() -> None:
    """A freshly-constructed client reports closed (initial _state is None)."""
    client = AletheiaClient(backend=MockBackend())
    assert client.is_closed is True


def test_reenter_injected_backend_succeeds() -> None:
    """Re-entering a client with an injected backend reuses it (backend retained)."""
    backend = MockBackend()
    client = AletheiaClient(backend=backend)
    with client:
        pass
    with client:  # injected backend is caller-owned → retained across close → no factory-missing
        pass
    assert client.is_closed is True


def test_close_passes_real_state_once_and_is_idempotent() -> None:
    """close() forwards the real state once, and a second close is a no-op."""
    backend = _RecordingBackend()
    client = AletheiaClient(backend=backend)
    with client:
        pass  # __exit__ → close #1, with the real (non-None) state
    assert len(backend.close_calls) == 1
    assert backend.close_calls[0] is not None  # kills close(None)
    client.close()  # close #2: idempotent — must NOT re-call backend.close
    assert len(backend.close_calls) == 1  # kills the `and`→`or` guard flip


def test_reenter_owned_backend_reconstructs() -> None:
    """Re-entering a client that owns its backend rebuilds it (real FFI)."""
    client = AletheiaClient()  # no injected backend → owned FFIBackend
    with client:
        pass
    with client:  # owned backend was cleared on close → factory rebuilds it
        pass
    assert client.is_closed is True


def test_send_frame_unbound_stub_raises_state_error() -> None:
    """The pre-__enter__ send-frame stub raises StateError with the guard message."""
    with pytest.raises(StateError) as excinfo:
        send_frame_unbound()
    assert str(excinfo.value) == "Client not initialized — use 'with' statement"


def test_parse_dbc_text_exactly_at_limit_allowed(monkeypatch: pytest.MonkeyPatch) -> None:
    """A DBC text exactly at MAX_DBC_TEXT_BYTES is allowed (bound is `>`, not `>=`)."""
    text = "x" * 100
    monkeypatch.setattr("aletheia.client._client.MAX_DBC_TEXT_BYTES", len(text.encode()))
    backend = MockBackend([_resp({"status": "error", "message": "bad", "code": "x"})])
    with AletheiaClient(backend=backend) as client:
        # At exactly the limit, `> limit` admits it → reaches the backend (the
        # canned error response); a `>= limit` mutant would reject it first.
        result = client.parse_dbc_text(text)
    assert result["status"] == "error"


def test_finalize_logs_parsed_message_count(caplog: pytest.LogCaptureFixture) -> None:
    """On a successful parse, the DBC_PARSED log carries the message count."""
    dbc_def = dbc([message(0x100, "M1", [signal("S1")]), message(0x200, "M2", [signal("S2")])])
    with AletheiaClient() as client, caplog.at_level(logging.INFO):
        result = client.parse_dbc(dbc_def)
    assert result["status"] == "success"
    # messages=len(dbc["messages"]); a `messages=None` mutant logs messages=None.
    assert "messages=2" in caplog.text


def test_build_frame_resolves_extended_message() -> None:
    """The signal lookup keys on the message's `extended` flag (read via msg.get).

    Parsing an extended (29-bit) message then building a frame on it with
    ``extended=True`` resolves only if ``msg.get("extended", False)`` was read
    correctly — a mutated key/default keys the lookup under ``extended=False``,
    so the (id, True) lookup misses and build_frame raises.
    """
    dbc_msg = message(0x100, "M", [signal("Sig")])
    dbc_msg["extended"] = True
    dbc_def = dbc([dbc_msg])
    with AletheiaClient() as client:
        client.parse_dbc(dbc_def)
        frame = client.build_frame(can_id=0x100, dlc=DLCCode(8), signals={"Sig": 1}, extended=True)
    assert len(frame) == 8
