# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared streaming-session helpers for test modules.

Several test modules drive a one-frame streaming session (``parse_dbc →
set_properties → start_stream → send_frame → end_stream``) or send a single
frame with the canonical lifecycle header, or run one entry on a client not
yet entered.  Centralising the boilerplate here keeps the wire details in one
place (pylint R0801) and out of ``conftest.py``, which is reserved for pytest
fixtures.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, TypedDict
from unittest.mock import Mock

import pytest

from aletheia import AletheiaClient, MockBackend, Signal, StateError
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.checks_runner import run_checks
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path
    from typing import Unpack

    from aletheia.checks import CheckResult
    from aletheia.checks_runner import CheckRunResult
    from aletheia.dsl import Property
    from aletheia.types import (
        AckResponse,
        CompleteResponse,
        DBCDefinition,
        ErrorResponse,
        PropertyBatchResponse,
        PropertyResultEntry,
    )


class _StreamOverrides(TypedDict, total=False):
    """Optional keyword overrides for :func:`run_one_frame_stream`."""

    property_: Property
    timestamp: int
    can_id: int
    dlc: int


def run_one_frame_stream(
    dbc: DBCDefinition,
    payload: bytes | bytearray,
    **overrides: Unpack[_StreamOverrides],
) -> None:
    """Drive a complete one-frame streaming session.

    The sequence is ``parse_dbc → set_properties → start_stream → send_frame →
    end_stream``.  Kept terse on purpose — logging tests want minimal noise in
    the capture buffer.  Recognized overrides: ``timestamp`` (default 1000),
    ``can_id`` (default 256), ``dlc`` (default 8), and ``property_`` (default
    ``Signal("TestSignal").less_than(1000).always()`` — matches the
    ``simple_dbc`` fixture).
    """
    prop = overrides.get("property_")
    chosen: Property = prop if prop is not None else Signal("TestSignal").less_than(1000).always()
    timestamp = overrides.get("timestamp", 1000)
    can_id = overrides.get("can_id", 256)
    dlc = DLCCode(overrides.get("dlc", 8))
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties([chosen.to_dict()])
        client.start_stream()
        client.send_frame(timestamp=timestamp, can_id=can_id, dlc=dlc, data=bytearray(payload))
        client.end_stream()


def refused_outside_a_session[R](
    call: Callable[[AletheiaClient], R],
) -> tuple[StateError, MockBackend]:
    """Run *call* on a client not yet entered; return the ``StateError`` raised and the backend.

    The backend is a ``MockBackend`` queuing no reply, whose ``inputs`` show
    whether the refused call reached it.
    """
    backend = MockBackend()
    with pytest.raises(StateError) as refused:
        _ = call(AletheiaClient(backend=backend))
    return refused.value, backend


def send_test_frame(
    client: AletheiaClient,
    payload: bytes | bytearray | list[int],
) -> AckResponse | PropertyBatchResponse | ErrorResponse:
    """Send one frame on an already-streaming client with the canonical header.

    Wraps ``send_frame`` with the lifecycle-test defaults (``timestamp=1000``,
    ``can_id=256``, ``dlc=8``) so the call sites that only vary the payload do
    not each repeat the frame literal (pylint R0801).
    """
    return client.send_frame(timestamp=1000, can_id=256, dlc=DLCCode(8), data=bytearray(payload))


_SUCCESS_REPLY = json.dumps({"status": "success"}).encode("utf-8")
_EMPTY_DBC: DBCDefinition = {"version": "", "messages": [], **empty_dbc_tier2()}


def run_checks_over_one_frame(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    checks: list[CheckResult],
    frame: PropertyResultEntry,
    complete: CompleteResponse,
) -> CheckRunResult:
    """Run *checks* over a one-frame log, the frame answered *frame* and the end *complete*.

    The client answers ``set_properties`` and ``start_stream`` from a
    ``MockBackend``, and the frame and the stream end with the dicts given, so
    no kernel answers the stream.
    """
    log = tmp_path / "frames.log"
    log.write_text("(0.000000) can0 100#00\n", encoding="utf-8")
    batch: PropertyBatchResponse = {"type": "property_batch", "results": [frame]}
    with AletheiaClient(backend=MockBackend([_SUCCESS_REPLY, _SUCCESS_REPLY])) as client:
        monkeypatch.setattr(client, "send_frame", Mock(return_value=batch))
        monkeypatch.setattr(client, "end_stream", Mock(return_value=complete))
        return run_checks(_EMPTY_DBC, checks, str(log), client=client)
