# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared streaming-session helpers for test modules.

Several test modules drive a one-frame streaming session (``parse_dbc →
set_properties → start_stream → send_frame → end_stream``) or send a single
frame with the canonical lifecycle header.  Centralising the boilerplate here
keeps the wire details in one place (pylint R0801) and out of ``conftest.py``,
which is reserved for pytest fixtures.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, TypedDict

from aletheia import AletheiaClient, Signal
from aletheia.protocols import DLCCode

if TYPE_CHECKING:
    from typing import Unpack

    from aletheia.dsl import Property
    from aletheia.protocols import (
        AckResponse,
        DBCDefinition,
        ErrorResponse,
        PropertyBatchResponse,
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
