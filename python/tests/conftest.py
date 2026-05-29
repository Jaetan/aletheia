"""Shared test fixtures for all test modules."""

from dataclasses import dataclass
from typing import TypedDict, Unpack

import pytest
from _canonical_dbc import CANONICAL_DBC, make_dbc
from aletheia import AletheiaClient, Signal
from aletheia.dsl import Property
from aletheia.protocols import DBCDefinition, DLCCode


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

    The sequence is: ``parse_dbc → set_properties → start_stream →
    send_frame → end_stream``. Kept terse on purpose — logging tests
    want minimal noise in the capture buffer. Recognized overrides:
    ``timestamp`` (default 1000), ``can_id`` (default 256),
    ``dlc`` (default 8), and ``property_`` (default
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
        client.send_frame(
            timestamp=timestamp,
            can_id=can_id,
            dlc=dlc,
            data=bytearray(payload),
        )
        client.end_stream()


@dataclass(frozen=True)
class CANFrame:
    """CAN frame test data with named fields for clarity."""

    timestamp: int
    can_id: int
    dlc: int
    data: bytearray


@pytest.fixture
def sample_dbc() -> DBCDefinition:
    """Sample DBC JSON structure for testing."""
    return make_dbc(msg_id=0x100, sender="TestECU")


@pytest.fixture
def simple_dbc() -> DBCDefinition:
    """Minimal DBC with one 16-bit unsigned signal at message ID 256.

    Distinct from ``sample_dbc`` (ID 0x100, sender "TestECU"); ``simple_dbc``
    lives at the canonical ID 256 used by the streaming/lifecycle tests.
    The body lives in ``_canonical_dbc.CANONICAL_DBC`` so the cross-binding
    integration tests can share the exact wire content.
    """
    return CANONICAL_DBC


@pytest.fixture
def sample_property() -> Property:
    """Sample LTL property for testing."""
    return Signal("Speed").less_than(220).always()


@pytest.fixture
def sample_can_frame() -> CANFrame:
    """Sample CAN frame data for testing."""
    return CANFrame(
        timestamp=1000,
        can_id=0x100,
        dlc=8,
        data=bytearray([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]),
    )
