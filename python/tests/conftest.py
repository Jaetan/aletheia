"""Shared test fixtures for all test modules"""

from dataclasses import dataclass

import pytest

from aletheia import AletheiaClient, Signal
from aletheia.dsl import Property
from aletheia.protocols import DBCDefinition


def run_one_frame_stream(
    dbc: DBCDefinition,
    payload: bytes | bytearray,
    **overrides: object,
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
    chosen: Property = prop if isinstance(prop, Property) else (
        Signal("TestSignal").less_than(1000).always()
    )
    timestamp = int(overrides.get("timestamp", 1000))  # type: ignore[arg-type]
    can_id = int(overrides.get("can_id", 256))  # type: ignore[arg-type]
    dlc = int(overrides.get("dlc", 8))  # type: ignore[arg-type]
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties([chosen.to_dict()])
        client.start_stream()
        client.send_frame(
            timestamp=timestamp, can_id=can_id, dlc=dlc,
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


@pytest.fixture(name="sample_dbc")
def _sample_dbc() -> DBCDefinition:
    """Sample DBC JSON structure for testing"""
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x100,
                "name": "TestMessage",
                "dlc": 8,
                "sender": "TestECU",
                "signals": [
                    {
                        "name": "TestSignal",
                        "startBit": 0,
                        "length": 16,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1.0,
                        "offset": 0.0,
                        "minimum": 0.0,
                        "maximum": 65535.0,
                        "unit": "",
                        "presence": "always"
                    }
                ]
            }
        ]
    }


@pytest.fixture
def simple_dbc() -> DBCDefinition:
    """Minimal DBC with one 16-bit unsigned signal at message ID 256.

    Distinct from ``sample_dbc`` (ID 0x100, sender "TestECU"); ``simple_dbc``
    lives at the canonical ID 256 used by the streaming/lifecycle tests.
    Kept as a separate fixture so tests can advertise which shape they need.
    """
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 256,
                "name": "TestMessage",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "TestSignal",
                        "startBit": 0,
                        "length": 16,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1.0,
                        "offset": 0.0,
                        "minimum": 0.0,
                        "maximum": 65535.0,
                        "unit": "",
                        "presence": "always",
                    }
                ],
            }
        ],
    }


@pytest.fixture(name="sample_property")
def _sample_property() -> Property:
    """Sample LTL property for testing"""
    return Signal("Speed").less_than(220).always()


@pytest.fixture(name="sample_can_frame")
def _sample_can_frame() -> CANFrame:
    """Sample CAN frame data for testing"""
    return CANFrame(
        timestamp=1000,
        can_id=0x100,
        dlc=8,
        data=bytearray([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07])
    )
