"""Shared test fixtures for all test modules"""

from dataclasses import dataclass
from pathlib import Path

import pytest

from aletheia import Signal
from aletheia.dsl import Property
from aletheia.protocols import DBCDefinition


@dataclass(frozen=True)
class CANFrame:
    """CAN frame test data with named fields for clarity."""
    timestamp: int
    can_id: int
    data: bytearray


__all__ = [
    "CANFrame",
    "_sample_dbc",
    "_sample_property",
    "_sample_can_frame",
]


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
        data=bytearray([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07])
    )
