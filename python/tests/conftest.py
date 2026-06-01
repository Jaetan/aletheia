"""Shared test fixtures for all test modules."""

import sys
from dataclasses import dataclass
from pathlib import Path

import pytest
from _canonical_dbc import CANONICAL_DBC, make_dbc

from aletheia import Signal
from aletheia.dsl import Property
from aletheia.protocols import DBCDefinition

# Make the repo root importable so tests can reach the ``tools`` package (the dev
# tooling lives at ``<repo>/tools``, a sibling of ``python/``, not under it).
_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))


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
