# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared test fixtures for all test modules."""

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _canonical_dbc import CANONICAL_DBC, make_dbc

from aletheia import FFIBackend, Signal

if TYPE_CHECKING:
    from aletheia.dsl import Property
    from aletheia.types import DBCDefinition

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


@pytest.fixture(scope="module")
def rts_up() -> FFIBackend:
    """Bring the GHC RTS up for renderer-dependent tests, lazily.

    Since point 2 the rational renderer no longer self-initialises the RTS — an
    ``FFIBackend`` is the sole initialiser — so ``format_formula`` /
    ``build_diagnostic`` (which render rational thresholds) need a live RTS.
    Request it module-wide with ``pytestmark = pytest.mark.usefixtures("rts_up")``
    rather than at import: the RTS comes up when the module's tests run, not during
    collection. ``RTSState.acquire`` is idempotent (refcounted), so this composes
    with any client a test creates; the RTS is one-shot per process, so there is no
    teardown (GHC cannot re-init after ``hs_exit``).
    """
    return FFIBackend()


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
