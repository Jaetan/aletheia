# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared test fixtures for all test modules."""

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _canonical_dbc import CANONICAL_DBC, make_dbc
from _hypothesis_profiles import register_profiles

from aletheia import RTSState, Signal, start_runtime

if TYPE_CHECKING:
    from aletheia.dsl import Property
    from aletheia.types import DBCDefinition

# Make the repo root importable so tests can reach the ``tools`` package (the dev
# tooling lives at ``<repo>/tools``, a sibling of ``python/``, not under it).  The
# root is the nearest directory above holding it, since the mutation lane runs
# this suite from mutmut's copy under ``python/mutants/``.
_REPO_ROOT = next(
    parent
    for parent in Path(__file__).resolve().parents
    if (parent / "tools" / "_common.py").is_file()
)
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

# Every test runs under the determinism guard: a clock that stands still unless
# the test advances it, and no thread, sleep or timed wait.  ``pytester`` runs
# the guard's own tests as sessions inside the suite's process.
pytest_plugins = ["tools._determinism_guard", "pytester"]

# The property tests' hypothesis profiles exist before pytest configures, which
# is when ``--hypothesis-profile`` loads the one it names.
register_profiles()


@dataclass(frozen=True)
class CANFrame:
    """CAN frame test data with named fields for clarity."""

    timestamp: int
    can_id: int
    dlc: int
    data: bytearray


@pytest.fixture(scope="module")
def rts_up() -> None:
    """Start the GHC runtime for tests that render thresholds or read decimals, lazily.

    The renderer and the decimal parser never start the runtime, so
    ``format_formula`` / ``build_diagnostic`` and ``from_decimal`` need it up.
    Request it module-wide with ``pytestmark = pytest.mark.usefixtures("rts_up")``
    rather than at import: the runtime starts when the module's tests run, not
    during collection.  A start of a runtime already up on the default count
    changes nothing and takes no reference, so this composes with any client a
    test opens.
    """
    start_runtime(1)


@pytest.fixture
def unstarted(monkeypatch: pytest.MonkeyPatch) -> None:
    """Give the test a runtime latch nothing has set, restored after it."""
    monkeypatch.setattr(RTSState, "lib", None)
    monkeypatch.setattr(RTSState, "initialized", False)
    monkeypatch.setattr(RTSState, "refcount", 0)
    monkeypatch.setattr(RTSState, "cores", 0)


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
