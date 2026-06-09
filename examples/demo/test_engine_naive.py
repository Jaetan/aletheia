# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Naive Engine ECU Tests — ALL PASS Against the Buggy ECU.

These tests represent the kind of checks that automotive test engineers
typically write: value-range assertions on individual frames. They verify
that each signal is within its valid range and that messages are arriving.

The problem: every single test passes against the frozen ECU trace,
even though the ECU has a critical firmware bug (stuck alive counter).

Run:
    python -m pytest examples/demo/test_engine_naive.py -v

Compare with demo_ltl_bug.py which uses Aletheia's LTL engine to
catch the staleness bug that these tests miss.
"""

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from engine_ecu_sim import ENGINE_DBC, generate_frozen_trace

from aletheia import AletheiaClient
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from engine_ecu_sim import CANFrame

    from aletheia import SignalExtractionResult

_RPM_MAX = 16383.75
_TEMP_MIN = -40
_TEMP_MAX = 215
_COUNTER_MAX = 15
_TRACE_FRAMES = 50
_FRAME_BYTES = 8
_COLD_START_SKIP = 5  # frames to skip for the "engine running" check
_WARMUP_SKIP = 10  # frames to skip for the "coolant warm" check


def _results(trace: list[CANFrame]) -> list[SignalExtractionResult]:
    """Extract every frame's signals through one client (dlc derived per frame)."""
    with AletheiaClient() as client:
        client.parse_dbc(ENGINE_DBC)
        return [
            client.extract_signals(
                can_id=frame.can_id, dlc=DLCCode(len(frame.data)), data=frame.data
            )
            for frame in trace
        ]


@pytest.fixture(name="frozen_trace")
def frozen_trace_fixture() -> list[CANFrame]:
    """Return the buggy trace — ECU freezes at frame 15."""
    return generate_frozen_trace(n_frames=_TRACE_FRAMES, freeze_at=_COUNTER_MAX)


# =============================================================================
# NAIVE TESTS — All pass against both normal AND frozen traces
# =============================================================================


class TestNaiveChecks:
    """Value-range checks that cannot detect staleness."""

    def test_rpm_in_valid_range(self, frozen_trace: list[CANFrame]) -> None:
        """RPM should be between 0 and 16383.75 rpm."""
        for result in _results(frozen_trace):
            rpm = result.get("EngineRPM")
            assert 0 <= rpm <= _RPM_MAX, f"RPM out of range: {rpm}"

    def test_coolant_in_valid_range(self, frozen_trace: list[CANFrame]) -> None:
        """Coolant temperature should be between -40 and 215 degC."""
        for result in _results(frozen_trace):
            temp = result.get("CoolantTemp")
            assert _TEMP_MIN <= temp <= _TEMP_MAX, f"CoolantTemp out of range: {temp}"

    def test_counter_in_valid_range(self, frozen_trace: list[CANFrame]) -> None:
        """FrameCounter should be between 0 and 15.

        This PASSES even though the counter is frozen — because a frozen value
        is still a perfectly valid one! Range checks can't detect staleness.
        """
        for result in _results(frozen_trace):
            counter = result.get("FrameCounter")
            assert 0 <= counter <= _COUNTER_MAX, f"FrameCounter out of range: {counter}"

    def test_messages_are_arriving(self, frozen_trace: list[CANFrame]) -> None:
        """Verify that we receive the expected number of frames.

        PASSES: The frozen ECU still sends frames — its CAN TX hardware
        keeps retransmitting the last buffer. The problem isn't missing
        frames, it's that the content is stale.
        """
        assert len(frozen_trace) == _TRACE_FRAMES

    def test_rpm_is_nonzero(self, frozen_trace: list[CANFrame]) -> None:
        """Engine RPM should be above idle after warmup.

        PASSES: The frozen ECU replays its last RPM value, which was a
        perfectly reasonable number.
        """
        for result in _results(frozen_trace[_COLD_START_SKIP:]):
            rpm = result.get("EngineRPM")
            assert rpm > 0, f"Engine not running: RPM={rpm}"

    def test_coolant_is_warming(self, frozen_trace: list[CANFrame]) -> None:
        """Coolant should be above ambient after warmup.

        PASSES: The frozen value is the last computed temperature,
        which was already warm.
        """
        for result in _results(frozen_trace[_WARMUP_SKIP:]):
            temp = result.get("CoolantTemp")
            assert temp > 0, f"Coolant too cold: {temp}"

    def test_all_signals_extracted(self, frozen_trace: list[CANFrame]) -> None:
        """All three signals should extract without errors."""
        for result in _results(frozen_trace):
            assert not result.has_errors()
            assert "EngineRPM" in result.values
            assert "CoolantTemp" in result.values
            assert "FrameCounter" in result.values

    def test_frame_data_is_8_bytes(self, frozen_trace: list[CANFrame]) -> None:
        """Every frame should have exactly 8 data bytes."""
        for frame in frozen_trace:
            assert len(frame.data) == _FRAME_BYTES


# =============================================================================
# SUMMARY
# =============================================================================
#
# All 8 tests pass against the frozen ECU trace. The naive approach of
# checking value ranges on individual frames cannot detect temporal
# properties like "the alive counter must keep changing."
#
# demo_ltl_bug.py catches this with an LTL alive-counter property: the
# FrameCounter must change (by at least one in either direction) on every
# frame, so a stuck (unchanged) counter is a violation.
# =============================================================================
