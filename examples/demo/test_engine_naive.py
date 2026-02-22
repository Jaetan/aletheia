"""Naive Engine ECU Tests — ALL PASS Against the Buggy ECU

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

import pytest

from aletheia import AletheiaClient

from engine_ecu_sim import (
    ENGINE_DBC,
    ENGINE_STATUS_ID,
    generate_frozen_trace,
    generate_normal_trace,
)


@pytest.fixture
def frozen_trace():
    """The buggy trace — ECU freezes at frame 15."""
    return generate_frozen_trace(n_frames=50, freeze_at=15)


@pytest.fixture
def normal_trace():
    """A healthy trace for comparison."""
    return generate_normal_trace(n_frames=50)


# =============================================================================
# NAIVE TESTS — All pass against both normal AND frozen traces
# =============================================================================


class TestNaiveChecks:
    """Value-range checks that cannot detect staleness."""

    def test_rpm_in_valid_range(self, frozen_trace) -> None:
        """RPM should be between 0 and 16383.75 rpm."""
        with AletheiaClient() as client:
            client.parse_dbc(ENGINE_DBC)
            for frame in frozen_trace:
                result = client.extract_signals(
                    can_id=frame.can_id, data=frame.data
                )
                rpm = result.get("EngineRPM")
                assert 0 <= rpm <= 16383.75, f"RPM out of range: {rpm}"

    def test_coolant_in_valid_range(self, frozen_trace) -> None:
        """Coolant temperature should be between -40 and 215 degC."""
        with AletheiaClient() as client:
            client.parse_dbc(ENGINE_DBC)
            for frame in frozen_trace:
                result = client.extract_signals(
                    can_id=frame.can_id, data=frame.data
                )
                temp = result.get("CoolantTemp")
                assert -40 <= temp <= 215, f"CoolantTemp out of range: {temp}"

    def test_counter_in_valid_range(self, frozen_trace) -> None:
        """FrameCounter should be between 0 and 15.

        This PASSES even though the counter is frozen at 7 — because 7
        is a perfectly valid value! Range checks can't detect staleness.
        """
        with AletheiaClient() as client:
            client.parse_dbc(ENGINE_DBC)
            for frame in frozen_trace:
                result = client.extract_signals(
                    can_id=frame.can_id, data=frame.data
                )
                counter = result.get("FrameCounter")
                assert 0 <= counter <= 15, f"FrameCounter out of range: {counter}"

    def test_messages_are_arriving(self, frozen_trace) -> None:
        """Verify that we receive the expected number of frames.

        PASSES: The frozen ECU still sends frames — its CAN TX hardware
        keeps retransmitting the last buffer. The problem isn't missing
        frames, it's that the content is stale.
        """
        assert len(frozen_trace) == 50

    def test_rpm_is_nonzero(self, frozen_trace) -> None:
        """Engine RPM should be above idle after warmup.

        PASSES: The frozen ECU replays its last RPM value, which was a
        perfectly reasonable number.
        """
        with AletheiaClient() as client:
            client.parse_dbc(ENGINE_DBC)
            # Skip first few frames (cold start)
            for frame in frozen_trace[5:]:
                result = client.extract_signals(
                    can_id=frame.can_id, data=frame.data
                )
                rpm = result.get("EngineRPM")
                assert rpm > 0, f"Engine not running: RPM={rpm}"

    def test_coolant_is_warming(self, frozen_trace) -> None:
        """Coolant should be above ambient after warmup.

        PASSES: The frozen value is the last computed temperature,
        which was already warm.
        """
        with AletheiaClient() as client:
            client.parse_dbc(ENGINE_DBC)
            for frame in frozen_trace[10:]:
                result = client.extract_signals(
                    can_id=frame.can_id, data=frame.data
                )
                temp = result.get("CoolantTemp")
                assert temp > 0, f"Coolant too cold: {temp}"

    def test_all_signals_extracted(self, frozen_trace) -> None:
        """All three signals should extract without errors."""
        with AletheiaClient() as client:
            client.parse_dbc(ENGINE_DBC)
            for frame in frozen_trace:
                result = client.extract_signals(
                    can_id=frame.can_id, data=frame.data
                )
                assert not result.has_errors()
                assert "EngineRPM" in result.values
                assert "CoolantTemp" in result.values
                assert "FrameCounter" in result.values

    def test_frame_data_is_8_bytes(self, frozen_trace) -> None:
        """Every frame should have exactly 8 data bytes."""
        for frame in frozen_trace:
            assert len(frame.data) == 8


# =============================================================================
# SUMMARY
# =============================================================================
#
# All 8 tests pass against the frozen ECU trace. The naive approach of
# checking value ranges on individual frames cannot detect temporal
# properties like "the alive counter must keep changing."
#
# See demo_ltl_bug.py for how Aletheia catches this with:
#   Signal("FrameCounter").changed_by(0).never()
#
# This LTL property means: "It is never the case that FrameCounter
# changes by 0 or less" — i.e., the counter must always increment.
# =============================================================================
