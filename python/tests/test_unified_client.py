"""Tests for the unified AletheiaClient.

Tests that the unified client can:
1. Parse DBC and extract signals
2. Build frames from signal values
3. Update frames with new signal values
4. Stream frames with LTL property checking
5. Mix signal operations while streaming
"""

from pathlib import Path

import pytest

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json


@pytest.fixture
def demo_dbc() -> dict:
    """Load the demo vehicle DBC."""
    dbc_path = Path(__file__).parent.parent.parent / "examples" / "demo" / "vehicle.dbc"
    return dbc_to_json(str(dbc_path))


@pytest.fixture
def simple_dbc() -> dict:
    """Create a simple DBC for testing."""
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
                        "presence": "always"
                    }
                ]
            }
        ]
    }


class TestAletheiaClientBasics:
    """Basic functionality tests."""

    def test_parse_dbc(self, simple_dbc: dict) -> None:
        """Test DBC parsing."""
        with AletheiaClient() as client:
            response = client.parse_dbc(simple_dbc)
            assert response.get("status") == "success"

    def test_extract_signals(self, simple_dbc: dict) -> None:
        """Test signal extraction."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            result = client.extract_signals(can_id=256, data=[100, 0, 0, 0, 0, 0, 0, 0])
            assert result.get("TestSignal") == 100.0

    def test_build_frame(self, simple_dbc: dict) -> None:
        """Test frame building."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            frame = client.build_frame(can_id=256, signals={"TestSignal": 1000.0})
            assert len(frame) == 8
            # Verify by extracting
            result = client.extract_signals(can_id=256, data=frame)
            assert result.get("TestSignal") == 1000.0

    def test_update_frame(self, simple_dbc: dict) -> None:
        """Test frame updating."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            original = [50, 0, 0, 0, 0, 0, 0, 0]
            updated = client.update_frame(can_id=256, frame=original, signals={"TestSignal": 200.0})
            assert len(updated) == 8
            # Verify
            result = client.extract_signals(can_id=256, data=updated)
            assert result.get("TestSignal") == 200.0


class TestAletheiaClientStreaming:
    """Streaming LTL tests."""

    def test_streaming_no_violation(self, simple_dbc: dict) -> None:
        """Test streaming without violations."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Send frames that don't violate
            for i in range(10):
                response = client.send_frame(
                    timestamp=i * 1000,
                    can_id=256,
                    data=[i * 10, 0, 0, 0, 0, 0, 0, 0]  # Values 0-90
                )
                assert response.get("status") == "ack"

            response = client.end_stream()
            assert response.get("status") == "complete"

    def test_streaming_with_violation(self, simple_dbc: dict) -> None:
        """Test streaming with a violation."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(100).always().to_dict()
            ])
            client.start_stream()

            # Send frame that violates (value = 200 > 100)
            response = client.send_frame(
                timestamp=1000,
                can_id=256,
                data=[200, 0, 0, 0, 0, 0, 0, 0]
            )
            assert response.get("status") == "violation"

            client.end_stream()


class TestAletheiaClientMixedOperations:
    """Test mixing signal operations with streaming."""

    def test_extract_while_streaming(self, simple_dbc: dict) -> None:
        """Test that extract_signals works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Send a frame
            client.send_frame(timestamp=1000, can_id=256, data=[50, 0, 0, 0, 0, 0, 0, 0])

            # Extract signals while streaming (should work!)
            result = client.extract_signals(can_id=256, data=[100, 0, 0, 0, 0, 0, 0, 0])
            assert result.get("TestSignal") == 100.0

            # Continue streaming
            client.send_frame(timestamp=2000, can_id=256, data=[60, 0, 0, 0, 0, 0, 0, 0])

            client.end_stream()

    def test_update_while_streaming(self, simple_dbc: dict) -> None:
        """Test that update_frame works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Update a frame while streaming
            original = [50, 0, 0, 0, 0, 0, 0, 0]
            updated = client.update_frame(can_id=256, frame=original, signals={"TestSignal": 75.0})

            # Send the updated frame
            response = client.send_frame(timestamp=1000, can_id=256, data=updated)
            assert response.get("status") == "ack"

            client.end_stream()

    def test_build_while_streaming(self, simple_dbc: dict) -> None:
        """Test that build_frame works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Build a frame while streaming
            frame = client.build_frame(can_id=256, signals={"TestSignal": 500.0})

            # Send it
            response = client.send_frame(timestamp=1000, can_id=256, data=frame)
            assert response.get("status") == "ack"

            client.end_stream()


class TestAletheiaClientWithDemoDBC:
    """Tests using the demo vehicle DBC."""

    def test_vehicle_speed_extraction(self, demo_dbc: dict) -> None:
        """Test extracting vehicle speed from demo DBC."""
        with AletheiaClient() as client:
            client.parse_dbc(demo_dbc)

            # Build a frame with speed = 72 kph
            frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 72.0})

            # Extract and verify
            result = client.extract_signals(can_id=0x100, data=frame)
            assert abs(result.get("VehicleSpeed") - 72.0) < 0.01

    def test_fault_injection_single_session(self, demo_dbc: dict) -> None:
        """Test fault injection in a single streaming session."""
        with AletheiaClient() as client:
            client.parse_dbc(demo_dbc)
            client.set_properties([
                Signal("VehicleSpeed").less_than(120).always().to_dict()
            ])
            client.start_stream()

            # Send normal frames
            for i in range(5):
                frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 50.0 + i})
                response = client.send_frame(timestamp=i * 100000, can_id=0x100, data=frame)
                assert response.get("status") == "ack"

            # Inject fault: speed = 130 kph (exceeds 120 limit)
            fault_frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 130.0})
            response = client.send_frame(timestamp=500000, can_id=0x100, data=fault_frame)
            assert response.get("status") == "violation"

            client.end_stream()
