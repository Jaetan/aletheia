"""Integration tests for Phase 2B JSON streaming client"""

from typing import cast

import pytest

from aletheia.protocols import AlwaysFormula, DBCDefinition, ErrorResponse
from aletheia.streaming_client import StreamingClient


# Sample minimal DBC for testing (JSON format for streaming protocol)
MINIMAL_DBC: DBCDefinition = {
    "version": "1.0",
    "messages": [
        {
            "id": 0x100,
            "name": "VehicleSpeed",
            "dlc": 8,
            "sender": "ECU",
            "signals": [
                {
                    "name": "Speed",
                    "startBit": 0,
                    "length": 16,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 0.01,
                    "offset": 0,
                    "minimum": 0,
                    "maximum": 655.35,
                    "unit": "kph",
                    "presence": "always"
                }
            ]
        }
    ]
}


def test_parse_dbc() -> None:
    """Test parsing DBC file"""
    with StreamingClient() as client:
        response = client.parse_dbc(MINIMAL_DBC)
        assert response["status"] == "success"
        assert "DBC parsed" in response.get("message", "")


def test_full_streaming_workflow() -> None:
    """Test complete streaming workflow: ParseDBC → SetProperties → StartStream → DataFrame → EndStream"""

    # Simple LTL property: Speed signal must always be less than 200
    property_json: AlwaysFormula = {
        "operator": "always",
        "formula": {
            "operator": "atomic",
            "predicate": {
                "predicate": "lessThan",
                "signal": "Speed",
                "value": 200.0
            }
        }
    }

    with StreamingClient() as client:
        # Step 1: Parse DBC
        response = client.parse_dbc(MINIMAL_DBC)
        assert response["status"] == "success"

        # Step 2: Set properties
        response = client.set_properties([property_json])
        assert response["status"] == "success"

        # Step 3: Start streaming
        response = client.start_stream()
        assert response["status"] == "success"

        # Step 4: Send frames that satisfy the property (Speed = 100.0)
        # Speed signal is 16-bit little-endian at bit 0
        # Value 10000 * 0.01 = 100.0
        frame_data = [0x10, 0x27, 0, 0, 0, 0, 0, 0]  # 0x2710 = 10000

        for i in range(5):
            response = client.send_frame(
                timestamp=i * 1000,  # microseconds
                can_id=0x100,  # 256 decimal
                data=frame_data
            )
            assert response["status"] == "ack", f"Frame {i} should be acknowledged"

        # Step 5: End streaming
        response = client.end_stream()
        assert response["status"] == "complete"


def test_property_violation() -> None:
    """Test that property violations are detected"""

    # Property: Speed must always be less than 100
    property_json: AlwaysFormula = {
        "operator": "always",
        "formula": {
            "operator": "atomic",
            "predicate": {
                "predicate": "lessThan",
                "signal": "Speed",
                "value": 100.0
            }
        }
    }

    with StreamingClient() as client:
        client.parse_dbc(MINIMAL_DBC)
        client.set_properties([property_json])
        client.start_stream()

        # Send frame with Speed = 150.0 (violates property)
        # Value 15000 * 0.01 = 150.0
        violation_frame = [0x98, 0x3A, 0, 0, 0, 0, 0, 0]  # 0x3A98 = 15000

        response = client.send_frame(
            timestamp=1000,
            can_id=0x100,  # 256 decimal
            data=violation_frame
        )

        # Should receive a property violation response
        assert response.get("type") == "property"
        assert response.get("status") == "violation"

        # property_index may be returned as integer or rational number format
        prop_idx = response.get("property_index")
        if isinstance(prop_idx, dict) and "numerator" in prop_idx:
            assert prop_idx["numerator"] == 0  # Rational format
        else:
            assert prop_idx == 0  # Plain integer format


def test_state_machine_error_dataframe_before_start() -> None:
    """Test that sending DataFrame before StartStream returns error"""
    with StreamingClient() as client:
        client.parse_dbc(MINIMAL_DBC)
        client.set_properties([])

        # Try to send frame without calling start_stream()
        raw_response = client.send_frame(
            timestamp=1000,
            can_id=0x100,  # 256 decimal
            data=[0, 0, 0, 0, 0, 0, 0, 0]
        )
        # Cast to ErrorResponse since we expect an error here
        response = cast(ErrorResponse, raw_response)

        assert response["status"] == "error"
        assert "StartStream" in response["message"]


def test_invalid_frame_data() -> None:
    """Test that invalid frame data (not 8 bytes) raises ValueError"""
    with StreamingClient() as client:
        with pytest.raises(ValueError, match="exactly 8 bytes"):
            client.send_frame(
                timestamp=1000,
                can_id=100,
                data=[1, 2, 3]  # Only 3 bytes
            )


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v"])
