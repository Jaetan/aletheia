"""Mock-based unit tests for StreamingClient

High-quality tests focusing on:
- JSON protocol validation
- Command input validation
- Edge cases with valid mocking
- Real-world usage scenarios
"""

import json

import pytest

from aletheia.streaming_client import StreamingClient, ProtocolError


# ============================================================================
# JSON PROTOCOL
# ============================================================================

class TestJSONProtocol:
    """Test JSON protocol handling"""

    def test_send_command_formats_json(self, mock_popen_factory):
        """Commands are sent as JSON with newline"""
        with mock_popen_factory(['{"status": "success"}\n']) as mock_proc:
            with StreamingClient() as client:
                client.parse_dbc({"version": "1.0", "messages": []})

            # Verify JSON was written to stdin
            assert mock_proc.stdin.write.called
            written_data = mock_proc.stdin.write.call_args[0][0]
            # Should be valid JSON ending with newline
            assert written_data.endswith("\n")
            parsed = json.loads(written_data.strip())
            assert parsed["type"] == "command"
            assert parsed["command"] == "parseDBC"

    def test_invalid_json_response(self, mock_popen_factory):
        """Invalid JSON response raises ProtocolError"""
        with mock_popen_factory(['not valid json\n']):
            with pytest.raises(ProtocolError, match="Invalid JSON"):
                with StreamingClient() as client:
                    client.parse_dbc({"version": "1.0", "messages": []})

    def test_empty_response(self, mock_popen_factory):
        """Empty response handled gracefully"""
        with mock_popen_factory(['']):  # EOF
            with pytest.raises(ProtocolError):
                with StreamingClient() as client:
                    client.parse_dbc({"version": "1.0", "messages": []})


# ============================================================================
# INPUT VALIDATION
# ============================================================================

class TestInputValidation:
    """Test explicit input validation (only send_frame validates currently)"""

    def test_send_frame_validates_data_length(self, mock_popen_factory):
        """send_frame requires 8-byte data"""
        with mock_popen_factory([]):
            with pytest.raises(ValueError, match="8 bytes"):
                with StreamingClient() as client:
                    # Wrong data length - validation happens before any I/O
                    client.send_frame(0, 0x100, [0] * 4)  # Only 4 bytes


# ============================================================================
# EDGE CASES
# ============================================================================

class TestEdgeCases:
    """Test edge cases and boundary conditions"""

    def test_very_large_dbc(self, mock_popen_factory):
        """Handle very large DBC files"""
        # Create large DBC (1000 messages)
        large_dbc = {
            "version": "1.0",
            "messages": [
                {
                    "id": i,
                    "name": f"Message{i}",
                    "dlc": 8,
                    "sender": "ECU",
                    "signals": []
                }
                for i in range(1000)
            ]
        }

        with mock_popen_factory(['{"status": "success"}\n']):
            with StreamingClient() as client:
                response = client.parse_dbc(large_dbc)
                assert response["status"] == "success"

    def test_unicode_in_signal_names(self, mock_popen_factory):
        """Handle unicode in signal names"""
        dbc = {
            "version": "1.0",
            "messages": [
                {
                    "id": 0x100,
                    "name": "Test",
                    "dlc": 8,
                    "sender": "ECU",
                    "signals": [{
                        "name": "Tür_Öffnen",  # Unicode
                        "startBit": 0,
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1,
                        "offset": 0,
                        "minimum": 0,
                        "maximum": 255,
                        "unit": "",
                        "presence": "always"
                    }]
                }
            ]
        }

        with mock_popen_factory(['{"status": "success"}\n']):
            with StreamingClient() as client:
                response = client.parse_dbc(dbc)
                assert response["status"] == "success"

    def test_rapid_commands(self, mock_popen_factory):
        """Handle rapid successive commands"""
        # 100 responses for 100 commands
        responses = ['{"status": "success"}\n'] * 100

        with mock_popen_factory(responses):
            with StreamingClient() as client:
                # Send many commands rapidly
                for _ in range(100):
                    client.parse_dbc({"version": "1.0", "messages": []})

        # Should complete without errors
        assert True


# ============================================================================
# REAL-WORLD SCENARIOS
# ============================================================================

class TestRealWorldScenarios:
    """Test realistic usage patterns"""

    def test_complete_workflow_mock(self, mock_popen_factory):
        """Complete workflow with mocked responses"""
        responses = [
            '{"status": "success", "message": "DBC parsed"}\n',
            '{"status": "success", "message": "Properties set"}\n',
            '{"status": "success", "message": "Stream started"}\n',
            '{"status": "ack"}\n',  # send_frame
            '{"status": "ack"}\n',  # send_frame
            '{"status": "complete"}\n',  # end_stream
        ]

        with mock_popen_factory(responses):
            with StreamingClient() as client:
                # Full workflow
                client.parse_dbc({"version": "1.0", "messages": []})
                client.set_properties([])
                client.start_stream()
                client.send_frame(0, 0x100, [0] * 8)
                client.send_frame(1, 0x100, [1] * 8)
                client.end_stream()

        # Should complete without errors
        assert True

    def test_property_violation_detection_mock(self, mock_popen_factory):
        """Detect property violations in mocked response"""
        violation = json.dumps({
            "type": "property",
            "status": "violation",
            "reason": "Speed exceeded limit",
            "property_index": {"numerator": 0, "denominator": 1},
            "timestamp": {"numerator": 100, "denominator": 1}
        }) + '\n'

        with mock_popen_factory([violation]):
            with StreamingClient() as client:
                response = client.send_frame(100, 0x100, [0xFF] * 8)

                assert response["type"] == "property"
                assert response["status"] == "violation"
                assert "Speed" in response["reason"]
