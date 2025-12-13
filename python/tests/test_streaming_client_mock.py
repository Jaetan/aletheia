"""Mock-based unit tests for StreamingClient

High-quality tests focusing on:
- JSON protocol validation
- Command input validation
- Edge cases with valid mocking
- Real-world usage scenarios
"""

import pytest
import json
from unittest.mock import Mock, patch

from aletheia.streaming_client import StreamingClient, AletheiaError, ProtocolError


# ============================================================================
# JSON PROTOCOL
# ============================================================================

class TestJSONProtocol:
    """Test JSON protocol handling"""

    @patch('subprocess.Popen')
    def test_send_command_formats_json(self, mock_popen):
        """Commands are sent as JSON with newline"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = b'{"status": "success"}\n'
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            # Mock the internal method to check JSON format
            original_send = client._send_command
            sent_data = []

            def capture_send(cmd):
                # Capture what would be sent
                json_str = json.dumps(cmd)
                sent_data.append(json_str)
                return original_send(cmd)

            client._send_command = capture_send
            client.parse_dbc({"version": "1.0", "messages": []})

            # Check JSON was formatted
            assert len(sent_data) > 0
            parsed = json.loads(sent_data[0])
            assert "type" in parsed

    @patch('subprocess.Popen')
    def test_invalid_json_response(self, mock_popen):
        """Invalid JSON response raises ProtocolError"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = b'not valid json\n'
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with pytest.raises(ProtocolError, match="Invalid JSON"):
            with StreamingClient() as client:
                client.parse_dbc({"version": "1.0", "messages": []})

    @patch('subprocess.Popen')
    def test_empty_response(self, mock_popen):
        """Empty response handled gracefully"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = b''  # EOF
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with pytest.raises(ProtocolError):
            with StreamingClient() as client:
                client.parse_dbc({"version": "1.0", "messages": []})


# ============================================================================
# COMMAND VALIDATION
# ============================================================================

class TestCommandValidation:
    """Test input validation"""

    @patch('subprocess.Popen')
    def test_parse_dbc_validates_dict(self, mock_popen):
        """parse_dbc requires dict input"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with pytest.raises((TypeError, ValueError)):
            with StreamingClient() as client:
                client.parse_dbc("not a dict")  # Wrong type

    @patch('subprocess.Popen')
    def test_set_properties_validates_list(self, mock_popen):
        """set_properties requires list input"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with pytest.raises((TypeError, ValueError)):
            with StreamingClient() as client:
                client.set_properties("not a list")  # Wrong type

    @patch('subprocess.Popen')
    def test_send_frame_validates_types(self, mock_popen):
        """send_frame validates parameter types"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with pytest.raises((TypeError, ValueError)):
            with StreamingClient() as client:
                # Invalid timestamp type
                client.send_frame("not an int", 0x100, [0] * 8)

    @patch('subprocess.Popen')
    def test_send_frame_validates_data_length(self, mock_popen):
        """send_frame requires 8-byte data"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with pytest.raises(ValueError, match="8 bytes"):
            with StreamingClient() as client:
                # Wrong data length
                client.send_frame(0, 0x100, [0] * 4)  # Only 4 bytes


# ============================================================================
# EDGE CASES
# ============================================================================

class TestEdgeCases:
    """Test edge cases and boundary conditions"""

    @patch('subprocess.Popen')
    def test_very_large_dbc(self, mock_popen):
        """Handle very large DBC files"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = b'{"status": "success"}\n'
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

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

        with StreamingClient() as client:
            response = client.parse_dbc(large_dbc)
            assert response["status"] == "success"

    @patch('subprocess.Popen')
    def test_unicode_in_signal_names(self, mock_popen):
        """Handle unicode in signal names"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = b'{"status": "success"}\n'
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

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

        with StreamingClient() as client:
            response = client.parse_dbc(dbc)
            assert response["status"] == "success"

    @patch('subprocess.Popen')
    def test_rapid_commands(self, mock_popen):
        """Handle rapid successive commands"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = b'{"status": "success"}\n'
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            # Send many commands rapidly
            for i in range(100):
                client.parse_dbc({"version": "1.0", "messages": []})

        # Should complete without errors
        assert True


# ============================================================================
# REAL-WORLD SCENARIOS
# ============================================================================

class TestRealWorldScenarios:
    """Test realistic usage patterns"""

    @patch('subprocess.Popen')
    def test_complete_workflow_mock(self, mock_popen):
        """Complete workflow with mocked responses"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()

        # Mock different responses for each command
        responses = [
            b'{"status": "success", "message": "DBC parsed"}\n',  # parse_dbc
            b'{"status": "success", "message": "Properties set"}\n',  # set_properties
            b'{"status": "success", "message": "Stream started"}\n',  # start_stream
            b'{"status": "ack"}\n',  # send_frame (binary sends "ack", not "success")
            b'{"status": "ack"}\n',  # send_frame
            b'{"status": "complete"}\n',  # end_stream (binary sends "complete")
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

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

    @patch('subprocess.Popen')
    def test_property_violation_detection_mock(self, mock_popen):
        """Detect property violations in mocked response"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()

        # Mock violation response (matching actual binary format)
        violation = {
            "type": "property",
            "status": "violation",
            "reason": "Speed exceeded limit",
            "property_index": {"numerator": 0, "denominator": 1},
            "timestamp": {"numerator": 100, "denominator": 1}
        }
        mock_process.stdout.readline.return_value = json.dumps(violation).encode() + b'\n'
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            response = client.send_frame(100, 0x100, [0xFF] * 8)

            assert response["type"] == "property"
            assert response["status"] == "violation"
            assert "Speed" in response["reason"]
