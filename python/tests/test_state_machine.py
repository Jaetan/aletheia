"""State machine tests for StreamingClient protocol

Tests all valid and invalid state transitions to ensure correct protocol enforcement.

State Machine:
    Initial → (parse_dbc) → DBCLoaded → (set_properties) → PropertiesSet
    PropertiesSet → (start_stream) → Streaming → (send_frame)* → Streaming
    Streaming → (end_stream) → Complete
"""

from unittest.mock import Mock, patch

from aletheia import StreamingClient
from aletheia.dsl import Property
from aletheia.protocols import DBCDefinition
from tests.conftest import CANFrame


# ============================================================================
# VALID STATE TRANSITIONS
# ============================================================================

class TestValidTransitions:
    """Test valid state transitions through the protocol"""

    @patch('subprocess.Popen')
    def test_complete_happy_path(
        self,
        mock_popen: Mock,
        sample_dbc: DBCDefinition,
        sample_property: Property,
        sample_can_frame: CANFrame
    ) -> None:
        """Test complete valid workflow: parse → set → start → send → end"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.side_effect = [
            b'{"status": "success", "message": "DBC parsed"}\n',
            b'{"status": "success", "message": "Properties set"}\n',
            b'{"status": "success", "message": "Stream started"}\n',
            b'{"status": "ack"}\n',
            b'{"status": "complete"}\n',
        ]
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            # Transition: Initial → DBCLoaded
            assert client.parse_dbc(sample_dbc)["status"] == "success"

            # Transition: DBCLoaded → PropertiesSet
            assert client.set_properties([sample_property.to_dict()])["status"] == "success"

            # Transition: PropertiesSet → Streaming
            assert client.start_stream()["status"] == "success"

            # Transition: Streaming → Streaming (multiple frames allowed)
            frame = sample_can_frame
            assert client.send_frame(frame.timestamp, frame.can_id, frame.data)["status"] == "ack"

            # Transition: Streaming → Complete
            assert client.end_stream()["status"] == "complete"

    @patch('subprocess.Popen')
    def test_minimal_workflow(
        self, mock_popen: Mock, sample_dbc: DBCDefinition
    ) -> None:
        """Test minimal valid workflow: parse → set → start → end (no frames)"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        responses = [
            b'{"status": "success"}\n',
            b'{"status": "success"}\n',
            b'{"status": "success"}\n',
            b'{"status": "complete"}\n',
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            client.parse_dbc(sample_dbc)
            client.set_properties([])
            client.start_stream()
            result = client.end_stream()
            assert result["status"] == "complete"

    @patch('subprocess.Popen')
    def test_multiple_frames_in_streaming_state(
        self,
        mock_popen: Mock,
        sample_dbc: DBCDefinition,
        sample_can_frame: CANFrame
    ) -> None:
        """Test sending multiple frames while in streaming state"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        responses = [
            b'{"status": "success"}\n',  # parse_dbc
            b'{"status": "success"}\n',  # set_properties
            b'{"status": "success"}\n',  # start_stream
            b'{"status": "ack"}\n',      # send_frame 1
            b'{"status": "ack"}\n',      # send_frame 2
            b'{"status": "ack"}\n',      # send_frame 3
            b'{"status": "complete"}\n', # end_stream
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            client.parse_dbc(sample_dbc)
            client.set_properties([])
            client.start_stream()

            # Send multiple frames
            frame = sample_can_frame
            for i in range(3):
                resp = client.send_frame(frame.timestamp + i, frame.can_id, frame.data)
                assert resp["status"] == "ack"

            client.end_stream()


# ============================================================================
# INVALID STATE TRANSITIONS
# ============================================================================

class TestInvalidTransitions:
    """Test invalid state transitions are rejected"""

    @patch('subprocess.Popen')
    def test_send_frame_before_start_stream(
        self, mock_popen: Mock, sample_can_frame: CANFrame
    ) -> None:
        """Cannot send frame before starting stream (caught by Agda state machine)"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = b'{"status": "error", "message": "Not in streaming state"}\n'
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            # Try to send frame without starting stream
            # The Agda side will return an error
            frame = sample_can_frame
            resp = client.send_frame(frame.timestamp, frame.can_id, frame.data)
            assert resp["status"] == "error"

    @patch('subprocess.Popen')
    def test_start_stream_before_parse_dbc(self, mock_popen: Mock) -> None:
        """Cannot start stream before parsing DBC"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = b'{"status": "error", "message": "DBC not loaded"}\n'
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            # Try to start stream without DBC
            resp = client.start_stream()
            assert resp["status"] == "error"

    @patch('subprocess.Popen')
    def test_start_stream_before_set_properties(
        self, mock_popen: Mock, sample_dbc: DBCDefinition
    ) -> None:
        """Cannot start stream before setting properties"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        responses = [
            b'{"status": "success"}\n',  # parse_dbc
            b'{"status": "error", "message": "Properties not set"}\n',  # start_stream
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            client.parse_dbc(sample_dbc)
            # Try to start stream without setting properties
            resp = client.start_stream()
            assert resp["status"] == "error"

    @patch('subprocess.Popen')
    def test_parse_dbc_twice(
        self, mock_popen: Mock, sample_dbc: DBCDefinition
    ) -> None:
        """Cannot parse DBC twice"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        responses = [
            b'{"status": "success"}\n',  # First parse_dbc
            b'{"status": "error", "message": "DBC already loaded"}\n',  # Second parse_dbc
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            resp1 = client.parse_dbc(sample_dbc)
            assert resp1["status"] == "success"

            # Try to parse again
            resp2 = client.parse_dbc(sample_dbc)
            assert resp2["status"] == "error"

    @patch('subprocess.Popen')
    def test_set_properties_twice(
        self, mock_popen: Mock, sample_dbc: DBCDefinition
    ) -> None:
        """Cannot set properties twice"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        responses = [
            b'{"status": "success"}\n',  # parse_dbc
            b'{"status": "success"}\n',  # First set_properties
            b'{"status": "error", "message": "Properties already set"}\n',  # Second set_properties
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            client.parse_dbc(sample_dbc)
            resp1 = client.set_properties([])
            assert resp1["status"] == "success"

            # Try to set properties again
            resp2 = client.set_properties([])
            assert resp2["status"] == "error"

    @patch('subprocess.Popen')
    def test_end_stream_before_start_stream(
        self, mock_popen: Mock, sample_dbc: DBCDefinition
    ) -> None:
        """Cannot end stream before starting it"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        responses = [
            b'{"status": "success"}\n',  # parse_dbc
            b'{"status": "success"}\n',  # set_properties
            b'{"status": "error", "message": "Stream not started"}\n',  # end_stream
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            client.parse_dbc(sample_dbc)
            client.set_properties([])
            # Try to end stream without starting
            resp = client.end_stream()
            assert resp["status"] == "error"


# ============================================================================
# STATE RECOVERY AND EDGE CASES
# ============================================================================

class TestStateEdgeCases:
    """Test edge cases in state management"""

    @patch('subprocess.Popen')
    def test_empty_properties_list_allowed(
        self, mock_popen: Mock, sample_dbc: DBCDefinition
    ) -> None:
        """Empty properties list is valid (no checks needed)"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        responses = [
            b'{"status": "success"}\n',
            b'{"status": "success"}\n',
            b'{"status": "success"}\n',
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            client.parse_dbc(sample_dbc)
            resp = client.set_properties([])  # Empty list
            assert resp["status"] == "success"
            client.start_stream()

    @patch('subprocess.Popen')
    def test_property_violation_during_streaming(
        self,
        mock_popen: Mock,
        sample_dbc: DBCDefinition,
        sample_can_frame: CANFrame
    ) -> None:
        """Property violation response during streaming is valid"""
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        violation_response = (
            b'{"type": "property", "status": "violation", '
            b'"reason": "Speed exceeded", '
            b'"property_index": {"numerator": 0, "denominator": 1}, '
            b'"timestamp": {"numerator": 1000, "denominator": 1}}\n'
        )
        responses = [
            b'{"status": "success"}\n',  # parse_dbc
            b'{"status": "success"}\n',  # set_properties
            b'{"status": "success"}\n',  # start_stream
            violation_response,
            b'{"status": "complete"}\n',  # end_stream
        ]
        mock_process.stdout.readline.side_effect = responses
        mock_process.poll.return_value = None
        mock_popen.return_value = mock_process

        with StreamingClient() as client:
            client.parse_dbc(sample_dbc)
            client.set_properties([])
            client.start_stream()

            # Send frame that triggers violation
            frame = sample_can_frame
            resp = client.send_frame(frame.timestamp, frame.can_id, frame.data)
            assert resp.get("type") == "property"
            assert resp["status"] == "violation"

            # Can still end stream after violation
            end_resp = client.end_stream()
            assert end_resp["status"] == "complete"
