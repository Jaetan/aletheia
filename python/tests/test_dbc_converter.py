"""Unit tests for DBC converter (cantools → JSON)

Tests cover:
- signal_to_json: Basic signals, multiplexing, byte order, signed/unsigned
- message_to_json: Messages with signals, extended frames, senders
- dbc_to_json: Full DBC conversion
- convert_dbc_file: File I/O
- Error handling: Invalid inputs, missing files
"""

import pytest
import json
import tempfile
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock

from aletheia.dbc_converter import (
    signal_to_json,
    message_to_json,
    dbc_to_json,
    convert_dbc_file
)


# ============================================================================
# SIGNAL CONVERSION
# ============================================================================

class TestSignalConversion:
    """Test signal_to_json function"""

    def test_basic_signal(self):
        """Basic signal converts correctly"""
        signal = Mock()
        signal.name = "Speed"
        signal.start = 0
        signal.length = 16
        signal.byte_order = "little_endian"
        signal.is_signed = False
        signal.scale = 0.01
        signal.offset = 0
        signal.minimum = 0
        signal.maximum = 655.35
        signal.unit = "kph"
        signal.multiplexer_ids = None
        signal.multiplexer_signal = None

        result = signal_to_json(signal)

        assert result["name"] == "Speed"
        assert result["startBit"] == 0
        assert result["length"] == 16
        assert result["byteOrder"] == "little_endian"
        assert result["signed"] == False
        assert result["factor"] == 0.01
        assert result["offset"] == 0
        assert result["minimum"] == 0
        assert result["maximum"] == 655.35
        assert result["unit"] == "kph"
        assert result["presence"] == "always"

    def test_signal_big_endian(self):
        """Big endian signal converts correctly"""
        signal = Mock()
        signal.name = "EngineSpeed"
        signal.start = 0
        signal.length = 16
        signal.byte_order = "big_endian"
        signal.is_signed = False
        signal.scale = 1
        signal.offset = 0
        signal.minimum = 0
        signal.maximum = 8000
        signal.unit = "rpm"
        signal.multiplexer_ids = None

        result = signal_to_json(signal)

        assert result["byteOrder"] == "big_endian"

    def test_signal_signed(self):
        """Signed signal converts correctly"""
        signal = Mock()
        signal.name = "Temperature"
        signal.start = 0
        signal.length = 16
        signal.byte_order = "little_endian"
        signal.is_signed = True
        signal.scale = 0.1
        signal.offset = -40
        signal.minimum = -40
        signal.maximum = 215
        signal.unit = "°C"
        signal.multiplexer_ids = None

        result = signal_to_json(signal)

        assert result["signed"] == True
        assert result["offset"] == -40

    def test_signal_without_unit(self):
        """Signal without unit uses empty string"""
        signal = Mock()
        signal.name = "Status"
        signal.start = 0
        signal.length = 8
        signal.byte_order = "little_endian"
        signal.is_signed = False
        signal.scale = 1
        signal.offset = 0
        signal.minimum = 0
        signal.maximum = 255
        signal.unit = None  # No unit
        signal.multiplexer_ids = None

        result = signal_to_json(signal)

        assert result["unit"] == ""

    def test_signal_multiplexed_with_value(self):
        """Multiplexed signal with specific value"""
        signal = Mock()
        signal.name = "MultiplexedSignal"
        signal.start = 8
        signal.length = 16
        signal.byte_order = "little_endian"
        signal.is_signed = False
        signal.scale = 1
        signal.offset = 0
        signal.minimum = 0
        signal.maximum = 100
        signal.unit = ""
        signal.multiplexer_ids = [5, 6, 7]  # Multiple values
        signal.multiplexer_signal = "Multiplexor"

        result = signal_to_json(signal)

        # Should use first multiplexer value
        assert result["multiplexor"] == "Multiplexor"
        assert result["multiplex_value"] == 5
        assert "presence" not in result

    def test_signal_multiplexed_no_values(self):
        """Multiplexed signal without specific values"""
        signal = Mock()
        signal.name = "SomeSignal"
        signal.start = 0
        signal.length = 8
        signal.byte_order = "little_endian"
        signal.is_signed = False
        signal.scale = 1
        signal.offset = 0
        signal.minimum = 0
        signal.maximum = 255
        signal.unit = ""
        signal.multiplexer_ids = []  # Empty list
        signal.multiplexer_signal = "Mux"

        result = signal_to_json(signal)

        # Treated as always present
        assert result["presence"] == "always"

    def test_signal_zero_scale_and_offset(self):
        """Signal with zero scale and offset"""
        signal = Mock()
        signal.name = "RawValue"
        signal.start = 0
        signal.length = 8
        signal.byte_order = "little_endian"
        signal.is_signed = False
        signal.scale = 1  # No scaling
        signal.offset = 0  # No offset
        signal.minimum = 0
        signal.maximum = 255
        signal.unit = ""
        signal.multiplexer_ids = None

        result = signal_to_json(signal)

        assert result["factor"] == 1
        assert result["offset"] == 0

    def test_signal_fractional_scale(self):
        """Signal with fractional scale factor"""
        signal = Mock()
        signal.name = "Voltage"
        signal.start = 0
        signal.length = 16
        signal.byte_order = "little_endian"
        signal.is_signed = False
        signal.scale = 0.001
        signal.offset = 0
        signal.minimum = 0
        signal.maximum = 65.535
        signal.unit = "V"
        signal.multiplexer_ids = None

        result = signal_to_json(signal)

        assert result["factor"] == 0.001


# ============================================================================
# MESSAGE CONVERSION
# ============================================================================

class TestMessageConversion:
    """Test message_to_json function"""

    def test_basic_message(self):
        """Basic message with signals"""
        signal1 = Mock()
        signal1.name = "Speed"
        signal1.start = 0
        signal1.length = 16
        signal1.byte_order = "little_endian"
        signal1.is_signed = False
        signal1.scale = 0.01
        signal1.offset = 0
        signal1.minimum = 0
        signal1.maximum = 655.35
        signal1.unit = "kph"
        signal1.multiplexer_ids = None

        message = Mock()
        message.frame_id = 0x100
        message.name = "VehicleSpeed"
        message.length = 8
        message.senders = ["ECU1"]
        message.signals = [signal1]
        message.is_extended_frame = False

        result = message_to_json(message)

        assert result["id"] == 0x100
        assert result["name"] == "VehicleSpeed"
        assert result["dlc"] == 8
        assert result["sender"] == "ECU1"
        assert len(result["signals"]) == 1
        assert result["signals"][0]["name"] == "Speed"
        assert "extended" not in result

    def test_message_extended_frame(self):
        """Extended frame message"""
        message = Mock()
        message.frame_id = 0x1FFFFFFF
        message.name = "ExtendedMessage"
        message.length = 8
        message.senders = ["ECU2"]
        message.signals = []
        message.is_extended_frame = True

        result = message_to_json(message)

        assert result["id"] == 0x1FFFFFFF
        assert result["extended"] == True

    def test_message_no_sender(self):
        """Message without sender"""
        message = Mock()
        message.frame_id = 0x200
        message.name = "NoSender"
        message.length = 8
        message.senders = []  # No senders
        message.signals = []
        message.is_extended_frame = False

        result = message_to_json(message)

        assert result["sender"] == ""

    def test_message_multiple_signals(self):
        """Message with multiple signals"""
        signals = []
        for i in range(3):
            sig = Mock()
            sig.name = f"Signal{i}"
            sig.start = i * 8
            sig.length = 8
            sig.byte_order = "little_endian"
            sig.is_signed = False
            sig.scale = 1
            sig.offset = 0
            sig.minimum = 0
            sig.maximum = 255
            sig.unit = ""
            sig.multiplexer_ids = None
            signals.append(sig)

        message = Mock()
        message.frame_id = 0x300
        message.name = "MultiSignal"
        message.length = 8
        message.senders = ["ECU"]
        message.signals = signals
        message.is_extended_frame = False

        result = message_to_json(message)

        assert len(result["signals"]) == 3
        assert result["signals"][0]["name"] == "Signal0"
        assert result["signals"][1]["name"] == "Signal1"
        assert result["signals"][2]["name"] == "Signal2"

    def test_message_short_dlc(self):
        """Message with DLC less than 8"""
        message = Mock()
        message.frame_id = 0x400
        message.name = "ShortMessage"
        message.length = 4
        message.senders = ["ECU"]
        message.signals = []
        message.is_extended_frame = False

        result = message_to_json(message)

        assert result["dlc"] == 4

    def test_message_multiple_senders(self):
        """Message with multiple senders (uses first)"""
        message = Mock()
        message.frame_id = 0x500
        message.name = "MultiSender"
        message.length = 8
        message.senders = ["ECU1", "ECU2", "ECU3"]
        message.signals = []
        message.is_extended_frame = False

        result = message_to_json(message)

        assert result["sender"] == "ECU1"  # Uses first sender


# ============================================================================
# FULL DBC CONVERSION
# ============================================================================

class TestDBCConversion:
    """Test dbc_to_json function"""

    @patch('cantools.database.load_file')
    def test_basic_dbc(self, mock_load):
        """Basic DBC file conversion"""
        # Mock database
        db = Mock()
        db.version = "1.0"

        # Mock message
        signal = Mock()
        signal.name = "Speed"
        signal.start = 0
        signal.length = 16
        signal.byte_order = "little_endian"
        signal.is_signed = False
        signal.scale = 0.01
        signal.offset = 0
        signal.minimum = 0
        signal.maximum = 655.35
        signal.unit = "kph"
        signal.multiplexer_ids = None

        message = Mock()
        message.frame_id = 0x100
        message.name = "VehicleSpeed"
        message.length = 8
        message.senders = ["ECU"]
        message.signals = [signal]
        message.is_extended_frame = False

        db.messages = [message]
        mock_load.return_value = db

        result = dbc_to_json("test.dbc")

        assert result["version"] == "1.0"
        assert len(result["messages"]) == 1
        assert result["messages"][0]["name"] == "VehicleSpeed"

    @patch('cantools.database.load_file')
    def test_dbc_no_version(self, mock_load):
        """DBC without version uses default"""
        db = Mock()
        db.version = None  # No version
        db.messages = []
        mock_load.return_value = db

        result = dbc_to_json("test.dbc")

        assert result["version"] == "1.0"  # Default

    @patch('cantools.database.load_file')
    def test_dbc_multiple_messages(self, mock_load):
        """DBC with multiple messages"""
        db = Mock()
        db.version = "2.0"

        messages = []
        for i in range(5):
            msg = Mock()
            msg.frame_id = 0x100 + i
            msg.name = f"Message{i}"
            msg.length = 8
            msg.senders = ["ECU"]
            msg.signals = []
            msg.is_extended_frame = False
            messages.append(msg)

        db.messages = messages
        mock_load.return_value = db

        result = dbc_to_json("test.dbc")

        assert len(result["messages"]) == 5
        assert result["messages"][0]["name"] == "Message0"
        assert result["messages"][4]["name"] == "Message4"

    @patch('cantools.database.load_file')
    def test_dbc_empty(self, mock_load):
        """Empty DBC file"""
        db = Mock()
        db.version = "1.0"
        db.messages = []
        mock_load.return_value = db

        result = dbc_to_json("empty.dbc")

        assert result["version"] == "1.0"
        assert result["messages"] == []


# ============================================================================
# FILE I/O
# ============================================================================

class TestFileIO:
    """Test convert_dbc_file function"""

    @patch('cantools.database.load_file')
    def test_convert_to_string(self, mock_load):
        """Convert DBC to JSON string"""
        db = Mock()
        db.version = "1.0"
        db.messages = []
        mock_load.return_value = db

        result = convert_dbc_file("test.dbc")

        assert isinstance(result, str)
        data = json.loads(result)
        assert data["version"] == "1.0"
        assert data["messages"] == []

    @patch('cantools.database.load_file')
    def test_convert_to_file(self, mock_load):
        """Convert DBC and write to file"""
        db = Mock()
        db.version = "1.0"
        db.messages = []
        mock_load.return_value = db

        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.json') as f:
            output_path = f.name

        try:
            result = convert_dbc_file("test.dbc", output_path)

            # Check return value
            assert isinstance(result, str)
            data = json.loads(result)
            assert data["version"] == "1.0"

            # Check file was written
            output_file = Path(output_path)
            assert output_file.exists()

            # Check file contents
            file_data = json.loads(output_file.read_text())
            assert file_data["version"] == "1.0"
        finally:
            Path(output_path).unlink(missing_ok=True)

    @patch('cantools.database.load_file')
    def test_json_formatting(self, mock_load):
        """JSON output is formatted with indentation"""
        db = Mock()
        db.version = "1.0"
        db.messages = []
        mock_load.return_value = db

        result = convert_dbc_file("test.dbc")

        # Check formatting (should have newlines and spaces)
        assert '\n' in result
        assert '  ' in result  # 2-space indentation


# ============================================================================
# ERROR HANDLING
# ============================================================================

class TestErrorHandling:
    """Test error handling and edge cases"""

    @patch('cantools.database.load_file')
    def test_invalid_dbc_file(self, mock_load):
        """Invalid DBC file raises exception"""
        mock_load.side_effect = Exception("Invalid DBC format")

        with pytest.raises(Exception, match="Invalid DBC format"):
            dbc_to_json("invalid.dbc")

    @patch('cantools.database.load_file')
    def test_missing_file(self, mock_load):
        """Missing file raises FileNotFoundError"""
        mock_load.side_effect = FileNotFoundError("File not found")

        with pytest.raises(FileNotFoundError, match="File not found"):
            dbc_to_json("nonexistent.dbc")

    def test_pathlib_path_support(self):
        """Function accepts pathlib.Path objects"""
        with patch('cantools.database.load_file') as mock_load:
            db = Mock()
            db.version = "1.0"
            db.messages = []
            mock_load.return_value = db

            path = Path("test.dbc")
            result = dbc_to_json(path)

            # Should convert Path to str
            mock_load.assert_called_once_with(str(path))
            assert result["version"] == "1.0"


# ============================================================================
# INTEGRATION-STYLE TESTS
# ============================================================================

class TestIntegrationStyle:
    """Integration-style tests with realistic data"""

    @patch('cantools.database.load_file')
    def test_realistic_automotive_message(self, mock_load):
        """Realistic automotive CAN message"""
        # Create realistic signal (vehicle speed)
        speed_signal = Mock()
        speed_signal.name = "VehicleSpeed"
        speed_signal.start = 0
        speed_signal.length = 16
        speed_signal.byte_order = "little_endian"
        speed_signal.is_signed = False
        speed_signal.scale = 0.01
        speed_signal.offset = 0
        speed_signal.minimum = 0
        speed_signal.maximum = 655.35
        speed_signal.unit = "kph"
        speed_signal.multiplexer_ids = None

        # Create message
        message = Mock()
        message.frame_id = 0x100
        message.name = "VehicleDynamics"
        message.length = 8
        message.senders = ["VehicleController"]
        message.signals = [speed_signal]
        message.is_extended_frame = False

        db = Mock()
        db.version = "1.0"
        db.messages = [message]
        mock_load.return_value = db

        result = dbc_to_json("vehicle.dbc")

        # Verify complete structure
        assert result["version"] == "1.0"
        assert len(result["messages"]) == 1

        msg = result["messages"][0]
        assert msg["id"] == 0x100
        assert msg["name"] == "VehicleDynamics"
        assert msg["dlc"] == 8
        assert msg["sender"] == "VehicleController"

        sig = msg["signals"][0]
        assert sig["name"] == "VehicleSpeed"
        assert sig["startBit"] == 0
        assert sig["length"] == 16
        assert sig["byteOrder"] == "little_endian"
        assert sig["signed"] == False
        assert sig["factor"] == 0.01
        assert sig["offset"] == 0
        assert sig["minimum"] == 0
        assert sig["maximum"] == 655.35
        assert sig["unit"] == "kph"
        assert sig["presence"] == "always"

    @patch('cantools.database.load_file')
    def test_mixed_standard_and_extended_frames(self, mock_load):
        """DBC with both standard and extended frames"""
        std_msg = Mock()
        std_msg.frame_id = 0x100
        std_msg.name = "StandardMessage"
        std_msg.length = 8
        std_msg.senders = ["ECU1"]
        std_msg.signals = []
        std_msg.is_extended_frame = False

        ext_msg = Mock()
        ext_msg.frame_id = 0x18FF1234
        ext_msg.name = "ExtendedMessage"
        ext_msg.length = 8
        ext_msg.senders = ["ECU2"]
        ext_msg.signals = []
        ext_msg.is_extended_frame = True

        db = Mock()
        db.version = "1.0"
        db.messages = [std_msg, ext_msg]
        mock_load.return_value = db

        result = dbc_to_json("mixed.dbc")

        assert len(result["messages"]) == 2
        assert "extended" not in result["messages"][0]
        assert result["messages"][1]["extended"] == True
