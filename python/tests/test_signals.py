"""
Unit tests for batch signal operations (Phase 2B.1).

Tests the FrameBuilder, SignalExtractor, and SignalExtractionResult classes
for signal encoding, extraction, and frame updates.

Note: These are unit tests that mock subprocess communication.
Integration tests with the actual binary are in test_integration.py.
"""

import pytest
from unittest.mock import Mock, patch, MagicMock, mock_open
from aletheia import FrameBuilder, SignalExtractor, SignalExtractionResult


@pytest.fixture
def mock_subprocess():
    """Mock subprocess.Popen for FrameBuilder/SignalExtractor"""
    with patch('aletheia.binary_client.subprocess.Popen') as mock_popen:
        # Create mock process
        mock_proc = MagicMock()
        mock_proc.stdin = MagicMock()
        mock_proc.stdout = MagicMock()
        mock_proc.stderr = MagicMock()
        mock_proc.poll.return_value = None  # Process is running

        # Mock successful DBC parsing response
        mock_proc.stdout.readline.return_value = '{"status":"success","message":"DBC parsed successfully"}\n'

        mock_popen.return_value = mock_proc
        yield mock_proc


@pytest.fixture
def mock_binary_path():
    """Mock binary path check"""
    with patch('aletheia.binary_utils.get_binary_path') as mock_path:
        mock_path.return_value = '/fake/path/to/aletheia'
        yield mock_path


class TestSignalExtractionResult:
    """Tests for SignalExtractionResult class"""

    def test_init_with_empty_results(self):
        """Test initialization with empty results"""
        result = SignalExtractionResult(
            values={},
            errors={},
            absent=[]
        )
        assert result.values == {}
        assert result.errors == {}
        assert result.absent == []
        assert not result.has_errors()

    def test_init_with_values(self):
        """Test initialization with successful extractions"""
        result = SignalExtractionResult(
            values={"EngineSpeed": 2000.0, "EngineTemp": 90.0},
            errors={},
            absent=[]
        )
        assert result.values["EngineSpeed"] == 2000.0
        assert result.values["EngineTemp"] == 90.0
        assert not result.has_errors()

    def test_init_with_errors(self):
        """Test initialization with extraction errors"""
        result = SignalExtractionResult(
            values={},
            errors={"ThrottlePosition": "Signal out of range"},
            absent=[]
        )
        assert result.has_errors()
        assert "ThrottlePosition" in result.errors
        assert result.errors["ThrottlePosition"] == "Signal out of range"

    def test_init_with_absent(self):
        """Test initialization with multiplexed signals"""
        result = SignalExtractionResult(
            values={"EngineSpeed": 2000.0},
            errors={},
            absent=["GearPosition", "ClutchStatus"]
        )
        assert "GearPosition" in result.absent
        assert "ClutchStatus" in result.absent
        assert len(result.absent) == 2

    def test_get_existing_signal(self):
        """Test getting an existing signal value"""
        result = SignalExtractionResult(
            values={"EngineSpeed": 2500.5},
            errors={},
            absent=[]
        )
        assert result.get("EngineSpeed") == 2500.5

    def test_get_missing_signal_with_default(self):
        """Test getting a missing signal returns default"""
        result = SignalExtractionResult(
            values={"EngineSpeed": 2000.0},
            errors={},
            absent=[]
        )
        assert result.get("BrakePressure", default=0.0) == 0.0
        assert result.get("ThrottlePosition", default=100.0) == 100.0

    def test_get_missing_signal_default_default(self):
        """Test get() with no explicit default uses 0.0"""
        result = SignalExtractionResult(values={}, errors={}, absent=[])
        assert result.get("MissingSignal") == 0.0

    def test_has_errors_false(self):
        """Test has_errors() returns False when no errors"""
        result = SignalExtractionResult(
            values={"Speed": 100.0},
            errors={},
            absent=[]
        )
        assert not result.has_errors()

    def test_has_errors_true(self):
        """Test has_errors() returns True when errors exist"""
        result = SignalExtractionResult(
            values={},
            errors={"Signal1": "error"},
            absent=[]
        )
        assert result.has_errors()

    def test_repr(self):
        """Test string representation"""
        result = SignalExtractionResult(
            values={"A": 1.0, "B": 2.0},
            errors={"C": "error"},
            absent=["D", "E", "F"]
        )
        repr_str = repr(result)
        assert "values=2" in repr_str
        assert "errors=1" in repr_str
        assert "absent=3" in repr_str


class TestFrameBuilder:
    """Tests for FrameBuilder class"""

    @pytest.fixture
    def sample_dbc(self):
        """Sample DBC definition"""
        return {
            "version": "1.0",
            "messages": [
                {
                    "id": 0x100,
                    "name": "EngineData",
                    "dlc": 8,
                    "sender": "ECU",
                    "signals": [
                        {
                            "name": "EngineSpeed",
                            "startBit": 0,
                            "length": 16,
                            "byteOrder": "little_endian",
                            "signed": False,
                            "factor": 0.25,
                            "offset": 0.0,
                            "minimum": 0.0,
                            "maximum": 16383.75,
                            "unit": "rpm",
                            "presence": "always"
                        },
                        {
                            "name": "EngineTemp",
                            "startBit": 16,
                            "length": 8,
                            "byteOrder": "little_endian",
                            "signed": False,
                            "factor": 1.0,
                            "offset": -40.0,
                            "minimum": -40.0,
                            "maximum": 215.0,
                            "unit": "°C",
                            "presence": "always"
                        }
                    ]
                }
            ]
        }

    def test_init(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test FrameBuilder initialization"""
        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder:
            assert builder._can_id == 0x100
            assert builder._dbc == sample_dbc
            assert builder._signals == {}

    def test_set_single_signal(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test setting a single signal"""
        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder:
            new_builder = builder.set("EngineSpeed", 2000.0)

            # Original builder unchanged (immutable)
            assert builder._signals == {}

            # New builder has signal
            assert new_builder._signals == {"EngineSpeed": 2000.0}

    def test_set_multiple_signals_chained(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test chaining multiple set() calls"""
        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder:
            final_builder = (builder
                .set("EngineSpeed", 2000.0)
                .set("EngineTemp", 90.0))

            assert final_builder._signals["EngineSpeed"] == 2000.0
            assert final_builder._signals["EngineTemp"] == 90.0
            assert len(final_builder._signals) == 2

    def test_immutability(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test that set() doesn't modify original builder"""
        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder1:
            builder2 = builder1.set("EngineSpeed", 2000.0)
            builder3 = builder2.set("EngineTemp", 90.0)

            # Each builder is independent
            assert len(builder1._signals) == 0
            assert len(builder2._signals) == 1
            assert len(builder3._signals) == 2

    def test_set_overwrites_value(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test that set() on same signal overwrites value"""
        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder:
            builder = builder.set("EngineSpeed", 2000.0)
            builder = builder.set("EngineSpeed", 2500.0)

            assert builder._signals["EngineSpeed"] == 2500.0

    def test_build(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test that build() calls Agda binary and returns frame"""
        # Mock buildFrame response (using decimal, not hex - JSON doesn't support hex)
        mock_subprocess.stdout.readline.side_effect = [
            '{"status":"success","message":"DBC parsed successfully"}\n',
            '{"status":"success","frame":[64,31,130,90,0,0,0,0]}\n'
        ]

        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder:
            builder = builder.set("EngineSpeed", 2000.0)
            frame = builder.build()

            assert frame == [64, 31, 130, 90, 0, 0, 0, 0]

    def test_repr(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test string representation"""
        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder:
            builder = (builder
                .set("EngineSpeed", 2000.0)
                .set("EngineTemp", 90.0))

            repr_str = repr(builder)
            assert "0x100" in repr_str
            assert "EngineSpeed" in repr_str
            assert "EngineTemp" in repr_str


class TestSignalExtractor:
    """Tests for SignalExtractor class"""

    @pytest.fixture
    def sample_dbc(self):
        """Sample DBC definition"""
        return {
            "version": "1.0",
            "messages": [
                {
                    "id": 0x100,
                    "name": "TestMessage",
                    "dlc": 8,
                    "signals": [
                        {"name": "Speed", "startBit": 0, "length": 16},
                        {"name": "Temp", "startBit": 16, "length": 8}
                    ]
                }
            ]
        }

    def test_init(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test SignalExtractor initialization"""
        with SignalExtractor(dbc=sample_dbc) as extractor:
            assert extractor._dbc == sample_dbc

    def test_extract_validates_frame_length(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test extract() rejects non-8-byte frames"""
        with SignalExtractor(dbc=sample_dbc) as extractor:
            with pytest.raises(ValueError, match="must be 8 bytes"):
                extractor.extract(can_id=0x100, data=[0x00, 0x01, 0x02])

            with pytest.raises(ValueError, match="must be 8 bytes"):
                extractor.extract(can_id=0x100, data=[0] * 10)

    def test_extract(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test extract() calls Agda binary and returns SignalExtractionResult"""
        # Mock extractAllSignals response
        mock_subprocess.stdout.readline.side_effect = [
            '{"status":"success","message":"DBC parsed successfully"}\n',
            '{"status":"success","values":[{"name":"Speed","value":120.5}],"errors":[],"absent":[]}\n'
        ]

        with SignalExtractor(dbc=sample_dbc) as extractor:
            result = extractor.extract(can_id=0x100, data=[0] * 8)

            assert result.values == {"Speed": 120.5}
            assert result.errors == {}
            assert result.absent == []

    def test_update_validates_frame_length(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test update() rejects non-8-byte frames"""
        with SignalExtractor(dbc=sample_dbc) as extractor:
            with pytest.raises(ValueError, match="must be 8 bytes"):
                extractor.update(
                    can_id=0x100,
                    frame=[0x00, 0x01],
                    signals={"Speed": 100.0}
                )

    def test_update(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test update() calls Agda binary and returns updated frame"""
        # Mock updateFrame response (using decimal, not hex - JSON doesn't support hex)
        mock_subprocess.stdout.readline.side_effect = [
            '{"status":"success","message":"DBC parsed successfully"}\n',
            '{"status":"success","frame":[100,0,0,0,0,0,0,0]}\n'
        ]

        with SignalExtractor(dbc=sample_dbc) as extractor:
            updated_frame = extractor.update(
                can_id=0x100,
                frame=[0] * 8,
                signals={"Speed": 100.0}
            )

            assert updated_frame == [100, 0, 0, 0, 0, 0, 0, 0]

    def test_repr(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test string representation"""
        with SignalExtractor(dbc=sample_dbc) as extractor:
            repr_str = repr(extractor)
            assert "SignalExtractor" in repr_str
            assert "dbc=loaded" in repr_str


class TestAPIUsagePatterns:
    """Integration-style tests for API usage patterns"""

    @pytest.fixture
    def sample_dbc(self):
        """Sample DBC definition"""
        return {
            "version": "1.0",
            "messages": [
                {
                    "id": 0x100,
                    "name": "EngineData",
                    "dlc": 8,
                    "signals": [
                        {"name": "Speed", "startBit": 0, "length": 16},
                        {"name": "Temp", "startBit": 16, "length": 8},
                        {"name": "Pressure", "startBit": 24, "length": 8}
                    ]
                }
            ]
        }

    def test_extraction_result_workflow(self):
        """Test typical workflow with extraction results"""
        # Simulate extraction results
        result = SignalExtractionResult(
            values={"Speed": 120.5, "Temp": 85.0},
            errors={"Pressure": "Value out of bounds"},
            absent=["GearPosition"]
        )

        # Check for errors
        if result.has_errors():
            assert "Pressure" in result.errors

        # Get values with defaults
        speed = result.get("Speed", default=0.0)
        gear = result.get("GearPosition", default=1.0)

        assert speed == 120.5
        assert gear == 1.0  # Used default

    def test_builder_fluent_interface(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test fluent interface pattern"""
        # This pattern should be ergonomic and readable
        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder:
            builder = (builder
                .set("Speed", 120.0)
                .set("Temp", 85.0)
                .set("Pressure", 100.0))

            assert len(builder._signals) == 3
            assert builder._signals["Speed"] == 120.0

    def test_builder_reuse(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test reusing a builder for similar frames"""
        with FrameBuilder(can_id=0x100, dbc=sample_dbc) as base_builder:
            # Create multiple frames with same base but different values
            frame1_builder = base_builder.set("Speed", 100.0).set("Temp", 80.0)
            frame2_builder = base_builder.set("Speed", 120.0).set("Temp", 90.0)

            # Builders are independent
            assert frame1_builder._signals["Speed"] == 100.0
            assert frame2_builder._signals["Speed"] == 120.0

    def test_separation_of_concerns(self, sample_dbc, mock_subprocess, mock_binary_path):
        """Test that signals module is independent from streaming"""
        # Can create signal tools without StreamingClient
        with SignalExtractor(dbc=sample_dbc) as extractor:
            with FrameBuilder(can_id=0x100, dbc=sample_dbc) as builder:
                # These are independent toolbox components
                assert extractor is not None
                assert builder is not None


class TestEdgeCases:
    """Tests for edge cases and error conditions"""

    def test_extraction_result_with_mixed_states(self):
        """Test extraction result with all three categories"""
        result = SignalExtractionResult(
            values={"A": 1.0, "B": 2.0},
            errors={"C": "error1", "D": "error2"},
            absent=["E", "F", "G"]
        )

        assert len(result.values) == 2
        assert len(result.errors) == 2
        assert len(result.absent) == 3
        assert result.has_errors()

    def test_builder_with_zero_signals(self, mock_subprocess, mock_binary_path):
        """Test builder with no signals set"""
        with FrameBuilder(can_id=0x100, dbc={}) as builder:
            assert len(builder._signals) == 0

    def test_builder_with_floating_point_precision(self, mock_subprocess, mock_binary_path):
        """Test builder handles floating point values correctly"""
        with FrameBuilder(can_id=0x100, dbc={}) as builder:
            builder = builder.set("Signal", 123.456789)

            assert builder._signals["Signal"] == 123.456789

    def test_extraction_result_empty_strings(self):
        """Test extraction result with empty signal names (invalid but should handle)"""
        result = SignalExtractionResult(
            values={"": 0.0},
            errors={},
            absent=[]
        )
        assert result.get("", default=1.0) == 0.0

    def test_builder_special_can_ids(self, mock_subprocess, mock_binary_path):
        """Test builder with various CAN ID values"""
        # Standard 11-bit ID
        with FrameBuilder(can_id=0x7FF, dbc={}) as builder1:
            assert builder1._can_id == 0x7FF

        # Extended 29-bit ID
        with FrameBuilder(can_id=0x1FFFFFFF, dbc={}) as builder2:
            assert builder2._can_id == 0x1FFFFFFF

        # Zero ID (valid)
        with FrameBuilder(can_id=0x000, dbc={}) as builder3:
            assert builder3._can_id == 0x000
