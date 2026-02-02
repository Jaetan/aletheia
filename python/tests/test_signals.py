"""
Unit tests for batch signal operations (Phase 2B.1).

Tests the FrameBuilder, SignalExtractor, and SignalExtractionResult classes
for signal encoding, extraction, and frame updates.

Note: These are unit tests that mock subprocess communication.
Integration tests with the actual binary are in test_integration.py.
"""

# DBC fixtures share required JSON structure (version, messages, id, name, dlc)
# pylint: disable=duplicate-code

import pytest

from aletheia import FrameBuilder, SignalExtractor, SignalExtractionResult
from aletheia.protocols import DBCDefinition
from tests.conftest import MockPopenFactory

# Fixtures are collected by pytest via the @pytest.fixture decorator.
__all__ = ["_engine_dbc", "_minimal_dbc", "_empty_dbc"]


@pytest.fixture(name="empty_dbc")
def _empty_dbc() -> DBCDefinition:
    """Empty DBC with no messages, for edge case testing."""
    return {"version": "1.0", "messages": []}


# ============================================================================
# SHARED FIXTURES
# ============================================================================

@pytest.fixture(name="engine_dbc")
def _engine_dbc() -> DBCDefinition:
    """Automotive DBC with full signal specifications.

    This fixture includes factor, offset, unit, and range fields that are
    required for encoding tests where signal scaling matters (e.g., converting
    2000 RPM to raw bytes using factor=0.25).
    """
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


@pytest.fixture(name="minimal_dbc")
def _minimal_dbc() -> DBCDefinition:
    """Minimal DBC with basic signal definitions.

    All fields are present as required by the protocol, but with simple default values.
    """
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x100,
                "name": "TestMessage",
                "dlc": 8,
                "sender": "TestECU",
                "signals": [
                    {
                        "name": "Speed",
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
                    },
                    {
                        "name": "Temp",
                        "startBit": 16,
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1.0,
                        "offset": 0.0,
                        "minimum": 0.0,
                        "maximum": 255.0,
                        "unit": "",
                        "presence": "always"
                    },
                    {
                        "name": "Pressure",
                        "startBit": 24,
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1.0,
                        "offset": 0.0,
                        "minimum": 0.0,
                        "maximum": 255.0,
                        "unit": "",
                        "presence": "always"
                    }
                ]
            }
        ]
    }


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

    def test_init(
        self, engine_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test FrameBuilder initialization"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=engine_dbc) as builder:
                assert builder.can_id == 0x100
                assert builder.signals == {}

    def test_set_single_signal(
        self, engine_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test setting a single signal"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=engine_dbc) as builder:
                new_builder = builder.set("EngineSpeed", 2000.0)

                # Original builder unchanged (immutable)
                assert builder.signals == {}

                # New builder has signal
                assert new_builder.signals == {"EngineSpeed": 2000.0}

    def test_set_multiple_signals_chained(
        self, engine_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test chaining multiple set() calls"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=engine_dbc) as builder:
                final_builder = (builder
                    .set("EngineSpeed", 2000.0)
                    .set("EngineTemp", 90.0))

                assert final_builder.signals["EngineSpeed"] == 2000.0
                assert final_builder.signals["EngineTemp"] == 90.0
                assert len(final_builder.signals) == 2

    def test_immutability(
        self, engine_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test that set() doesn't modify original builder"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=engine_dbc) as builder1:
                builder2 = builder1.set("EngineSpeed", 2000.0)
                builder3 = builder2.set("EngineTemp", 90.0)

                # Each builder is independent
                assert len(builder1.signals) == 0
                assert len(builder2.signals) == 1
                assert len(builder3.signals) == 2

    def test_set_overwrites_value(
        self, engine_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test that set() on same signal overwrites value"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=engine_dbc) as builder:
                builder = builder.set("EngineSpeed", 2000.0)
                builder = builder.set("EngineSpeed", 2500.0)

                assert builder.signals["EngineSpeed"] == 2500.0

    def test_build(
        self, engine_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test that build() calls Agda binary and returns frame"""
        responses = [
            '{"status":"success","message":"DBC parsed"}\n',
            '{"status":"success","frame":[64,31,130,90,0,0,0,0]}\n'
        ]
        with mock_popen_factory(responses):
            with FrameBuilder(can_id=0x100, dbc=engine_dbc) as builder:
                builder = builder.set("EngineSpeed", 2000.0)
                frame = builder.build()

                assert frame == [64, 31, 130, 90, 0, 0, 0, 0]

    def test_repr(
        self, engine_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test string representation"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=engine_dbc) as builder:
                builder = (builder
                    .set("EngineSpeed", 2000.0)
                    .set("EngineTemp", 90.0))

                repr_str = repr(builder)
                assert "0x100" in repr_str
                assert "EngineSpeed" in repr_str
                assert "EngineTemp" in repr_str


class TestSignalExtractor:
    """Tests for SignalExtractor class"""

    def test_init(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test SignalExtractor initialization"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with SignalExtractor(dbc=minimal_dbc) as extractor:
                # Extractor is ready to use (DBC loaded during init)
                assert repr(extractor) == "SignalExtractor(dbc=loaded)"

    def test_extract_validates_frame_length(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test extract() rejects non-8-byte frames"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with SignalExtractor(dbc=minimal_dbc) as extractor:
                with pytest.raises(ValueError, match="must be 8 bytes"):
                    extractor.extract(can_id=0x100, data=[0x00, 0x01, 0x02])

                with pytest.raises(ValueError, match="must be 8 bytes"):
                    extractor.extract(can_id=0x100, data=[0] * 10)

    def test_extract(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test extract() calls Agda binary and returns SignalExtractionResult"""
        responses = [
            '{"status":"success","message":"DBC parsed"}\n',
            '{"status":"success","values":[{"name":"Speed","value":120.5}],"errors":[],"absent":[]}\n'
        ]
        with mock_popen_factory(responses):
            with SignalExtractor(dbc=minimal_dbc) as extractor:
                result = extractor.extract(can_id=0x100, data=[0] * 8)

                assert result.values == {"Speed": 120.5}
                assert result.errors == {}
                assert result.absent == []

    def test_update_validates_frame_length(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test update() rejects non-8-byte frames"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with SignalExtractor(dbc=minimal_dbc) as extractor:
                with pytest.raises(ValueError, match="must be 8 bytes"):
                    extractor.update(
                        can_id=0x100,
                        frame=[0x00, 0x01],
                        signals={"Speed": 100.0}
                    )

    def test_update(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test update() calls Agda binary and returns updated frame"""
        responses = [
            '{"status":"success","message":"DBC parsed"}\n',
            '{"status":"success","data":[100,0,0,0,0,0,0,0]}\n'
        ]
        with mock_popen_factory(responses):
            with SignalExtractor(dbc=minimal_dbc) as extractor:
                updated_frame = extractor.update(
                    can_id=0x100,
                    frame=[0] * 8,
                    signals={"Speed": 100.0}
                )

                assert updated_frame == [100, 0, 0, 0, 0, 0, 0, 0]

    def test_repr(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test string representation"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with SignalExtractor(dbc=minimal_dbc) as extractor:
                repr_str = repr(extractor)
                assert "SignalExtractor" in repr_str
                assert "dbc=loaded" in repr_str


class TestAPIUsagePatterns:
    """Integration-style tests for API usage patterns"""

    def test_extraction_result_workflow(self) -> None:
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

    def test_builder_fluent_interface(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test fluent interface pattern"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=minimal_dbc) as builder:
                builder = (builder
                    .set("Speed", 120.0)
                    .set("Temp", 85.0)
                    .set("Pressure", 100.0))

                assert len(builder.signals) == 3
                assert builder.signals["Speed"] == 120.0

    def test_builder_reuse(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test reusing a builder for similar frames"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=minimal_dbc) as base_builder:
                # Create multiple frames with same base but different values
                frame1_builder = base_builder.set("Speed", 100.0).set("Temp", 80.0)
                frame2_builder = base_builder.set("Speed", 120.0).set("Temp", 90.0)

                # Builders are independent
                assert frame1_builder.signals["Speed"] == 100.0
                assert frame2_builder.signals["Speed"] == 120.0

    def test_separation_of_concerns(
        self, minimal_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test that signals module is independent from streaming"""
        # Need two responses: one for extractor, one for builder
        responses = [
            '{"status":"success","message":"DBC parsed"}\n',
            '{"status":"success","message":"DBC parsed"}\n'
        ]
        with mock_popen_factory(responses):
            with SignalExtractor(dbc=minimal_dbc) as extractor:
                with FrameBuilder(can_id=0x100, dbc=minimal_dbc) as builder:
                    # These are independent toolbox components
                    assert extractor is not None
                    assert builder is not None


class TestEdgeCases:
    """Tests for edge cases and error conditions"""

    def test_extraction_result_with_mixed_states(self) -> None:
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

    def test_builder_with_zero_signals(
        self, empty_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test builder with no signals set"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=empty_dbc) as builder:
                assert len(builder.signals) == 0

    def test_builder_with_floating_point_precision(
        self, empty_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test builder handles floating point values correctly"""
        with mock_popen_factory(['{"status":"success","message":"DBC parsed"}\n']):
            with FrameBuilder(can_id=0x100, dbc=empty_dbc) as builder:
                builder = builder.set("Signal", 123.456789)

                assert builder.signals["Signal"] == 123.456789

    def test_extraction_result_empty_strings(self) -> None:
        """Test extraction result with empty signal names (invalid but should handle)"""
        result = SignalExtractionResult(
            values={"": 0.0},
            errors={},
            absent=[]
        )
        assert result.get("", default=1.0) == 0.0

    def test_builder_special_can_ids(
        self, empty_dbc: DBCDefinition, mock_popen_factory: MockPopenFactory
    ) -> None:
        """Test builder with various CAN ID values"""
        # Need 3 responses for 3 builders
        responses = [
            '{"status":"success","message":"DBC parsed"}\n',
            '{"status":"success","message":"DBC parsed"}\n',
            '{"status":"success","message":"DBC parsed"}\n'
        ]
        with mock_popen_factory(responses):
            # Standard 11-bit ID
            with FrameBuilder(can_id=0x7FF, dbc=empty_dbc) as builder1:
                assert builder1.can_id == 0x7FF

            # Extended 29-bit ID
            with FrameBuilder(can_id=0x1FFFFFFF, dbc=empty_dbc) as builder2:
                assert builder2.can_id == 0x1FFFFFFF

            # Zero ID (valid)
            with FrameBuilder(can_id=0x000, dbc=empty_dbc) as builder3:
                assert builder3.can_id == 0x000
