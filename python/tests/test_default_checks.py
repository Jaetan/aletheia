"""Tests for AletheiaClient default_checks and add_checks() API.

Verifies that default checks are correctly merged with session checks,
and that property indices are consistent across defaults + session checks.
"""

import pytest

from aletheia import AletheiaClient, Check, Signal
from aletheia.checks import CheckResult


# Simple DBC for testing
SIMPLE_DBC = {
    "version": "1.0",
    "messages": [
        {
            "id": 0x100,
            "name": "TestMsg",
            "dlc": 8,
            "sender": "ECU",
            "signals": [
                {
                    "name": "Speed",
                    "startBit": 0,
                    "length": 16,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 0.1,
                    "offset": 0.0,
                    "minimum": 0.0,
                    "maximum": 6553.5,
                    "unit": "kph",
                    "presence": "always",
                },
                {
                    "name": "Voltage",
                    "startBit": 16,
                    "length": 16,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 0.01,
                    "offset": 0.0,
                    "minimum": 0.0,
                    "maximum": 655.35,
                    "unit": "V",
                    "presence": "always",
                },
            ],
        }
    ],
}


def _make_frame(speed_raw: int, voltage_raw: int) -> bytearray:
    """Build a test frame from raw signal values."""
    return bytearray([
        speed_raw & 0xFF, (speed_raw >> 8) & 0xFF,
        voltage_raw & 0xFF, (voltage_raw >> 8) & 0xFF,
        0, 0, 0, 0,
    ])


class TestAddChecks:
    """Test add_checks() merges defaults + session checks."""

    def test_no_defaults_session_only(self) -> None:
        """add_checks() with no defaults works like set_properties()."""
        check = Check.signal("Speed").never_exceeds(200)
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            resp = client.add_checks([check])
            assert resp["status"] == "success"

            client.start_stream()
            # Speed = 100 raw * 0.1 = 10.0 kph — should pass
            result = client.send_frame(0, 0x100, _make_frame(100, 1200))
            assert result["status"] == "ack"
            client.end_stream()

    def test_defaults_only(self) -> None:
        """add_checks() with only defaults (empty session list)."""
        default = Check.signal("Speed").never_exceeds(200).named("Speed limit")
        with AletheiaClient(default_checks=[default]) as client:
            client.parse_dbc(SIMPLE_DBC)
            resp = client.add_checks([])
            assert resp["status"] == "success"

            client.start_stream()
            # Speed = 100 raw * 0.1 = 10.0 kph — should pass
            result = client.send_frame(0, 0x100, _make_frame(100, 1200))
            assert result["status"] == "ack"
            client.end_stream()

    def test_defaults_plus_session(self) -> None:
        """add_checks() merges defaults + session checks."""
        default = Check.signal("Speed").never_exceeds(200).named("Speed limit")
        session = Check.signal("Voltage").never_exceeds(15).named("Overvoltage")

        with AletheiaClient(default_checks=[default]) as client:
            client.parse_dbc(SIMPLE_DBC)
            resp = client.add_checks([session])
            assert resp["status"] == "success"

            client.start_stream()
            # Both signals within limits
            result = client.send_frame(0, 0x100, _make_frame(100, 1200))
            assert result["status"] == "ack"
            client.end_stream()

    def test_default_violation_correct_index(self) -> None:
        """Violation from a default check reports the correct property index."""
        default = Check.signal("Speed").never_exceeds(5).named("Speed limit")
        session = Check.signal("Voltage").never_exceeds(15).named("Overvoltage")

        with AletheiaClient(default_checks=[default]) as client:
            client.parse_dbc(SIMPLE_DBC)
            client.add_checks([session])
            client.start_stream()

            # Speed = 100 raw * 0.1 = 10.0 kph — exceeds limit of 5
            result = client.send_frame(0, 0x100, _make_frame(100, 1200))
            assert result["status"] == "violation"
            # Default is property 0
            prop_index = result["property_index"]
            assert prop_index["numerator"] // prop_index["denominator"] == 0
            client.end_stream()

    def test_session_violation_correct_index(self) -> None:
        """Violation from a session check reports correct index (offset by defaults)."""
        default = Check.signal("Speed").never_exceeds(200).named("Speed limit")
        session = Check.signal("Voltage").never_exceeds(5).named("Overvoltage")

        with AletheiaClient(default_checks=[default]) as client:
            client.parse_dbc(SIMPLE_DBC)
            client.add_checks([session])
            client.start_stream()

            # Voltage = 1200 raw * 0.01 = 12.0 V — exceeds limit of 5
            result = client.send_frame(0, 0x100, _make_frame(100, 1200))
            assert result["status"] == "violation"
            # Session check is property 1 (after 1 default)
            prop_index = result["property_index"]
            assert prop_index["numerator"] // prop_index["denominator"] == 1
            client.end_stream()

    def test_enrichment_with_defaults(self) -> None:
        """Violation enrichment works correctly with default checks."""
        default = Check.signal("Speed").never_exceeds(5).named("Speed limit")

        with AletheiaClient(default_checks=[default]) as client:
            client.parse_dbc(SIMPLE_DBC)
            client.add_checks([])
            client.start_stream()

            # Speed = 100 raw * 0.1 = 10.0 kph — violation
            result = client.send_frame(0, 0x100, _make_frame(100, 1200))
            assert result["status"] == "violation"
            assert result.get("signal_name") == "Speed"
            assert result.get("condition") == "< 5"
            assert result.get("actual_value") == pytest.approx(10.0)
            client.end_stream()


class TestDefaultChecksConstructor:
    """Test AletheiaClient(default_checks=...) constructor parameter."""

    def test_none_defaults(self) -> None:
        """default_checks=None is the same as no defaults."""
        with AletheiaClient(default_checks=None) as client:
            client.parse_dbc(SIMPLE_DBC)
            resp = client.add_checks([])
            assert resp["status"] == "success"

    def test_empty_defaults(self) -> None:
        """default_checks=[] is the same as no defaults."""
        with AletheiaClient(default_checks=[]) as client:
            client.parse_dbc(SIMPLE_DBC)
            resp = client.add_checks([])
            assert resp["status"] == "success"

    def test_defaults_not_modified(self) -> None:
        """add_checks() does not modify the original defaults list."""
        defaults = [Check.signal("Speed").never_exceeds(200)]
        original_len = len(defaults)

        with AletheiaClient(default_checks=defaults) as client:
            client.parse_dbc(SIMPLE_DBC)
            client.add_checks([Check.signal("Voltage").never_exceeds(15)])

        assert len(defaults) == original_len
