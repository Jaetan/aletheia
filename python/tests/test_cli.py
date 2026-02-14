"""Unit tests for the CLI module

Tests cover:
- Hex data parsing: various formats -> bytearray
- CAN ID parsing: hex/decimal, error cases
- Timestamp formatting: microseconds -> human-readable
- Rational number conversion: {numerator, denominator} -> int
- Signals subcommand: text and JSON output from sample DBC
- Extract subcommand: signal decoding via FFI
- Check subcommand: streaming LTL checking via FFI
- Error handling: missing files, bad arguments, exit codes
"""

from __future__ import annotations

import json
from pathlib import Path

import can
import pytest

from aletheia.cli import (
    format_timestamp,
    parse_can_id,
    parse_hex_data,
    rational_to_int,
    main,
)


# ============================================================================
# Shared DBC content
# ============================================================================

_DBC_HEADER = (
    'VERSION ""\n\n'
    + "NS_ :\n\n"
    + "BS_:\n\n"
    + "BU_:\n\n"
)

_DBC_ENGINE_MSG = (
    "BO_ 256 EngineStatus: 8 ECU1\n"
    + ' SG_ EngineSpeed : 0|16@1+ (0.25,0) [0|8000] "rpm" Vector__XXX\n'
    + ' SG_ EngineTemp : 16|8@1+ (1,-40) [-40|215] "celsius" Vector__XXX\n'
)

_DBC_BRAKE_MSG = (
    "BO_ 512 BrakeStatus: 8 ECU2\n"
    + ' SG_ BrakePressure : 0|16@1+ (0.1,0) [0|6553.5] "bar" Vector__XXX\n'
)

_CHECKS_YAML = (
    "checks:\n"
    + "  - name: Speed limit\n"
    + "    signal: EngineSpeed\n"
    + "    condition: never_exceeds\n"
    + "    value: 200\n"
    + "    severity: critical\n"
)


def _write_dbc(path: Path, *messages: str) -> None:
    """Write a minimal .dbc file from message blocks."""
    path.write_text(_DBC_HEADER + "\n".join(messages))


def _write_asc(path: Path, messages: list[can.Message]) -> None:
    """Write CAN messages to an ASC file."""
    writer = can.ASCWriter(str(path))
    for msg in messages:
        writer.on_message_received(msg)
    writer.stop()


# ============================================================================
# Hex data parsing
# ============================================================================

class TestParseHexData:
    """Test parse_hex_data: various hex formats -> bytearray."""

    def test_contiguous_hex(self) -> None:
        result = parse_hex_data("401F820000000000")
        assert result == bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])

    def test_space_separated(self) -> None:
        result = parse_hex_data("40 1F 82 00 00 00 00 00")
        assert result == bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])

    def test_colon_separated(self) -> None:
        result = parse_hex_data("40:1F:82:00:00:00:00:00")
        assert result == bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])

    def test_with_0x_prefix(self) -> None:
        result = parse_hex_data("0x401F820000000000")
        assert result == bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])

    def test_lowercase(self) -> None:
        result = parse_hex_data("deadbeef")
        assert result == bytearray([0xDE, 0xAD, 0xBE, 0xEF])

    def test_empty_string(self) -> None:
        result = parse_hex_data("")
        assert result == bytearray()

    def test_odd_length_raises(self) -> None:
        with pytest.raises(ValueError, match="odd number"):
            parse_hex_data("ABC")

    def test_invalid_hex_raises(self) -> None:
        with pytest.raises(ValueError, match="invalid hex"):
            parse_hex_data("ZZZZ")


# ============================================================================
# CAN ID parsing
# ============================================================================

class TestParseCanId:
    """Test parse_can_id: hex/decimal parsing, error cases."""

    def test_hex_id(self) -> None:
        assert parse_can_id("0x100") == 256

    def test_hex_uppercase(self) -> None:
        assert parse_can_id("0X1FF") == 511

    def test_decimal_id(self) -> None:
        assert parse_can_id("256") == 256

    def test_zero(self) -> None:
        assert parse_can_id("0") == 0

    def test_whitespace_stripped(self) -> None:
        assert parse_can_id("  0x100  ") == 256

    def test_invalid_raises(self) -> None:
        with pytest.raises(ValueError, match="invalid CAN ID"):
            parse_can_id("not_a_number")


# ============================================================================
# Timestamp formatting
# ============================================================================

class TestFormatTimestamp:
    """Test format_timestamp: microseconds -> human-readable string."""

    def test_zero(self) -> None:
        assert format_timestamp(0) == "0.000ms"

    def test_milliseconds(self) -> None:
        assert format_timestamp(1234500) == "1234.500ms"

    def test_exact_ms(self) -> None:
        assert format_timestamp(1000) == "1.000ms"

    def test_sub_millisecond(self) -> None:
        assert format_timestamp(500) == "0.500ms"


# ============================================================================
# Rational number conversion
# ============================================================================

class TestRationalToInt:
    """Test rational_to_int: {numerator, denominator} -> int."""

    def test_simple(self) -> None:
        assert rational_to_int({"numerator": 0, "denominator": 1}) == 0

    def test_integer_value(self) -> None:
        assert rational_to_int({"numerator": 42, "denominator": 1}) == 42

    def test_floor_division(self) -> None:
        assert rational_to_int({"numerator": 7, "denominator": 2}) == 3

    def test_large_value(self) -> None:
        assert rational_to_int({"numerator": 1234500, "denominator": 1}) == 1234500


# ============================================================================
# Signals subcommand
# ============================================================================

class TestSignalsCommand:
    """Test 'aletheia signals' -- pure DBC traversal, no FFI needed."""

    @pytest.fixture()
    def dbc_file(self, tmp_path: Path) -> Path:
        """Create a .dbc file with two messages."""
        p = tmp_path / "test.dbc"
        _write_dbc(p, _DBC_ENGINE_MSG, _DBC_BRAKE_MSG)
        return p

    def test_text_output(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        code = main(["signals", "--dbc", str(dbc_file)])
        assert code == 0
        out = capsys.readouterr().out
        assert "EngineStatus" in out
        assert "EngineSpeed" in out
        assert "BrakePressure" in out
        assert "2 messages, 3 signals" in out

    def test_json_output(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        code = main(["signals", "--dbc", str(dbc_file), "--json"])
        assert code == 0
        out = capsys.readouterr().out
        data = json.loads(out)
        assert "messages" in data
        assert len(data["messages"]) == 2

    def test_missing_dbc_file(self, capsys: pytest.CaptureFixture[str]) -> None:
        code = main(["signals", "--dbc", "/nonexistent/file.dbc"])
        assert code == 2

    def test_no_dbc_specified(self) -> None:
        code = main(["signals"])
        assert code == 2


# ============================================================================
# Extract subcommand (requires FFI)
# ============================================================================

class TestExtractCommand:
    """Test 'aletheia extract' -- requires FFI shared library."""

    @pytest.fixture()
    def dbc_file(self, tmp_path: Path) -> Path:
        p = tmp_path / "test.dbc"
        _write_dbc(p, _DBC_ENGINE_MSG)
        return p

    def test_text_output(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        # EngineSpeed at bits 0:16 LE unsigned, factor=0.25, offset=0
        # Raw value 0x0320 = 800, physical = 800 * 0.25 = 200.0 rpm
        code = main(["extract", "--dbc", str(dbc_file), "0x100", "2003000000000000"])
        assert code == 0
        out = capsys.readouterr().out
        assert "EngineStatus" in out
        assert "EngineSpeed" in out
        assert "Errors: none" in out

    def test_json_output(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        code = main(["extract", "--dbc", str(dbc_file), "0x100", "2003000000000000", "--json"])
        assert code == 0
        out = capsys.readouterr().out
        data = json.loads(out)
        assert data["can_id"] == 0x100
        assert "values" in data
        assert "EngineSpeed" in data["values"]

    def test_decimal_can_id(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        code = main(["extract", "--dbc", str(dbc_file), "256", "0000000000000000"])
        assert code == 0

    def test_space_separated_data(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        code = main(["extract", "--dbc", str(dbc_file), "0x100", "20 03 00 00 00 00 00 00"])
        assert code == 0

    def test_wrong_data_length(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        code = main(["extract", "--dbc", str(dbc_file), "0x100", "AABB"])
        assert code == 2

    def test_missing_dbc(self) -> None:
        code = main(["extract", "--dbc", "/nonexistent.dbc", "0x100", "0000000000000000"])
        assert code == 2


# ============================================================================
# Check subcommand (requires FFI)
# ============================================================================

class TestCheckCommand:
    """Test 'aletheia check' -- requires FFI shared library."""

    @pytest.fixture()
    def dbc_file(self, tmp_path: Path) -> Path:
        p = tmp_path / "test.dbc"
        _write_dbc(p, _DBC_ENGINE_MSG)
        return p

    @pytest.fixture()
    def checks_file(self, tmp_path: Path) -> Path:
        p = tmp_path / "checks.yaml"
        p.write_text(_CHECKS_YAML)
        return p

    def test_passing_log(
        self,
        dbc_file: Path,
        checks_file: Path,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """All checks pass -- exit code 0."""
        asc_file = tmp_path / "pass.asc"
        # EngineSpeed raw = 400 -> physical = 400 * 0.25 = 100.0 rpm (< 200)
        _write_asc(asc_file, [
            can.Message(
                timestamp=1.0,
                arbitration_id=0x100,
                data=bytearray([0x90, 0x01, 0, 0, 0, 0, 0, 0]),
                is_extended_id=False,
            ),
        ])

        code = main([
            "check",
            "--dbc", str(dbc_file),
            "--checks", str(checks_file),
            str(asc_file),
        ])
        assert code == 0
        out = capsys.readouterr().out
        assert "all checks passed" in out

    def test_passing_log_json(
        self,
        dbc_file: Path,
        checks_file: Path,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """JSON output when all checks pass."""
        asc_file = tmp_path / "pass.asc"
        _write_asc(asc_file, [
            can.Message(
                timestamp=1.0,
                arbitration_id=0x100,
                data=bytearray([0x90, 0x01, 0, 0, 0, 0, 0, 0]),
                is_extended_id=False,
            ),
        ])

        code = main([
            "check",
            "--dbc", str(dbc_file),
            "--checks", str(checks_file),
            "--json",
            str(asc_file),
        ])
        assert code == 0
        out = capsys.readouterr().out
        data = json.loads(out)
        assert data["status"] == "pass"
        assert data["total_violations"] == 0
        assert data["violations"] == []

    def test_violation_detected(
        self,
        dbc_file: Path,
        checks_file: Path,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Violation detected -- exit code 1."""
        asc_file = tmp_path / "fail.asc"
        # EngineSpeed raw = 4000 -> physical = 4000 * 0.25 = 1000.0 rpm (> 200)
        _write_asc(asc_file, [
            can.Message(
                timestamp=1.0,
                arbitration_id=0x100,
                data=bytearray([0xA0, 0x0F, 0, 0, 0, 0, 0, 0]),
                is_extended_id=False,
            ),
        ])

        code = main([
            "check",
            "--dbc", str(dbc_file),
            "--checks", str(checks_file),
            str(asc_file),
        ])
        assert code == 1
        out = capsys.readouterr().out
        assert "violations found" in out.lower() or "violation" in out.lower()

    def test_violation_json(
        self,
        dbc_file: Path,
        checks_file: Path,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """JSON output with violations."""
        asc_file = tmp_path / "fail.asc"
        _write_asc(asc_file, [
            can.Message(
                timestamp=1.0,
                arbitration_id=0x100,
                data=bytearray([0xA0, 0x0F, 0, 0, 0, 0, 0, 0]),
                is_extended_id=False,
            ),
        ])

        code = main([
            "check",
            "--dbc", str(dbc_file),
            "--checks", str(checks_file),
            "--json",
            str(asc_file),
        ])
        assert code == 1
        out = capsys.readouterr().out
        data = json.loads(out)
        assert data["status"] == "violations"
        assert data["total_violations"] >= 1
        assert len(data["violations"]) >= 1
        v = data["violations"][0]
        assert v["check_name"] == "Speed limit"
        assert v["severity"] == "critical"

    def test_missing_log_file(
        self,
        dbc_file: Path,
        checks_file: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        code = main([
            "check",
            "--dbc", str(dbc_file),
            "--checks", str(checks_file),
            "/nonexistent/drive.asc",
        ])
        assert code == 2

    def test_no_checks_specified(
        self,
        dbc_file: Path,
        tmp_path: Path,
    ) -> None:
        asc_file = tmp_path / "empty.asc"
        _write_asc(asc_file, [])
        code = main([
            "check",
            "--dbc", str(dbc_file),
            str(asc_file),
        ])
        assert code == 2


# ============================================================================
# Error cases
# ============================================================================

class TestErrorCases:
    """Test error handling and exit codes."""

    def test_no_subcommand(self) -> None:
        code = main([])
        assert code == 2

    def test_unknown_subcommand(self) -> None:
        code = main(["unknown"])
        assert code == 2

    def test_check_missing_dbc(self, tmp_path: Path) -> None:
        asc = tmp_path / "test.asc"
        asc.touch()
        checks = tmp_path / "checks.yaml"
        checks.write_text(_CHECKS_YAML)
        code = main(["check", "--checks", str(checks), str(asc)])
        assert code == 2
