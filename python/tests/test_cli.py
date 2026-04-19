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
    path.write_text(_DBC_HEADER + "\n".join(messages), encoding="utf-8")


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
        """Verify contiguous hex."""
        result = parse_hex_data("401F7D0000000000")
        assert result == bytearray([0x40, 0x1F, 0x7D, 0x00, 0x00, 0x00, 0x00, 0x00])

    def test_space_separated(self) -> None:
        """Verify space separated."""
        result = parse_hex_data("40 1F 7D 00 00 00 00 00")
        assert result == bytearray([0x40, 0x1F, 0x7D, 0x00, 0x00, 0x00, 0x00, 0x00])

    def test_colon_separated(self) -> None:
        """Verify colon separated."""
        result = parse_hex_data("40:1F:7D:00:00:00:00:00")
        assert result == bytearray([0x40, 0x1F, 0x7D, 0x00, 0x00, 0x00, 0x00, 0x00])

    def test_with_0x_prefix(self) -> None:
        """Verify with 0x prefix."""
        result = parse_hex_data("0x401F7D0000000000")
        assert result == bytearray([0x40, 0x1F, 0x7D, 0x00, 0x00, 0x00, 0x00, 0x00])

    def test_lowercase(self) -> None:
        """Verify lowercase."""
        result = parse_hex_data("deadbeef")
        assert result == bytearray([0xDE, 0xAD, 0xBE, 0xEF])

    def test_empty_string(self) -> None:
        """Verify empty string."""
        result = parse_hex_data("")
        assert result == bytearray()

    def test_odd_length_raises(self) -> None:
        """Verify odd length raises."""
        with pytest.raises(ValueError, match="odd number"):
            parse_hex_data("ABC")

    def test_invalid_hex_raises(self) -> None:
        """Verify invalid hex raises."""
        with pytest.raises(ValueError, match="Invalid hex data"):
            parse_hex_data("ZZZZ")


# ============================================================================
# CAN ID parsing
# ============================================================================

class TestParseCanId:
    """Test parse_can_id: hex/decimal parsing, error cases."""

    def test_hex_id(self) -> None:
        """Verify hex id."""
        assert parse_can_id("0x100") == 256

    def test_hex_uppercase(self) -> None:
        """Verify hex uppercase."""
        assert parse_can_id("0X1FF") == 511

    def test_decimal_id(self) -> None:
        """Verify decimal id."""
        assert parse_can_id("256") == 256

    def test_zero(self) -> None:
        """Verify zero."""
        assert parse_can_id("0") == 0

    def test_whitespace_stripped(self) -> None:
        """Verify whitespace stripped."""
        assert parse_can_id("  0x100  ") == 256

    def test_invalid_raises(self) -> None:
        """Verify invalid raises."""
        with pytest.raises(ValueError, match="Invalid CAN ID"):
            parse_can_id("not_a_number")


# ============================================================================
# Timestamp formatting
# ============================================================================

class TestFormatTimestamp:
    """Test format_timestamp: microseconds -> human-readable string."""

    def test_zero(self) -> None:
        """Verify zero."""
        assert format_timestamp(0) == "0.000ms"

    def test_milliseconds(self) -> None:
        """Verify milliseconds."""
        assert format_timestamp(1234500) == "1234.500ms"

    def test_exact_ms(self) -> None:
        """Verify exact ms."""
        assert format_timestamp(1000) == "1.000ms"

    def test_sub_millisecond(self) -> None:
        """Verify sub millisecond."""
        assert format_timestamp(500) == "0.500ms"


# ============================================================================
# Rational number conversion
# ============================================================================

class TestRationalToInt:
    """Test rational_to_int: {numerator, denominator} -> int."""

    def test_simple(self) -> None:
        """Verify simple."""
        assert rational_to_int({"numerator": 0, "denominator": 1}) == 0

    def test_integer_value(self) -> None:
        """Verify integer value."""
        assert rational_to_int({"numerator": 42, "denominator": 1}) == 42

    def test_floor_division(self) -> None:
        """Verify floor division."""
        assert rational_to_int({"numerator": 7, "denominator": 2}) == 3

    def test_large_value(self) -> None:
        """Verify large value."""
        assert rational_to_int({"numerator": 1234500, "denominator": 1}) == 1234500

    def test_zero_denominator_raises(self) -> None:
        """Verify zero denominator raises."""
        with pytest.raises(ValueError, match="denominator is zero"):
            rational_to_int({"numerator": 42, "denominator": 0})


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
        """Verify text output."""
        code = main(["signals", "--dbc", str(dbc_file)])
        assert code == 0
        out = capsys.readouterr().out
        assert "EngineStatus" in out
        assert "EngineSpeed" in out
        assert "BrakePressure" in out
        assert "2 messages, 3 signals" in out

    def test_json_output(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        """Verify json output."""
        code = main(["signals", "--dbc", str(dbc_file), "--json"])
        assert code == 0
        out = capsys.readouterr().out
        data = json.loads(out)
        assert "messages" in data
        assert len(data["messages"]) == 2

    def test_missing_dbc_file(self) -> None:
        """Verify missing dbc file."""
        code = main(["signals", "--dbc", "/nonexistent/file.dbc"])
        assert code == 2

    def test_no_dbc_specified(self) -> None:
        """Verify no dbc specified."""
        code = main(["signals"])
        assert code == 2


# ============================================================================
# Extract subcommand (requires FFI)
# ============================================================================

class TestExtractCommand:
    """Test 'aletheia extract' -- requires FFI shared library."""

    @pytest.fixture()
    def dbc_file(self, tmp_path: Path) -> Path:
        """Write a DBC fixture and return its path."""
        p = tmp_path / "test.dbc"
        _write_dbc(p, _DBC_ENGINE_MSG)
        return p

    def test_text_output(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        # EngineSpeed at bits 0:16 LE unsigned, factor=0.25, offset=0
        # Raw value 0x0320 = 800, physical = 800 * 0.25 = 200.0 rpm
        """Verify text output."""
        code = main(["extract", "--dbc", str(dbc_file), "0x100", "2003000000000000"])
        assert code == 0
        out = capsys.readouterr().out
        assert "EngineStatus" in out
        assert "EngineSpeed" in out
        assert "Errors: none" in out

    def test_json_output(self, dbc_file: Path, capsys: pytest.CaptureFixture[str]) -> None:
        """Verify json output."""
        code = main(["extract", "--dbc", str(dbc_file), "0x100", "2003000000000000", "--json"])
        assert code == 0
        out = capsys.readouterr().out
        data = json.loads(out)
        assert data["can_id"] == 0x100
        assert "values" in data
        assert "EngineSpeed" in data["values"]

    def test_decimal_can_id(self, dbc_file: Path) -> None:
        """Verify decimal can id."""
        code = main(["extract", "--dbc", str(dbc_file), "256", "0000000000000000"])
        assert code == 0

    def test_space_separated_data(self, dbc_file: Path) -> None:
        """Verify space separated data."""
        code = main(["extract", "--dbc", str(dbc_file), "0x100", "20 03 00 00 00 00 00 00"])
        assert code == 0

    def test_wrong_data_length(self, dbc_file: Path) -> None:
        """Verify wrong data length."""
        code = main(["extract", "--dbc", str(dbc_file), "0x100", "AABB"])
        assert code == 2

    def test_missing_dbc(self) -> None:
        """Verify missing dbc."""
        code = main(["extract", "--dbc", "/nonexistent.dbc", "0x100", "0000000000000000"])
        assert code == 2


# ============================================================================
# Check subcommand (requires FFI)
# ============================================================================

class TestCheckCommand:
    """Test 'aletheia check' -- requires FFI shared library."""

    @pytest.fixture()
    def dbc_file(self, tmp_path: Path) -> Path:
        """Write a DBC fixture and return its path."""
        p = tmp_path / "test.dbc"
        _write_dbc(p, _DBC_ENGINE_MSG)
        return p

    @pytest.fixture()
    def checks_file(self, tmp_path: Path) -> Path:
        """Write a checks YAML fixture and return its path."""
        p = tmp_path / "checks.yaml"
        p.write_text(_CHECKS_YAML, encoding="utf-8")
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
        """Violation detected -- exit code 1, enriched reason in text output."""
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
        assert "violation" in out.lower()
        assert "EngineSpeed" in out
        assert "1000" in out

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
        assert "EngineSpeed" in v["reason"]
        assert "1000" in v["reason"]

    def test_missing_log_file(
        self,
        dbc_file: Path,
        checks_file: Path,
    ) -> None:
        """Verify missing log file."""
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
        """Verify no checks specified."""
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
        """Verify no subcommand."""
        code = main([])
        assert code == 2

    def test_unknown_subcommand(self) -> None:
        """Verify unknown subcommand."""
        code = main(["unknown"])
        assert code == 2

    def test_check_missing_dbc(self, tmp_path: Path) -> None:
        """Verify check missing dbc."""
        asc = tmp_path / "test.asc"
        asc.touch()
        checks = tmp_path / "checks.yaml"
        checks.write_text(_CHECKS_YAML, encoding="utf-8")
        code = main(["check", "--checks", str(checks), str(asc)])
        assert code == 2


# ============================================================================
# mux-query subcommand
# ============================================================================

_DBC_MUX_MSG = (
    "BO_ 768 DiagStatus: 8 ECU1\n"
    + ' SG_ Mode M : 0|8@1+ (1,0) [0|255] "" Vector__XXX\n'
    + ' SG_ Always1 : 56|8@1+ (1,0) [0|255] "" Vector__XXX\n'
    + ' SG_ RpmMux m0 : 8|16@1+ (1,0) [0|65535] "rpm" Vector__XXX\n'
    + ' SG_ TempMux m1 : 8|16@1+ (1,-40) [-40|215] "celsius" Vector__XXX\n'
)


class TestMuxQueryCommand:
    """Test 'aletheia mux-query' -- pure DBC traversal, no FFI needed."""

    @pytest.fixture()
    def dbc_file(self, tmp_path: Path) -> Path:
        """Create a .dbc file with one multiplexed and one plain message."""
        p = tmp_path / "mux.dbc"
        _write_dbc(p, _DBC_ENGINE_MSG, _DBC_MUX_MSG)
        return p

    def test_summary_text_plain_message(
        self, dbc_file: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Verify summary text plain message."""
        code = main(["mux-query", "--dbc", str(dbc_file), "0x100"])
        assert code == 0
        out = capsys.readouterr().out
        assert "EngineStatus" in out
        assert "Not multiplexed" in out

    def test_summary_text_multiplexed(
        self, dbc_file: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Verify summary text multiplexed."""
        code = main(["mux-query", "--dbc", str(dbc_file), "0x300"])
        assert code == 0
        out = capsys.readouterr().out
        assert "DiagStatus" in out
        assert "Multiplexors: Mode" in out
        assert "value 0" in out
        assert "RpmMux" in out
        assert "value 1" in out
        assert "TempMux" in out

    def test_summary_json(
        self, dbc_file: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Verify summary json."""
        code = main(["mux-query", "--dbc", str(dbc_file), "0x300", "--json"])
        assert code == 0
        data = json.loads(capsys.readouterr().out)
        assert data["message_id"] == 0x300
        assert data["message_name"] == "DiagStatus"
        assert data["is_multiplexed"] is True
        mux_names = [m["name"] for m in data["multiplexors"]]
        assert mux_names == ["Mode"]
        values = {v["value"]: v["signals"] for v in data["multiplexors"][0]["values"]}
        assert set(values.keys()) == {0, 1}
        assert "RpmMux" in values[0]
        assert "TempMux" in values[1]

    def test_selection_by_mux_and_value_text(
        self, dbc_file: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Verify selection by mux and value text."""
        code = main([
            "mux-query", "--dbc", str(dbc_file), "0x300",
            "--mux", "Mode", "--value", "0",
        ])
        assert code == 0
        out = capsys.readouterr().out
        assert "Mode = 0" in out
        assert "RpmMux" in out
        assert "Always1" in out
        assert "TempMux" not in out

    def test_selection_by_mux_and_value_json(
        self, dbc_file: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Verify selection by mux and value json."""
        code = main([
            "mux-query", "--dbc", str(dbc_file), "0x300",
            "--mux", "Mode", "--value", "1", "--json",
        ])
        assert code == 0
        data = json.loads(capsys.readouterr().out)
        assert data["multiplexor"] == "Mode"
        assert data["value"] == 1
        assert "TempMux" in data["signals"]
        assert "Always1" in data["signals"]
        assert "RpmMux" not in data["signals"]

    def test_message_by_name(
        self, dbc_file: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Verify message by name."""
        code = main(["mux-query", "--dbc", str(dbc_file), "DiagStatus"])
        assert code == 0
        out = capsys.readouterr().out
        assert "DiagStatus" in out
        assert "Multiplexors: Mode" in out

    def test_unknown_message(self, dbc_file: Path) -> None:
        """Verify unknown message."""
        code = main(["mux-query", "--dbc", str(dbc_file), "0x999"])
        assert code == 2

    def test_unknown_message_name(self, dbc_file: Path) -> None:
        """Verify unknown message name."""
        code = main(["mux-query", "--dbc", str(dbc_file), "NoSuchMessage"])
        assert code == 2

    def test_unknown_multiplexor(self, dbc_file: Path) -> None:
        """Verify unknown multiplexor."""
        code = main([
            "mux-query", "--dbc", str(dbc_file), "0x300",
            "--mux", "NoSuch", "--value", "0",
        ])
        assert code == 2

    def test_mux_without_value_rejected(self, dbc_file: Path) -> None:
        """Verify mux without value rejected."""
        code = main([
            "mux-query", "--dbc", str(dbc_file), "0x300", "--mux", "Mode",
        ])
        assert code == 2

    def test_value_without_mux_rejected(self, dbc_file: Path) -> None:
        """Verify value without mux rejected."""
        code = main([
            "mux-query", "--dbc", str(dbc_file), "0x300", "--value", "0",
        ])
        assert code == 2


# ============================================================================
# format-dbc subcommand
# ============================================================================

class TestFormatDBCCommand:
    """Test 'aletheia format-dbc' -- DBC roundtrip through the Agda core."""

    @pytest.fixture()
    def dbc_file(self, tmp_path: Path) -> Path:
        """Create a .dbc file with one message."""
        p = tmp_path / "format.dbc"
        _write_dbc(p, _DBC_ENGINE_MSG)
        return p

    def test_json_roundtrip(
        self, dbc_file: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The canonical JSON mirrors the input DBC and is valid JSON."""
        code = main(["format-dbc", "--dbc", str(dbc_file)])
        assert code == 0
        out = capsys.readouterr().out
        data = json.loads(out)
        assert "messages" in data
        msg_names = {m["name"] for m in data["messages"]}
        assert "EngineStatus" in msg_names

    def test_missing_dbc_file(self, capsys: pytest.CaptureFixture[str]) -> None:
        """Non-existent --dbc argument fails fast with exit 2."""
        code = main(["format-dbc", "--dbc", "/nonexistent/file.dbc"])
        assert code == 2
        err = capsys.readouterr().err
        assert "not found" in err or "Error" in err

    def test_no_source_specified(self, capsys: pytest.CaptureFixture[str]) -> None:
        """Neither --dbc nor --excel: fail fast."""
        code = main(["format-dbc"])
        assert code == 2
        err = capsys.readouterr().err
        assert "DBC source" in err or "Error" in err
