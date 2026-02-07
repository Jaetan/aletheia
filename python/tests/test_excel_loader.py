"""Unit tests for the Excel loader

Tests cover:
- Simple checks: each condition type loaded from Excel rows
- When/Then checks: all trigger/response combinations
- Metadata: name and severity from cells
- DBC loading: parse DBC sheet, message grouping, hex IDs
- Template creation: sheet names, headers, no-overwrite
- Error handling: invalid conditions, missing cells, bad message IDs
- File round-trip: write temp .xlsx, load it, verify
- Equivalence: Excel-loaded checks produce same formula as Check API
"""

from pathlib import Path

import pytest
import openpyxl  # type: ignore[import-untyped]
from openpyxl.workbook import Workbook  # type: ignore[import-untyped]

from aletheia.checks import Check
from aletheia.excel_loader import (
    create_template,
    load_checks_from_excel,
    load_dbc_from_excel,
)


# ============================================================================
# Test helper
# ============================================================================

_CHECKS_HEADERS = [
    "Check Name", "Signal", "Condition", "Value", "Min", "Max",
    "Time (ms)", "Severity",
]

_WHEN_THEN_HEADERS = [
    "Check Name", "When Signal", "When Condition", "When Value",
    "Then Signal", "Then Condition", "Then Value", "Then Min", "Then Max",
    "Within (ms)", "Severity",
]

_DBC_HEADERS = [
    "Message ID", "Message Name", "DLC", "Signal", "Start Bit", "Length",
    "Byte Order", "Signed", "Factor", "Offset", "Min", "Max", "Unit",
    "Multiplexor", "Multiplex Value",
]


def _make_checks_workbook(
    tmp_path: Path,
    rows: list[list[object]],
    filename: str = "test.xlsx",
) -> Path:
    """Shortcut: workbook with only a Checks sheet."""
    wb = Workbook()
    ws = wb.active
    ws.title = "Checks"  # type: ignore[union-attr]
    ws.append(_CHECKS_HEADERS)  # type: ignore[union-attr]
    for row in rows:
        ws.append(row)  # type: ignore[union-attr]
    p = tmp_path / filename
    wb.save(str(p))
    return p


def _make_when_then_workbook(
    tmp_path: Path,
    rows: list[list[object]],
    filename: str = "test.xlsx",
) -> Path:
    """Shortcut: workbook with only a When-Then sheet."""
    wb = Workbook()
    ws = wb.active
    ws.title = "When-Then"  # type: ignore[union-attr]
    ws.append(_WHEN_THEN_HEADERS)  # type: ignore[union-attr]
    for row in rows:
        ws.append(row)  # type: ignore[union-attr]
    p = tmp_path / filename
    wb.save(str(p))
    return p


def _make_dbc_workbook(
    tmp_path: Path,
    rows: list[list[object]],
    filename: str = "test.xlsx",
) -> Path:
    """Shortcut: workbook with only a DBC sheet."""
    wb = Workbook()
    ws = wb.active
    ws.title = "DBC"  # type: ignore[union-attr]
    ws.append(_DBC_HEADERS)  # type: ignore[union-attr]
    for row in rows:
        ws.append(row)  # type: ignore[union-attr]
    p = tmp_path / filename
    wb.save(str(p))
    return p


# ============================================================================
# Simple checks — each condition type
# ============================================================================

class TestLoadSimpleChecks:
    """Load each simple condition from Excel rows and verify formula."""

    def test_never_exceeds(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Speed", "never_exceeds", 220, None, None, None, None],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("Speed").never_exceeds(220).to_dict()

    def test_never_below(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Voltage", "never_below", 11.5, None, None, None, None],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("Voltage").never_below(11.5).to_dict()

    def test_stays_between(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Voltage", "stays_between", None, 11.5, 14.5, None, None],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 1
        assert checks[0].to_dict() == (
            Check.signal("Voltage").stays_between(11.5, 14.5).to_dict()
        )

    def test_never_equals(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "ErrorCode", "never_equals", 255, None, None, None, None],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("ErrorCode").never_equals(255).to_dict()

    def test_equals_always(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Gear", "equals", 0, None, None, None, None],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("Gear").equals(0).always().to_dict()

    def test_settles_between(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "CoolantTemp", "settles_between", None, 80, 100, 5000, None],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 1
        assert checks[0].to_dict() == (
            Check.signal("CoolantTemp").settles_between(80, 100).within(5000).to_dict()
        )

    def test_multiple_checks(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Speed", "never_exceeds", 220, None, None, None, None],
            [None, "Voltage", "stays_between", None, 11.5, 14.5, None, None],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 2
        assert checks[0].to_dict() == Check.signal("Speed").never_exceeds(220).to_dict()
        assert checks[1].to_dict() == (
            Check.signal("Voltage").stays_between(11.5, 14.5).to_dict()
        )


# ============================================================================
# When/Then checks
# ============================================================================

class TestLoadWhenThenChecks:
    """Load when/then causal checks from Excel rows."""

    def test_when_exceeds_then_equals(self, tmp_path: Path) -> None:
        p = _make_when_then_workbook(tmp_path, [
            # name, when_sig, when_cond, when_val, then_sig, then_cond, then_val, then_min, then_max, within, sev
            ["Brake response", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, None, None, 100, None],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 1
        expected = (
            Check.when("BrakePedal").exceeds(50)
            .then("BrakeLight").equals(1)
            .within(100)
            .to_dict()
        )
        assert checks[0].to_dict() == expected

    def test_when_equals_then_exceeds(self, tmp_path: Path) -> None:
        p = _make_when_then_workbook(tmp_path, [
            [None, "Ignition", "equals", 1, "RPM", "exceeds", 500, None, None, 2000, None],
        ])
        checks = load_checks_from_excel(p)
        expected = (
            Check.when("Ignition").equals(1)
            .then("RPM").exceeds(500)
            .within(2000)
            .to_dict()
        )
        assert checks[0].to_dict() == expected

    def test_when_drops_below_then_stays_between(self, tmp_path: Path) -> None:
        p = _make_when_then_workbook(tmp_path, [
            [None, "FuelLevel", "drops_below", 10, "FuelWarning", "stays_between", None, 1, 1, 50, None],
        ])
        checks = load_checks_from_excel(p)
        expected = (
            Check.when("FuelLevel").drops_below(10)
            .then("FuelWarning").stays_between(1, 1)
            .within(50)
            .to_dict()
        )
        assert checks[0].to_dict() == expected


# ============================================================================
# Metadata
# ============================================================================

class TestLoadMetadata:
    """Verify name and severity are set on CheckResult from Excel cells."""

    def test_name_set(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            ["Speed limit", "Speed", "never_exceeds", 220, None, None, None, None],
        ])
        checks = load_checks_from_excel(p)
        assert checks[0].name == "Speed limit"

    def test_severity_set(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Speed", "never_exceeds", 220, None, None, None, "critical"],
        ])
        checks = load_checks_from_excel(p)
        assert checks[0].check_severity == "critical"

    def test_name_and_severity(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            ["Speed limit", "Speed", "never_exceeds", 220, None, None, None, "warning"],
        ])
        checks = load_checks_from_excel(p)
        assert checks[0].name == "Speed limit"
        assert checks[0].check_severity == "warning"

    def test_defaults_none(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Speed", "never_exceeds", 220, None, None, None, None],
        ])
        checks = load_checks_from_excel(p)
        assert checks[0].name is None
        assert checks[0].check_severity is None

    def test_when_then_metadata(self, tmp_path: Path) -> None:
        p = _make_when_then_workbook(tmp_path, [
            ["Brake response", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, None, None, 100, "safety"],
        ])
        checks = load_checks_from_excel(p)
        assert checks[0].name == "Brake response"
        assert checks[0].check_severity == "safety"


# ============================================================================
# DBC loading
# ============================================================================

class TestLoadDBCFromExcel:
    """Parse DBC sheet, verify DBCDefinition structure."""

    def test_single_signal(self, tmp_path: Path) -> None:
        p = _make_dbc_workbook(tmp_path, [
            # id, name, dlc, signal, startbit, length, byteorder, signed, factor, offset, min, max, unit
            [256, "EngineData", 8, "RPM", 0, 16, "little_endian", False, 0.25, 0, 0, 16383.75, "rpm"],
        ])
        dbc = load_dbc_from_excel(p)
        assert dbc["version"] == ""
        assert len(dbc["messages"]) == 1
        msg = dbc["messages"][0]
        assert msg["id"] == 256
        assert msg["name"] == "EngineData"
        assert msg["dlc"] == 8
        assert len(msg["signals"]) == 1
        sig = msg["signals"][0]
        assert sig["name"] == "RPM"
        assert sig["startBit"] == 0
        assert sig["length"] == 16
        assert sig["byteOrder"] == "little_endian"
        assert sig["signed"] is False
        assert sig["factor"] == 0.25
        assert sig["offset"] == 0
        assert sig["minimum"] == 0
        assert sig["maximum"] == 16383.75
        assert sig["unit"] == "rpm"
        assert sig["presence"] == "always"

    def test_message_grouping(self, tmp_path: Path) -> None:
        """Multiple rows with same message ID are grouped."""
        p = _make_dbc_workbook(tmp_path, [
            [256, "EngineData", 8, "RPM", 0, 16, "little_endian", False, 0.25, 0, 0, 16383.75, "rpm"],
            [256, "EngineData", 8, "Temp", 16, 8, "little_endian", False, 1, -40, -40, 215, "C"],
            [512, "BrakeData", 4, "BrakePressure", 0, 16, "big_endian", False, 0.1, 0, 0, 6553.5, "bar"],
        ])
        dbc = load_dbc_from_excel(p)
        assert len(dbc["messages"]) == 2
        assert dbc["messages"][0]["name"] == "EngineData"
        assert len(dbc["messages"][0]["signals"]) == 2
        assert dbc["messages"][0]["signals"][0]["name"] == "RPM"
        assert dbc["messages"][0]["signals"][1]["name"] == "Temp"
        assert dbc["messages"][1]["name"] == "BrakeData"
        assert len(dbc["messages"][1]["signals"]) == 1

    def test_hex_message_id(self, tmp_path: Path) -> None:
        """Message IDs can be hex strings."""
        p = _make_dbc_workbook(tmp_path, [
            ["0x100", "EngineData", 8, "RPM", 0, 16, "little_endian", False, 0.25, 0, 0, 16383.75, "rpm"],
        ])
        dbc = load_dbc_from_excel(p)
        assert dbc["messages"][0]["id"] == 0x100

    def test_signed_true(self, tmp_path: Path) -> None:
        p = _make_dbc_workbook(tmp_path, [
            [256, "EngineData", 8, "Temp", 0, 8, "little_endian", True, 1, -40, -40, 215, "C"],
        ])
        dbc = load_dbc_from_excel(p)
        assert dbc["messages"][0]["signals"][0]["signed"] is True

    def test_missing_unit_defaults_empty(self, tmp_path: Path) -> None:
        p = _make_dbc_workbook(tmp_path, [
            [256, "EngineData", 8, "RPM", 0, 16, "little_endian", False, 0.25, 0, 0, 16383.75, None],
        ])
        dbc = load_dbc_from_excel(p)
        assert dbc["messages"][0]["signals"][0]["unit"] == ""


# ============================================================================
# Multiplexed signals in DBC
# ============================================================================

class TestLoadDBCMultiplexed:
    """Multiplexed signal support via optional Multiplexor/Multiplex Value columns."""

    def test_multiplexed_signal(self, tmp_path: Path) -> None:
        """Signal with both Multiplexor and Multiplex Value produces DBCSignalMultiplexed."""
        p = _make_dbc_workbook(tmp_path, [
            [256, "Msg", 8, "MuxSignal", 8, 8, "little_endian", False, 1, 0, 0, 255, "", "Selector", 3],
        ])
        dbc = load_dbc_from_excel(p)
        sig = dbc["messages"][0]["signals"][0]
        assert "multiplexor" in sig
        assert sig["multiplexor"] == "Selector"
        assert sig["multiplex_value"] == 3
        assert "presence" not in sig

    def test_always_signal_no_mux_columns(self, tmp_path: Path) -> None:
        """Signal without Multiplexor/Multiplex Value columns is always-present."""
        p = _make_dbc_workbook(tmp_path, [
            [256, "Msg", 8, "Sig", 0, 16, "little_endian", False, 1, 0, 0, 100, "", None, None],
        ])
        dbc = load_dbc_from_excel(p)
        sig = dbc["messages"][0]["signals"][0]
        assert sig["presence"] == "always"
        assert "multiplexor" not in sig

    def test_mixed_always_and_multiplexed(self, tmp_path: Path) -> None:
        """Same message can have both always-present and multiplexed signals."""
        p = _make_dbc_workbook(tmp_path, [
            [256, "Msg", 8, "Selector", 0, 8, "little_endian", False, 1, 0, 0, 255, "", None, None],
            [256, "Msg", 8, "TempA", 8, 8, "little_endian", False, 1, -40, -40, 215, "C", "Selector", 0],
            [256, "Msg", 8, "TempB", 8, 8, "little_endian", False, 1, -40, -40, 215, "C", "Selector", 1],
        ])
        dbc = load_dbc_from_excel(p)
        msg = dbc["messages"][0]
        assert len(msg["signals"]) == 3
        assert msg["signals"][0]["presence"] == "always"
        assert msg["signals"][1]["multiplexor"] == "Selector"
        assert msg["signals"][1]["multiplex_value"] == 0
        assert msg["signals"][2]["multiplexor"] == "Selector"
        assert msg["signals"][2]["multiplex_value"] == 1

    def test_partial_mux_raises(self, tmp_path: Path) -> None:
        """Only Multiplexor without Multiplex Value raises ValueError."""
        p = _make_dbc_workbook(tmp_path, [
            [256, "Msg", 8, "Sig", 0, 16, "little_endian", False, 1, 0, 0, 100, "", "Selector", None],
        ])
        with pytest.raises(ValueError, match="must both be provided or both be empty"):
            load_dbc_from_excel(p)

    def test_partial_mux_value_only_raises(self, tmp_path: Path) -> None:
        """Only Multiplex Value without Multiplexor raises ValueError."""
        p = _make_dbc_workbook(tmp_path, [
            [256, "Msg", 8, "Sig", 0, 16, "little_endian", False, 1, 0, 0, 100, "", None, 3],
        ])
        with pytest.raises(ValueError, match="must both be provided or both be empty"):
            load_dbc_from_excel(p)


# ============================================================================
# Template creation
# ============================================================================

class TestCreateTemplate:
    """Verify create_template() creates a correct workbook."""

    def test_creates_file(self, tmp_path: Path) -> None:
        p = tmp_path / "template.xlsx"
        create_template(p)
        assert p.exists()

    def test_sheet_names(self, tmp_path: Path) -> None:
        p = tmp_path / "template.xlsx"
        create_template(p)
        wb = openpyxl.load_workbook(p)
        assert wb.sheetnames == ["DBC", "Checks", "When-Then"]
        wb.close()

    def test_dbc_headers(self, tmp_path: Path) -> None:
        p = tmp_path / "template.xlsx"
        create_template(p)
        wb = openpyxl.load_workbook(p)
        ws = wb["DBC"]
        headers = [cell.value for cell in ws[1]]
        assert headers == _DBC_HEADERS
        wb.close()

    def test_checks_headers(self, tmp_path: Path) -> None:
        p = tmp_path / "template.xlsx"
        create_template(p)
        wb = openpyxl.load_workbook(p)
        ws = wb["Checks"]
        headers = [cell.value for cell in ws[1]]
        assert headers == _CHECKS_HEADERS
        wb.close()

    def test_when_then_headers(self, tmp_path: Path) -> None:
        p = tmp_path / "template.xlsx"
        create_template(p)
        wb = openpyxl.load_workbook(p)
        ws = wb["When-Then"]
        headers = [cell.value for cell in ws[1]]
        assert headers == _WHEN_THEN_HEADERS
        wb.close()

    def test_headers_bold(self, tmp_path: Path) -> None:
        p = tmp_path / "template.xlsx"
        create_template(p)
        wb = openpyxl.load_workbook(p)
        ws = wb["DBC"]
        for cell in ws[1]:
            assert cell.font.bold is True
        wb.close()

    def test_no_overwrite(self, tmp_path: Path) -> None:
        p = tmp_path / "template.xlsx"
        create_template(p)
        with pytest.raises(FileExistsError, match="File already exists"):
            create_template(p)


# ============================================================================
# Error handling
# ============================================================================

class TestLoadErrors:
    """All validation error cases raise ValueError or FileNotFoundError."""

    def test_file_not_found(self) -> None:
        with pytest.raises(FileNotFoundError, match="Excel file not found"):
            load_checks_from_excel("/nonexistent/path/checks.xlsx")

    def test_dbc_file_not_found(self) -> None:
        with pytest.raises(FileNotFoundError, match="Excel file not found"):
            load_dbc_from_excel("/nonexistent/path/dbc.xlsx")

    def test_no_checks_or_when_then_sheet(self, tmp_path: Path) -> None:
        """Workbook with neither Checks nor When-Then raises ValueError."""
        wb = Workbook()
        ws = wb.active
        ws.title = "Other"  # type: ignore[union-attr]
        p = tmp_path / "bad.xlsx"
        wb.save(str(p))
        with pytest.raises(ValueError, match="no 'Checks' or 'When-Then' sheet"):
            load_checks_from_excel(p)

    def test_no_dbc_sheet(self, tmp_path: Path) -> None:
        wb = Workbook()
        ws = wb.active
        ws.title = "Other"  # type: ignore[union-attr]
        p = tmp_path / "bad.xlsx"
        wb.save(str(p))
        with pytest.raises(ValueError, match="no 'DBC' sheet"):
            load_dbc_from_excel(p)

    def test_unknown_simple_condition(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Speed", "bogus", 100, None, None, None, None],
        ])
        with pytest.raises(ValueError, match="unknown condition 'bogus'"):
            load_checks_from_excel(p)

    def test_missing_value_for_never_exceeds(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Speed", "never_exceeds", None, None, None, None, None],
        ])
        with pytest.raises(ValueError, match="missing or invalid 'Value'"):
            load_checks_from_excel(p)

    def test_stays_between_missing_min(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Voltage", "stays_between", None, None, 14.5, None, None],
        ])
        with pytest.raises(ValueError, match="requires 'Min' and 'Max'"):
            load_checks_from_excel(p)

    def test_settles_between_missing_time(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            [None, "Temp", "settles_between", None, 80, 100, None, None],
        ])
        with pytest.raises(ValueError, match="requires 'Time \\(ms\\)'"):
            load_checks_from_excel(p)

    def test_unknown_when_condition(self, tmp_path: Path) -> None:
        p = _make_when_then_workbook(tmp_path, [
            [None, "Brake", "bogus", 50, "BrakeLight", "equals", 1, None, None, 100, None],
        ])
        with pytest.raises(ValueError, match="unknown when condition 'bogus'"):
            load_checks_from_excel(p)

    def test_unknown_then_condition(self, tmp_path: Path) -> None:
        p = _make_when_then_workbook(tmp_path, [
            [None, "Brake", "exceeds", 50, "BrakeLight", "bogus", 1, None, None, 100, None],
        ])
        with pytest.raises(ValueError, match="unknown then condition 'bogus'"):
            load_checks_from_excel(p)

    def test_invalid_byte_order(self, tmp_path: Path) -> None:
        p = _make_dbc_workbook(tmp_path, [
            [256, "Msg", 8, "Sig", 0, 16, "mixed_endian", False, 1, 0, 0, 100, ""],
        ])
        with pytest.raises(ValueError, match="Byte Order"):
            load_dbc_from_excel(p)

    def test_invalid_message_id(self, tmp_path: Path) -> None:
        p = _make_dbc_workbook(tmp_path, [
            ["not_a_number", "Msg", 8, "Sig", 0, 16, "little_endian", False, 1, 0, 0, 100, ""],
        ])
        with pytest.raises(ValueError, match="invalid 'Message ID'"):
            load_dbc_from_excel(p)

    def test_dbc_empty_data(self, tmp_path: Path) -> None:
        """DBC sheet with only header row raises ValueError."""
        wb = Workbook()
        ws = wb.active
        ws.title = "DBC"  # type: ignore[union-attr]
        ws.append(_DBC_HEADERS)  # type: ignore[union-attr]
        p = tmp_path / "empty.xlsx"
        wb.save(str(p))
        with pytest.raises(ValueError, match="at least one data row"):
            load_dbc_from_excel(p)


# ============================================================================
# File round-trip
# ============================================================================

class TestLoadFromFile:
    """Write temp .xlsx, load it, verify round-trip."""

    def test_checks_round_trip(self, tmp_path: Path) -> None:
        p = _make_checks_workbook(tmp_path, [
            ["Speed limit", "Speed", "never_exceeds", 220, None, None, None, "critical"],
        ])
        checks = load_checks_from_excel(p)
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("Speed").never_exceeds(220).to_dict()
        assert checks[0].name == "Speed limit"
        assert checks[0].check_severity == "critical"

    def test_combined_checks_and_when_then(self, tmp_path: Path) -> None:
        """Workbook with both Checks and When-Then sheets."""
        wb = Workbook()
        ws_checks = wb.active
        ws_checks.title = "Checks"  # type: ignore[union-attr]
        ws_checks.append(_CHECKS_HEADERS)  # type: ignore[union-attr]
        ws_checks.append([None, "Speed", "never_exceeds", 220, None, None, None, None])  # type: ignore[union-attr]

        ws_wt = wb.create_sheet("When-Then")
        ws_wt.append(_WHEN_THEN_HEADERS)
        ws_wt.append([None, "Brake", "exceeds", 50, "BrakeLight", "equals", 1, None, None, 100, None])

        p = tmp_path / "combined.xlsx"
        wb.save(str(p))

        checks = load_checks_from_excel(p)
        assert len(checks) == 2
        # First is the simple check, second is the when/then
        assert checks[0].to_dict() == Check.signal("Speed").never_exceeds(220).to_dict()
        expected_wt = (
            Check.when("Brake").exceeds(50)
            .then("BrakeLight").equals(1)
            .within(100)
            .to_dict()
        )
        assert checks[1].to_dict() == expected_wt

    def test_dbc_round_trip(self, tmp_path: Path) -> None:
        p = _make_dbc_workbook(tmp_path, [
            [256, "EngineData", 8, "RPM", 0, 16, "little_endian", False, 0.25, 0, 0, 16383.75, "rpm"],
            [256, "EngineData", 8, "Temp", 16, 8, "little_endian", False, 1, -40, -40, 215, "C"],
        ])
        dbc = load_dbc_from_excel(p)
        assert len(dbc["messages"]) == 1
        msg = dbc["messages"][0]
        assert msg["id"] == 256
        assert len(msg["signals"]) == 2
        assert msg["signals"][0]["name"] == "RPM"
        assert msg["signals"][1]["name"] == "Temp"


# ============================================================================
# Skips empty rows
# ============================================================================

class TestEmptyRows:
    """Empty rows in the middle of data are skipped."""

    def test_empty_row_skipped_in_checks(self, tmp_path: Path) -> None:
        wb = Workbook()
        ws = wb.active
        ws.title = "Checks"  # type: ignore[union-attr]
        ws.append(_CHECKS_HEADERS)  # type: ignore[union-attr]
        ws.append([None, "Speed", "never_exceeds", 220, None, None, None, None])  # type: ignore[union-attr]
        ws.append([None, None, None, None, None, None, None, None])  # empty row  # type: ignore[union-attr]
        ws.append([None, "Voltage", "never_below", 11.5, None, None, None, None])  # type: ignore[union-attr]
        p = tmp_path / "gaps.xlsx"
        wb.save(str(p))
        checks = load_checks_from_excel(p)
        assert len(checks) == 2
