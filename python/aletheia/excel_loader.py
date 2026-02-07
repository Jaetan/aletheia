"""Excel loader for CAN signal checks and DBC definitions

Loads check definitions and DBC signal tables from Excel workbooks
(.xlsx) and compiles them through the Check API into LTL properties.

Designed for automotive technicians who define checks in spreadsheet
templates — no code, no YAML, just fill in cells.

Usage:
    from aletheia import load_checks_from_excel, load_dbc_from_excel

    # Load signal checks
    checks = load_checks_from_excel("my_checks.xlsx")
    client.set_properties([c.to_dict() for c in checks])

    # Load DBC definition
    dbc = load_dbc_from_excel("my_dbc.xlsx")
    client.parse_dbc(dbc)

    # Create a blank template for technicians
    create_template("template.xlsx")

Excel Template Layout
=====================

The workbook has three sheets:

**DBC** — one row per signal::

    Message ID | Message Name | DLC | Signal | Start Bit | Length |
    Byte Order | Signed | Factor | Offset | Min | Max | Unit |
    Multiplexor | Multiplex Value

Multiplexor and Multiplex Value are optional. If both are filled in, the
signal is multiplexed; if both are empty, the signal is always-present.

**Checks** — one row per simple check::

    Check Name | Signal | Condition | Value | Min | Max | Time (ms) | Severity

**When-Then** — one row per causal check::

    Check Name | When Signal | When Condition | When Value |
    Then Signal | Then Condition | Then Value | Then Min | Then Max |
    Within (ms) | Severity
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import TypeAlias, TypeGuard

import openpyxl
from openpyxl.styles import Font
from openpyxl.workbook import Workbook
from openpyxl.worksheet.worksheet import Worksheet

from .checks import Check, CheckResult
from .protocols import (
    DBCDefinition,
    DBCMessage,
    DBCSignal,
    DBCSignalAlways,
    DBCSignalMultiplexed,
)

# Excel cell values: str, numbers, booleans, or None (empty)
CellValue: TypeAlias = str | int | float | bool | None

# A row of cell values as returned by openpyxl iter_rows(values_only=True)
ExcelRow: TypeAlias = tuple[CellValue, ...]


@dataclass(frozen=True)
class _MessageKey:
    """Grouping key for DBC message rows."""

    msg_id: int
    name: str
    dlc: int


# ============================================================================
# Condition constants (shared with yaml_loader.py by design — kept local)
# ============================================================================

_SIMPLE_VALUE_CONDITIONS = frozenset({
    "never_exceeds", "never_below", "never_equals",
})
_SIMPLE_RANGE_CONDITIONS = frozenset({
    "stays_between",
})
_SIMPLE_SETTLES_CONDITIONS = frozenset({
    "settles_between",
})
_SIMPLE_EQUALS_CONDITIONS = frozenset({
    "equals",
})
_ALL_SIMPLE_CONDITIONS = (
    _SIMPLE_VALUE_CONDITIONS
    | _SIMPLE_RANGE_CONDITIONS
    | _SIMPLE_SETTLES_CONDITIONS
    | _SIMPLE_EQUALS_CONDITIONS
)

_WHEN_CONDITIONS = frozenset({"exceeds", "equals", "drops_below"})
_THEN_VALUE_CONDITIONS = frozenset({"equals", "exceeds"})
_THEN_RANGE_CONDITIONS = frozenset({"stays_between"})
_ALL_THEN_CONDITIONS = _THEN_VALUE_CONDITIONS | _THEN_RANGE_CONDITIONS


# ============================================================================
# Sheet headers
# ============================================================================

_DBC_HEADERS = [
    "Message ID", "Message Name", "DLC", "Signal", "Start Bit", "Length",
    "Byte Order", "Signed", "Factor", "Offset", "Min", "Max", "Unit",
    "Multiplexor", "Multiplex Value",
]

_CHECKS_HEADERS = [
    "Check Name", "Signal", "Condition", "Value", "Min", "Max",
    "Time (ms)", "Severity",
]

_WHEN_THEN_HEADERS = [
    "Check Name", "When Signal", "When Condition", "When Value",
    "Then Signal", "Then Condition", "Then Value", "Then Min", "Then Max",
    "Within (ms)", "Severity",
]


# ============================================================================
# Type guards and field accessors
# ============================================================================

def _is_str(val: object) -> TypeGuard[str]:
    return isinstance(val, str)


def _is_number(val: object) -> TypeGuard[int | float]:
    return isinstance(val, (int, float)) and not isinstance(val, bool)


def _get_str(d: dict[str, object], key: str, row_num: int) -> str:
    """Extract a required string field, with row-number error context."""
    val = d.get(key)
    if not _is_str(val):
        raise ValueError(f"Row {row_num}: missing or invalid '{key}' (expected string)")
    return val


def _get_number(d: dict[str, object], key: str, row_num: int) -> float:
    """Extract a required numeric field, with row-number error context."""
    val = d.get(key)
    if _is_number(val):
        return float(val)
    raise ValueError(f"Row {row_num}: missing or invalid '{key}' (expected number)")


def _get_int(d: dict[str, object], key: str, row_num: int) -> int:
    """Extract a required integer field, with row-number error context."""
    val = d.get(key)
    if isinstance(val, int) and not isinstance(val, bool):
        return val
    raise ValueError(f"Row {row_num}: missing or invalid '{key}' (expected integer)")


def _get_bool(d: dict[str, object], key: str, row_num: int) -> bool:
    """Extract a required boolean field, with row-number error context."""
    val = d.get(key)
    if isinstance(val, bool):
        return val
    # Accept string "TRUE"/"FALSE" (Excel sometimes stores booleans as text)
    if _is_str(val):
        upper = val.upper()
        if upper == "TRUE":
            return True
        if upper == "FALSE":
            return False
    raise ValueError(f"Row {row_num}: missing or invalid '{key}' (expected TRUE/FALSE)")


# ============================================================================
# Row helpers
# ============================================================================

def _row_to_dict(headers: list[str], row: ExcelRow) -> dict[str, object]:
    """Zip headers with cell values, skipping None values."""
    return {h: v for h, v in zip(headers, row, strict=False) if v is not None}


def _headers_from_row(row: ExcelRow) -> list[str]:
    """Extract header strings from the first row of a sheet."""
    return [str(c) if c is not None else "" for c in row]


def _parse_message_id(val: object, row_num: int) -> int:
    """Parse a message ID from an int or hex-string cell value."""
    if isinstance(val, int) and not isinstance(val, bool):
        return val
    if _is_str(val):
        stripped = val.strip()
        try:
            if stripped.lower().startswith("0x"):
                return int(stripped, 16)
            return int(stripped)
        except ValueError:
            pass
    raise ValueError(
        f"Row {row_num}: invalid 'Message ID' — expected integer or hex string (e.g. 0x100)"
    )


# ============================================================================
# Public API
# ============================================================================

def load_checks_from_excel(
    path: str | Path,
    *,
    checks_sheet: str = "Checks",
    when_then_sheet: str = "When-Then",
) -> list[CheckResult]:
    """Load signal checks from an Excel workbook.

    Reads the Checks and When-Then sheets. Either or both may be present.

    Args:
        path: Path to a .xlsx workbook
        checks_sheet: Name of the simple-checks sheet
        when_then_sheet: Name of the when/then-checks sheet

    Returns:
        List of CheckResult objects ready for use with AletheiaClient

    Raises:
        FileNotFoundError: File doesn't exist
        ValueError: Invalid data in cells
    """
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(f"Excel file not found: {path}")

    wb = openpyxl.load_workbook(p, read_only=True, data_only=True)
    try:
        results: list[CheckResult] = []
        sheet_names = wb.sheetnames

        if checks_sheet in sheet_names:
            results.extend(_load_simple_checks(wb[checks_sheet]))

        if when_then_sheet in sheet_names:
            results.extend(_load_when_then_checks(wb[when_then_sheet]))

        if checks_sheet not in sheet_names and when_then_sheet not in sheet_names:
            raise ValueError(
                f"Workbook has no '{checks_sheet}' or '{when_then_sheet}' sheet"
            )

        return results
    finally:
        wb.close()


def load_dbc_from_excel(
    path: str | Path,
    *,
    sheet: str = "DBC",
) -> DBCDefinition:
    """Load a DBC definition from the DBC sheet of an Excel workbook.

    Args:
        path: Path to a .xlsx workbook
        sheet: Name of the DBC sheet

    Returns:
        DBCDefinition dict ready for use with AletheiaClient.parse_dbc()

    Raises:
        FileNotFoundError: File doesn't exist
        ValueError: Invalid or missing data
    """
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(f"Excel file not found: {path}")

    wb = openpyxl.load_workbook(p, read_only=True, data_only=True)
    try:
        if sheet not in wb.sheetnames:
            raise ValueError(f"Workbook has no '{sheet}' sheet")

        ws = wb[sheet]
        rows: list[ExcelRow] = list(ws.iter_rows(values_only=True))
        if len(rows) < 2:
            raise ValueError("DBC sheet must have a header row and at least one data row")

        headers = _headers_from_row(rows[0])
        data_rows = [_row_to_dict(headers, r) for r in rows[1:]]
        # Filter out completely empty rows
        data_rows = [r for r in data_rows if r]

        if not data_rows:
            raise ValueError("DBC sheet has no data rows")

        return _parse_dbc_rows(data_rows)
    finally:
        wb.close()


def create_template(path: str | Path) -> None:
    """Create a blank Excel template with headers and column formatting.

    Writes a .xlsx file with three sheets (DBC, Checks, When-Then),
    each with correct headers in bold. Does not overwrite existing files.

    Args:
        path: Output path for the .xlsx file

    Raises:
        FileExistsError: File already exists
    """
    p = Path(path)
    if p.exists():
        raise FileExistsError(f"File already exists: {path}")

    wb = Workbook()

    # DBC sheet (rename the default sheet)
    ws_dbc = wb.active
    assert ws_dbc is not None
    ws_dbc.title = "DBC"
    _write_header_row(ws_dbc, _DBC_HEADERS)

    # Checks sheet
    ws_checks = wb.create_sheet("Checks")
    _write_header_row(ws_checks, _CHECKS_HEADERS)

    # When-Then sheet
    ws_wt = wb.create_sheet("When-Then")
    _write_header_row(ws_wt, _WHEN_THEN_HEADERS)

    wb.save(str(p))


# ============================================================================
# Internal: sheet loaders
# ============================================================================

def _write_header_row(ws: Worksheet, headers: list[str]) -> None:
    """Write bold header row to a worksheet."""
    bold = Font(bold=True)
    for col_idx, header in enumerate(headers, start=1):
        cell = ws.cell(row=1, column=col_idx, value=header)
        cell.font = bold


def _load_simple_checks(ws: Worksheet) -> list[CheckResult]:
    """Load CheckResults from a Checks sheet."""
    rows: list[ExcelRow] = list(ws.iter_rows(values_only=True))
    if not rows:
        return []

    headers = _headers_from_row(rows[0])
    results: list[CheckResult] = []
    for row_idx, row in enumerate(rows[1:], start=2):
        d = _row_to_dict(headers, row)
        if not d:
            continue  # skip empty rows
        results.append(_parse_simple_row(d, row_idx))
    return results


def _load_when_then_checks(ws: Worksheet) -> list[CheckResult]:
    """Load CheckResults from a When-Then sheet."""
    rows: list[ExcelRow] = list(ws.iter_rows(values_only=True))
    if not rows:
        return []

    headers = _headers_from_row(rows[0])
    results: list[CheckResult] = []
    for row_idx, row in enumerate(rows[1:], start=2):
        d = _row_to_dict(headers, row)
        if not d:
            continue  # skip empty rows
        results.append(_parse_when_then_row(d, row_idx))
    return results


# ============================================================================
# Internal: row parsers
# ============================================================================

def _apply_metadata(result: CheckResult, d: dict[str, object]) -> CheckResult:
    """Apply optional name and severity from row data to a CheckResult."""
    name = d.get("Check Name")
    if _is_str(name):
        result.named(name)
    sev = d.get("Severity")
    if _is_str(sev):
        result.severity(sev)
    return result


def _parse_simple_row(d: dict[str, object], row_num: int) -> CheckResult:
    """Parse a Checks-sheet row into a CheckResult."""
    signal = _get_str(d, "Signal", row_num)
    condition = _get_str(d, "Condition", row_num)

    if condition not in _ALL_SIMPLE_CONDITIONS:
        raise ValueError(f"Row {row_num}: unknown condition '{condition}'")

    builder = Check.signal(signal)

    if condition in _SIMPLE_VALUE_CONDITIONS:
        value = _get_number(d, "Value", row_num)
        if condition == "never_exceeds":
            result = builder.never_exceeds(value)
        elif condition == "never_below":
            result = builder.never_below(value)
        else:  # never_equals
            result = builder.never_equals(value)
    elif condition in _SIMPLE_RANGE_CONDITIONS:
        if "Min" not in d or "Max" not in d:
            raise ValueError(
                f"Row {row_num}: condition '{condition}' requires 'Min' and 'Max'"
            )
        result = builder.stays_between(
            _get_number(d, "Min", row_num),
            _get_number(d, "Max", row_num),
        )
    elif condition in _SIMPLE_SETTLES_CONDITIONS:
        if "Min" not in d or "Max" not in d:
            raise ValueError(
                f"Row {row_num}: condition 'settles_between' requires 'Min' and 'Max'"
            )
        if "Time (ms)" not in d:
            raise ValueError(
                f"Row {row_num}: condition 'settles_between' requires 'Time (ms)'"
            )
        result = builder.settles_between(
            _get_number(d, "Min", row_num),
            _get_number(d, "Max", row_num),
        ).within(_get_int(d, "Time (ms)", row_num))
    else:
        # equals → equals().always()
        value = _get_number(d, "Value", row_num)
        result = builder.equals(value).always()

    return _apply_metadata(result, d)


def _parse_when_then_row(d: dict[str, object], row_num: int) -> CheckResult:
    """Parse a When-Then-sheet row into a CheckResult."""
    # When clause
    when_signal = _get_str(d, "When Signal", row_num)
    when_cond = _get_str(d, "When Condition", row_num)
    when_value = _get_number(d, "When Value", row_num)

    if when_cond not in _WHEN_CONDITIONS:
        raise ValueError(f"Row {row_num}: unknown when condition '{when_cond}'")

    when_builder = Check.when(when_signal)
    if when_cond == "exceeds":
        when_result = when_builder.exceeds(when_value)
    elif when_cond == "equals":
        when_result = when_builder.equals(when_value)
    else:  # drops_below
        when_result = when_builder.drops_below(when_value)

    # Then clause
    then_signal = _get_str(d, "Then Signal", row_num)
    then_cond = _get_str(d, "Then Condition", row_num)

    if then_cond not in _ALL_THEN_CONDITIONS:
        raise ValueError(f"Row {row_num}: unknown then condition '{then_cond}'")

    then_builder = when_result.then(then_signal)

    if then_cond == "equals":
        then_result = then_builder.equals(_get_number(d, "Then Value", row_num))
    elif then_cond == "exceeds":
        then_result = then_builder.exceeds(_get_number(d, "Then Value", row_num))
    else:  # stays_between
        if "Then Min" not in d or "Then Max" not in d:
            raise ValueError(
                f"Row {row_num}: then condition 'stays_between' requires 'Then Min' and 'Then Max'"
            )
        then_result = then_builder.stays_between(
            _get_number(d, "Then Min", row_num),
            _get_number(d, "Then Max", row_num),
        )

    result = then_result.within(_get_int(d, "Within (ms)", row_num))
    return _apply_metadata(result, d)


# ============================================================================
# Internal: DBC parser
# ============================================================================

def _parse_dbc_signal(row: dict[str, object], row_num: int) -> DBCSignal:
    """Parse a single DBC signal row into a DBCSignal dict."""
    byte_order = _get_str(row, "Byte Order", row_num)
    if byte_order not in ("little_endian", "big_endian"):
        raise ValueError(
            f"Row {row_num}: 'Byte Order' must be 'little_endian' or 'big_endian'"
        )

    unit = row.get("Unit")
    unit_str = str(unit) if _is_str(unit) else ""

    base_fields = {
        "name": _get_str(row, "Signal", row_num),
        "startBit": _get_int(row, "Start Bit", row_num),
        "length": _get_int(row, "Length", row_num),
        "byteOrder": byte_order,
        "signed": _get_bool(row, "Signed", row_num),
        "factor": _get_number(row, "Factor", row_num),
        "offset": _get_number(row, "Offset", row_num),
        "minimum": _get_number(row, "Min", row_num),
        "maximum": _get_number(row, "Max", row_num),
        "unit": unit_str,
    }

    has_muxor = "Multiplexor" in row
    has_mux_val = "Multiplex Value" in row

    if has_muxor != has_mux_val:
        msg = "must both be provided or both be empty"
        raise ValueError(
            f"Row {row_num}: 'Multiplexor' and 'Multiplex Value' {msg}"
        )

    if has_muxor:
        mux_signal: DBCSignalMultiplexed = {
            **base_fields,  # type: ignore[typeddict-item]
            "multiplexor": _get_str(row, "Multiplexor", row_num),
            "multiplex_value": _get_int(row, "Multiplex Value", row_num),
        }
        return mux_signal

    always_signal: DBCSignalAlways = {
        **base_fields,  # type: ignore[typeddict-item]
        "presence": "always",
    }
    return always_signal


def _parse_dbc_rows(rows: list[dict[str, object]]) -> DBCDefinition:
    """Group DBC rows by message and build a DBCDefinition."""
    groups: dict[_MessageKey, list[int]] = defaultdict(list)
    insertion_order: list[_MessageKey] = []

    for idx, row in enumerate(rows):
        row_num = idx + 2  # 1-indexed, skip header
        key = _MessageKey(
            msg_id=_parse_message_id(row.get("Message ID"), row_num),
            name=_get_str(row, "Message Name", row_num),
            dlc=_get_int(row, "DLC", row_num),
        )
        if key not in groups:
            insertion_order.append(key)
        groups[key].append(idx)

    messages: list[DBCMessage] = []
    for key in insertion_order:
        signals: list[DBCSignal] = [
            _parse_dbc_signal(rows[i], i + 2) for i in groups[key]
        ]
        messages.append({
            "id": key.msg_id,
            "name": key.name,
            "dlc": key.dlc,
            "sender": "",
            "signals": signals,
        })

    return {"version": "", "messages": messages}
