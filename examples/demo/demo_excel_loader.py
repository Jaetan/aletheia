#!/usr/bin/env python3
"""Excel Loader Demo

Load signal checks and DBC definitions from Excel workbooks (.xlsx).
Designed for automotive technicians: fill in cells, press Run.

No FFI or Agda build required — this demo only generates formulas.
"""

import json
import sys
import tempfile
from pathlib import Path

# Allow running from examples/demo/ or project root
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "python"))

from openpyxl.workbook import Workbook  # type: ignore[import-untyped]

from aletheia import Check, load_checks_from_excel, load_dbc_from_excel, create_template


# =============================================================================
# SECTION 1: Create a Template
# =============================================================================

print("=" * 70)
print("EXCEL LOADER — Spreadsheet Templates for Technicians")
print("=" * 70)

print("""
The Excel loader lets technicians define checks in familiar spreadsheets.
Three sheets in one workbook: DBC, Checks, When-Then.
""")

print("-" * 70)
print("SECTION 1: Create a Blank Template")
print("-" * 70)

with tempfile.TemporaryDirectory() as tmpdir:
    template_path = Path(tmpdir) / "template.xlsx"
    create_template(template_path)
    print(f"\n  Created template: {template_path.name}")
    print("  Sheets: DBC, Checks, When-Then")
    print("  Headers are bold and ready for data entry")

    # Verify
    import openpyxl  # type: ignore[import-untyped]
    wb = openpyxl.load_workbook(template_path)
    print(f"  Sheet names: {wb.sheetnames}")
    wb.close()


# =============================================================================
# SECTION 2: Load Simple Checks
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 2: Load Checks from Excel")
print("-" * 70)

print("""
The Checks sheet has one row per simple check:
  Check Name | Signal | Condition | Value | Min | Max | Time (ms) | Severity
""")

CHECKS_HEADERS = [
    "Check Name", "Signal", "Condition", "Value", "Min", "Max",
    "Time (ms)", "Severity",
]

WHEN_THEN_HEADERS = [
    "Check Name", "When Signal", "When Condition", "When Value",
    "Then Signal", "Then Condition", "Then Value", "Then Min", "Then Max",
    "Within (ms)", "Severity",
]

with tempfile.TemporaryDirectory() as tmpdir:
    # Build a workbook with the same 9 checks as the other demos
    wb = Workbook()

    # -- Checks sheet --
    ws_checks = wb.active
    assert ws_checks is not None
    ws_checks.title = "Checks"
    ws_checks.append(CHECKS_HEADERS)
    ws_checks.append(["Speed limit", "VehicleSpeed", "never_exceeds", 220, None, None, None, "safety"])
    ws_checks.append(["Battery voltage range", "BatteryVoltage", "stays_between", None, 11.5, 14.5, None, "warning"])
    ws_checks.append(["Coolant settling", "CoolantTemp", "settles_between", None, 80, 100, 5000, "info"])
    ws_checks.append(["Fault code exclusion", "FaultCode", "never_equals", 255, None, None, None, "critical"])
    ws_checks.append(["Parking brake", "ParkingBrake", "equals", 1, None, None, None, "info"])
    ws_checks.append(["Battery floor", "BatteryVoltage", "never_below", 11.0, None, None, None, "critical"])

    # -- When-Then sheet --
    ws_wt = wb.create_sheet("When-Then")
    ws_wt.append(WHEN_THEN_HEADERS)
    ws_wt.append(["Brake light", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, None, None, 100, "safety"])
    ws_wt.append(["Engine start", "Ignition", "equals", 1, "EngineRPM", "exceeds", 500, None, None, 2000, "warning"])
    ws_wt.append(["Fuel warning", "FuelLevel", "drops_below", 10, "FuelWarning", "stays_between", None, 1, 1, 50, "info"])

    checks_path = Path(tmpdir) / "checks.xlsx"
    wb.save(str(checks_path))

    # Load them back
    checks = load_checks_from_excel(checks_path)
    print(f"\n  Loaded {len(checks)} checks from Excel workbook")

    for i, check in enumerate(checks, 1):
        name = check.name or "<unnamed>"
        sev = check.check_severity or "-"
        print(f"    {i}. {name} [{sev}]")


# =============================================================================
# SECTION 3: Load DBC from Excel
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 3: Load DBC Definition from Excel")
print("-" * 70)

print("""
The DBC sheet has one row per signal. Multiple rows with the same
Message ID are grouped into one message.
""")

DBC_HEADERS = [
    "Message ID", "Message Name", "DLC", "Signal", "Start Bit", "Length",
    "Byte Order", "Signed", "Factor", "Offset", "Min", "Max", "Unit",
]

with tempfile.TemporaryDirectory() as tmpdir:
    wb = Workbook()
    ws = wb.active
    assert ws is not None
    ws.title = "DBC"
    ws.append(DBC_HEADERS)
    # EngineData message with 2 signals
    ws.append(["0x100", "EngineData", 8, "EngineSpeed", 0, 16, "little_endian", False, 0.25, 0, 0, 8000, "rpm"])
    ws.append(["0x100", "EngineData", 8, "EngineTemp", 16, 8, "little_endian", True, 1, -40, -40, 215, "C"])
    # BrakeStatus message with 2 signals
    ws.append([512, "BrakeStatus", 8, "BrakePressure", 0, 16, "little_endian", False, 0.1, 0, 0, 6553.5, "bar"])
    ws.append([512, "BrakeStatus", 8, "BrakeActive", 16, 1, "little_endian", False, 1, 0, 0, 1, ""])

    dbc_path = Path(tmpdir) / "vehicle.xlsx"
    wb.save(str(dbc_path))

    dbc = load_dbc_from_excel(dbc_path)

    print(f"\n  Loaded DBC with {len(dbc['messages'])} messages:")
    for msg in dbc["messages"]:
        sig_names = [s["name"] for s in msg["signals"]]
        print(f"    0x{msg['id']:03X} {msg['name']} (DLC={msg['dlc']}): {', '.join(sig_names)}")

    # Show one signal's details
    sig = dbc["messages"][0]["signals"][0]
    print(f"\n  Signal detail — {sig['name']}:")
    print(f"    Start bit: {sig['startBit']}, Length: {sig['length']}")
    print(f"    Byte order: {sig['byteOrder']}, Signed: {sig['signed']}")
    print(f"    Factor: {sig['factor']}, Offset: {sig['offset']}")
    print(f"    Range: [{sig['minimum']}, {sig['maximum']}] {sig['unit']}")


# =============================================================================
# SECTION 4: Hex Message IDs
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 4: Hex Message IDs")
print("-" * 70)

print("""
Message IDs can be entered as hex strings (0x100) or decimal (256).
Both produce the same result:
""")

print(f"  0x100 -> {dbc['messages'][0]['id']} (EngineData)")
print(f"  512   -> {dbc['messages'][1]['id']} (BrakeStatus)")


# =============================================================================
# SECTION 5: Equivalence with Check API
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 5: Equivalence with Check API")
print("-" * 70)

excel_speed = checks[0].to_dict()
api_speed = Check.signal("VehicleSpeed").never_exceeds(220).to_dict()
print(f"\n  Excel 'Speed limit' == Check API: {excel_speed == api_speed}")

excel_brake = checks[6].to_dict()
api_brake = (
    Check.when("BrakePedal").exceeds(50)
    .then("BrakeLight").equals(1)
    .within(100)
    .to_dict()
)
print(f"  Excel 'Brake light' == Check API: {excel_brake == api_brake}")


# =============================================================================
# SUMMARY
# =============================================================================

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
The Excel loader provides:
  - Blank templates with create_template()
  - Load checks from Checks and When-Then sheets
  - Load DBC definitions from DBC sheet
  - Hex and decimal message IDs
  - Multiplexed signal support (optional columns)
  - Same formulas as Check API, YAML, and raw DSL

Workflow for technicians:
  1. Open template.xlsx in Excel/LibreOffice
  2. Fill in signal names, conditions, values
  3. Save and run: load_checks_from_excel("my_checks.xlsx")
""")
