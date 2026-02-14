#!/usr/bin/env python3
"""Excel Loader Demo

Load signal checks and DBC definitions from an Excel workbook (.xlsx).
Designed for automotive technicians: fill in cells, press Run.

The workbook used here is demo_workbook.xlsx — open it alongside this
script to see what the spreadsheet looks like.

No FFI or Agda build required — this demo only generates formulas.
"""

import tempfile
from pathlib import Path

from aletheia import Check, load_checks_from_excel, load_dbc_from_excel, create_template


WORKBOOK = Path(__file__).parent / "demo_workbook.xlsx"


# =============================================================================
# SECTION 1: Create a Blank Template
# =============================================================================

print("=" * 60)
print("SECTION 1: Create a Blank Template")
print("=" * 60)

with tempfile.TemporaryDirectory() as tmpdir:
    template_path = Path(tmpdir) / "template.xlsx"
    create_template(template_path)

    import openpyxl  # type: ignore[import-untyped]
    wb = openpyxl.load_workbook(template_path)
    print(f"\n  Created: {template_path.name}")
    print(f"  Sheets:  {wb.sheetnames}")
    wb.close()


# =============================================================================
# SECTION 2: Load Checks from Excel
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 2: Load Checks from Excel")
print("=" * 60)

print(f"\n  Workbook: {WORKBOOK.name}")

checks = load_checks_from_excel(WORKBOOK)
print(f"  Loaded {len(checks)} checks:")

for i, check in enumerate(checks, 1):
    name = check.name or "<unnamed>"
    sev = check.check_severity or "-"
    print(f"    {i}. {name} [{sev}]")


# =============================================================================
# SECTION 3: Load DBC from Excel
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 3: Load DBC from Excel")
print("=" * 60)

dbc = load_dbc_from_excel(WORKBOOK)

print(f"\n  {len(dbc['messages'])} messages:")
for msg in dbc["messages"]:
    sig_names = [s["name"] for s in msg["signals"]]
    print(f"    0x{msg['id']:03X} {msg['name']} (DLC={msg['dlc']}): {', '.join(sig_names)}")

sig = dbc["messages"][0]["signals"][0]
print(f"\n  Signal detail — {sig['name']}:")
print(f"    bits[{sig['startBit']}:{sig['length']}]  {sig['byteOrder']}")
print(f"    factor={sig['factor']}  offset={sig['offset']}")
print(f"    range=[{sig['minimum']}, {sig['maximum']}] {sig['unit']}")


# =============================================================================
# SECTION 4: Equivalence with Check API
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 4: Equivalence with Check API")
print("=" * 60)

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
# DONE
# =============================================================================

print("\n" + "=" * 60)
print("DONE")
print("=" * 60)
