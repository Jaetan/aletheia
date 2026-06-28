# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Four-Tier Equivalence Demo.

Defines the same 3 checks using all four interface tiers and proves
they produce identical LTL formulas:

    Excel -> YAML -> Check API -> DSL -> same verified Agda core

Decimals are exact `Fraction`s in code, and the YAML/Excel loaders parse decimal
text via the verified Agda kernel (the float principle: never a lossy float), so a
live client must be up while loading — hence the `with AletheiaClient()` blocks.
Build the library first: `cabal run shake -- build`.
"""

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

import tempfile
from fractions import Fraction
from pathlib import Path

from openpyxl.workbook import Workbook  # type: ignore[import-untyped]

from aletheia import (
    AletheiaClient,
    Signal,
    load_checks,
    load_checks_from_excel,
)
from aletheia.checks import signal, when
from aletheia.types import dump_json

# The 3 checks:
#   1. VehicleSpeed never_exceeds 220
#   2. BatteryVoltage stays_between 11.5, 14.5
#   3. BrakePedal > 50 => BrakeLight = 1 within 100ms

CHECKS_HEADERS = [
    "Check Name",
    "Signal",
    "Condition",
    "Value",
    "Min",
    "Max",
    "Time (ms)",
    "Severity",
]
WHEN_THEN_HEADERS = [
    "Check Name",
    "When Signal",
    "When Condition",
    "When Value",
    "Then Signal",
    "Then Condition",
    "Then Value",
    "Then Min",
    "Then Max",
    "Within (ms)",
    "Severity",
]


# =============================================================================
# TIER 1: Raw DSL
# =============================================================================

print("=" * 60)
print("TIER 1: Raw DSL (developer)")
print("=" * 60)

dsl_1 = Signal("VehicleSpeed").less_than(220).always().to_dict()
dsl_2 = Signal("BatteryVoltage").between(Fraction("11.5"), Fraction("14.5")).always().to_dict()
dsl_3 = (
    Signal("BrakePedal")
    .greater_than(50)
    .implies(Signal("BrakeLight").equals(1).within(100))
    .always()
    .to_dict()
)

print("\n  Signal('VehicleSpeed').less_than(220).always()")
print("  Signal('BatteryVoltage').between(11.5, 14.5).always()")
print("  Signal('BrakePedal').greater_than(50)")
print("      .implies(Signal('BrakeLight').equals(1).within(100)).always()")


# =============================================================================
# TIER 2: Check API
# =============================================================================

print("\n" + "=" * 60)
print("TIER 2: Check API (scripter)")
print("=" * 60)

api_1 = signal("VehicleSpeed").never_exceeds(220).to_dict()
api_2 = signal("BatteryVoltage").stays_between(Fraction("11.5"), Fraction("14.5")).to_dict()
api_3 = when("BrakePedal").exceeds(50).then("BrakeLight").equals(1).within(100).to_dict()

print("\n  signal('VehicleSpeed').never_exceeds(220)")
print("  signal('BatteryVoltage').stays_between(11.5, 14.5)")
print("  when('BrakePedal').exceeds(50)")
print("      .then('BrakeLight').equals(1).within(100)")


# =============================================================================
# TIER 3: YAML
# =============================================================================

print("\n" + "=" * 60)
print("TIER 3: YAML (test engineer)")
print("=" * 60)

YAML_SRC = """
checks:
  - signal: VehicleSpeed
    condition: never_exceeds
    value: 220

  - signal: BatteryVoltage
    condition: stays_between
    min: 11.5
    max: 14.5

  - when:
      signal: BrakePedal
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
    within_ms: 100
"""

# Loading parses the YAML's decimal values via the verified kernel (RTS-gated).
with AletheiaClient():
    yaml_checks = load_checks(YAML_SRC)
yaml_1 = yaml_checks[0].to_dict()
yaml_2 = yaml_checks[1].to_dict()
yaml_3 = yaml_checks[2].to_dict()

for line in YAML_SRC.strip().split("\n"):
    print(f"  {line}")


# =============================================================================
# TIER 4: Excel
# =============================================================================

print("\n" + "=" * 60)
print("TIER 4: Excel (technician)")
print("=" * 60)

with tempfile.TemporaryDirectory() as tmpdir:
    wb = Workbook()
    ws = wb.active
    assert ws is not None
    ws.title = "Checks"
    ws.append(CHECKS_HEADERS)
    # Numeric cells are TEXT-formatted (the all-text contract — a number cell
    # stores a lossy float), parsed exactly by the kernel on load.
    ws.append([None, "VehicleSpeed", "never_exceeds", "220", None, None, None, None])
    ws.append([None, "BatteryVoltage", "stays_between", None, "11.5", "14.5", None, None])

    ws_wt = wb.create_sheet("When-Then")
    ws_wt.append(WHEN_THEN_HEADERS)
    ws_wt.append(
        [None, "BrakePedal", "exceeds", "50", "BrakeLight", "equals", "1", None, None, "100", None]
    )

    xlsx_path = Path(tmpdir) / "checks.xlsx"
    wb.save(str(xlsx_path))

    with AletheiaClient():
        excel_checks = load_checks_from_excel(xlsx_path)
    excel_1 = excel_checks[0].to_dict()
    excel_2 = excel_checks[1].to_dict()
    excel_3 = excel_checks[2].to_dict()

print("\n  Checks sheet:    | VehicleSpeed | never_exceeds | 220 |")
print("                   | BatteryVoltage | stays_between | | 11.5 | 14.5 |")
print("  When-Then sheet: | BrakePedal | exceeds | 50 | BrakeLight | equals | 1 | 100ms |")


# =============================================================================
# EQUIVALENCE PROOF
# =============================================================================

print("\n" + "=" * 60)
print("EQUIVALENCE PROOF")
print("=" * 60)

all_pass = True

match_1 = dsl_1 == api_1 == yaml_1 == excel_1
all_pass = all_pass and match_1
print("\n  1. VehicleSpeed never_exceeds 220")
print(f"     DSL == Check API == YAML == Excel: {match_1}")

match_2 = dsl_2 == api_2 == yaml_2 == excel_2
all_pass = all_pass and match_2
print("\n  2. BatteryVoltage stays_between 11.5, 14.5")
print(f"     DSL == Check API == YAML == Excel: {match_2}")

match_3 = dsl_3 == api_3 == yaml_3 == excel_3
all_pass = all_pass and match_3
print("\n  3. BrakePedal > 50 => BrakeLight = 1 within 100ms")
print(f"     DSL == Check API == YAML == Excel: {match_3}")

print("\n  Shared formula:")
print(f"  {dump_json(dsl_1, indent=2)}")


# =============================================================================
# DONE
# =============================================================================

print("\n" + "=" * 60)
if all_pass:
    print("ALL 3 CHECKS MATCH ACROSS ALL 4 TIERS")
else:
    print("MISMATCH DETECTED")
print("=" * 60)
