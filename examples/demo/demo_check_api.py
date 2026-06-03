#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Check API Demo.

The Check API provides industry-vocabulary wrappers over the LTL DSL.
Every check compiles to the same verified LTL property used by the DSL layer.

No FFI or Agda build required — this demo only generates formulas.
"""

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

import json

from aletheia import Signal
from aletheia.checks import signal, when

# =============================================================================
# SECTION 1: Simple Signal Checks
# =============================================================================

print("=" * 60)
print("SECTION 1: Simple Signal Checks")
print("=" * 60)

check1 = signal("VehicleSpeed").never_exceeds(220)
print("\n1. signal('VehicleSpeed').never_exceeds(220)")

check2 = signal("BatteryVoltage").stays_between(11.5, 14.5)
print("2. signal('BatteryVoltage').stays_between(11.5, 14.5)")

check3 = signal("CoolantTemp").settles_between(80, 100).within(5000)
print("3. signal('CoolantTemp').settles_between(80, 100).within(5000)")

check4 = signal("FaultCode").never_equals(255)
print("4. signal('FaultCode').never_equals(255)")

check5 = signal("ParkingBrake").equals(1).always()
print("5. signal('ParkingBrake').equals(1).always()")

check6 = signal("BatteryVoltage").never_below(11.0)
print("6. signal('BatteryVoltage').never_below(11.0)")


# =============================================================================
# SECTION 2: When/Then Causal Checks
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 2: When/Then Causal Checks")
print("=" * 60)

check7 = when("BrakePedal").exceeds(50).then("BrakeLight").equals(1).within(100)
print("\n7. when('BrakePedal').exceeds(50)")
print("       .then('BrakeLight').equals(1).within(100)")

check8 = when("Ignition").equals(1).then("EngineRPM").exceeds(500).within(2000)
print("\n8. when('Ignition').equals(1)")
print("       .then('EngineRPM').exceeds(500).within(2000)")

check9 = when("FuelLevel").drops_below(10).then("FuelWarning").stays_between(1, 1).within(50)
print("\n9. when('FuelLevel').drops_below(10)")
print("       .then('FuelWarning').stays_between(1, 1).within(50)")


# =============================================================================
# SECTION 3: Metadata
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 3: Metadata")
print("=" * 60)

labeled = signal("VehicleSpeed").never_exceeds(220).named("Speed limit").severity("safety")
print(f"\n  Name:     {labeled.name}")
print(f"  Severity: {labeled.check_severity}")


# =============================================================================
# SECTION 4: Generated LTL
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 4: Generated LTL Formula")
print("=" * 60)

print("\nsignal('VehicleSpeed').never_exceeds(220) produces:\n")
print(json.dumps(check1.to_dict(), indent=2))


# =============================================================================
# SECTION 5: Equivalence with Raw DSL
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 5: Equivalence with Raw DSL")
print("=" * 60)

dsl_formula = Signal("VehicleSpeed").less_than(220).always().to_dict()
check_formula = signal("VehicleSpeed").never_exceeds(220).to_dict()

print("\n  Check API: signal('VehicleSpeed').never_exceeds(220)")
print("  Raw DSL:   Signal('VehicleSpeed').less_than(220).always()")
print(f"  Identical: {dsl_formula == check_formula}")

dsl_wt = (
    Signal("BrakePedal")
    .greater_than(50)
    .implies(Signal("BrakeLight").equals(1).within(100))
    .always()
    .to_dict()
)
check_wt = when("BrakePedal").exceeds(50).then("BrakeLight").equals(1).within(100).to_dict()

print("\n  Check API: when('BrakePedal').exceeds(50)")
print("                 .then('BrakeLight').equals(1).within(100)")
print("  Raw DSL:   Signal('BrakePedal').greater_than(50)")
print("                 .implies(Signal('BrakeLight').equals(1).within(100))")
print("                 .always()")
print(f"  Identical: {dsl_wt == check_wt}")


# =============================================================================
# DONE
# =============================================================================

print("\n" + "=" * 60)
print("DONE")
print("=" * 60)
