#!/usr/bin/env python3
"""Check API Demo

The Check API provides industry-vocabulary wrappers over the LTL DSL.
Automotive technicians can define signal checks without knowing temporal logic.

Every check compiles to the same verified LTL property used by the DSL layer.

No FFI or Agda build required — this demo only generates formulas.
"""

import json
import sys
from pathlib import Path

# Allow running from examples/demo/ or project root
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "python"))

from aletheia import Check, Signal


# =============================================================================
# SECTION 1: Simple Signal Checks
# =============================================================================

print("=" * 70)
print("CHECK API — Industry Vocabulary for Signal Verification")
print("=" * 70)

print("""
The Check API wraps the LTL DSL with domain-specific methods.
Each call returns a CheckResult that can be named, given a severity,
and serialized to the same JSON that the verified Agda core processes.
""")

print("-" * 70)
print("SECTION 1: Simple Signal Checks")
print("-" * 70)

# 1. Speed limit — never_exceeds
check1 = Check.signal("VehicleSpeed").never_exceeds(220)
print("\n1. Speed limit (safety):")
print("   Check.signal('VehicleSpeed').never_exceeds(220)")
print("   Meaning: Vehicle speed must always stay below 220 km/h")

# 2. Battery voltage range — stays_between
check2 = Check.signal("BatteryVoltage").stays_between(11.5, 14.5)
print("\n2. Battery voltage range (warning):")
print("   Check.signal('BatteryVoltage').stays_between(11.5, 14.5)")
print("   Meaning: Battery voltage must always remain between 11.5V and 14.5V")

# 3. Coolant temperature settling — settles_between + within
check3 = Check.signal("CoolantTemp").settles_between(80, 100).within(5000)
print("\n3. Coolant temperature settling (info):")
print("   Check.signal('CoolantTemp').settles_between(80, 100).within(5000)")
print("   Meaning: Coolant temperature must stay between 80-100C for 5 seconds")

# 4. Fault code exclusion — never_equals
check4 = Check.signal("FaultCode").never_equals(255)
print("\n4. Fault code exclusion (critical):")
print("   Check.signal('FaultCode').never_equals(255)")
print("   Meaning: Fault code 0xFF must never appear")

# 5. Parking brake engaged — equals + always
check5 = Check.signal("ParkingBrake").equals(1).always()
print("\n5. Parking brake engaged (info):")
print("   Check.signal('ParkingBrake').equals(1).always()")
print("   Meaning: Parking brake signal must always equal 1")

# 6. Battery floor — never_below
check6 = Check.signal("BatteryVoltage").never_below(11.0)
print("\n6. Battery floor (critical):")
print("   Check.signal('BatteryVoltage').never_below(11.0)")
print("   Meaning: Battery voltage must never drop below 11.0V")


# =============================================================================
# SECTION 2: When/Then Causal Checks
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 2: When/Then Causal Checks")
print("-" * 70)

print("""
Causal checks express response-time requirements:
"When X happens, then Y must follow within T milliseconds."
""")

# 7. Brake light response
check7 = (
    Check.when("BrakePedal").exceeds(50)
    .then("BrakeLight").equals(1)
    .within(100)
)
print("7. Brake light response (safety):")
print("   Check.when('BrakePedal').exceeds(50)")
print("       .then('BrakeLight').equals(1)")
print("       .within(100)")
print("   Meaning: When brake pedal > 50%, brake light must turn on within 100ms")

# 8. Engine start response
check8 = (
    Check.when("Ignition").equals(1)
    .then("EngineRPM").exceeds(500)
    .within(2000)
)
print("\n8. Engine start response (warning):")
print("   Check.when('Ignition').equals(1)")
print("       .then('EngineRPM').exceeds(500)")
print("       .within(2000)")
print("   Meaning: When ignition is turned on, RPM must exceed 500 within 2s")

# 9. Fuel warning
check9 = (
    Check.when("FuelLevel").drops_below(10)
    .then("FuelWarning").stays_between(1, 1)
    .within(50)
)
print("\n9. Fuel warning activation (info):")
print("   Check.when('FuelLevel').drops_below(10)")
print("       .then('FuelWarning').stays_between(1, 1)")
print("       .within(50)")
print("   Meaning: When fuel < 10%, warning light must activate within 50ms")


# =============================================================================
# SECTION 3: Metadata
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 3: Metadata — Naming and Severity")
print("-" * 70)

print("""
Every check can carry a name and severity for reporting and diagnostics.
Metadata is for display only — it does not affect the LTL formula.
""")

labeled = (
    Check.signal("VehicleSpeed").never_exceeds(220)
    .named("Speed limit")
    .severity("safety")
)
print(f"   Name:     {labeled.name}")
print(f"   Severity: {labeled.check_severity}")
print(f"   Formula:  (same as unlabeled check)")


# =============================================================================
# SECTION 4: Generated LTL
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 4: Generated LTL Formula")
print("-" * 70)

print("""
The Check API compiles to the same JSON schema that the verified Agda core
processes. Here is what Check.signal("VehicleSpeed").never_exceeds(220)
produces:
""")

print(json.dumps(check1.to_dict(), indent=2))


# =============================================================================
# SECTION 5: Equivalence with Raw DSL
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 5: Equivalence with Raw DSL")
print("-" * 70)

print("""
The Check API is syntactic sugar. Each check produces the exact same
formula as the equivalent DSL expression:
""")

dsl_formula = Signal("VehicleSpeed").less_than(220).always().to_dict()
check_formula = Check.signal("VehicleSpeed").never_exceeds(220).to_dict()

print("   Check API: Check.signal('VehicleSpeed').never_exceeds(220)")
print("   Raw DSL:   Signal('VehicleSpeed').less_than(220).always()")
print(f"   Identical: {dsl_formula == check_formula}")

dsl_wt = (
    Signal("BrakePedal").greater_than(50)
    .implies(Signal("BrakeLight").equals(1).within(100))
    .always()
    .to_dict()
)
check_wt = (
    Check.when("BrakePedal").exceeds(50)
    .then("BrakeLight").equals(1)
    .within(100)
    .to_dict()
)

print("\n   Check API: Check.when('BrakePedal').exceeds(50)")
print("                 .then('BrakeLight').equals(1).within(100)")
print("   Raw DSL:   Signal('BrakePedal').greater_than(50)")
print("                 .implies(Signal('BrakeLight').equals(1).within(100))")
print("                 .always()")
print(f"   Identical: {dsl_wt == check_wt}")


# =============================================================================
# SUMMARY
# =============================================================================

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
The Check API provides:
  - Industry vocabulary: never_exceeds, stays_between, settles_between
  - Causal checks: when/then/within for response-time requirements
  - Metadata: name and severity for reporting
  - Zero overhead: compiles to the same LTL as the raw DSL
  - Correctness: formulas are checked by the verified Agda core

Designed for automotive technicians who think in terms of
"speed must never exceed 220" rather than "G(speed < 220)".
""")
