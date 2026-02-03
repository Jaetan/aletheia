#!/usr/bin/env python3
"""Aletheia Demo Script

This script demonstrates Aletheia's capabilities for the team presentation.
Run sections interactively or execute the whole script.

Requirements:
- Aletheia binary must be built: `cabal run shake -- build`
- Run from the examples/demo directory or adjust paths

Three-Valued Signal Semantics:
  Aletheia uses three-valued logic (True/False/Unknown) for signal predicates.
  When a CAN frame doesn't contain a referenced signal, the predicate returns
  Unknown instead of failing. This means:

  - You can send ALL frames without filtering by CAN ID
  - Safety properties (always, for_at_least) continue monitoring on Unknown
  - Liveness properties (eventually, within) wait for the signal to appear
  - Once a signal is observed, its value is cached for future frames

  This eliminates the need to pre-filter frames by message type.
"""

from pathlib import Path

# =============================================================================
# SECTION 1: Integration - Loading DBC and Signals (3-6 min)
# =============================================================================

print("=" * 60)
print("SECTION 1: Integration - Nothing Exotic")
print("=" * 60)

# "This starts from the same artifacts we already have."

from aletheia import Signal
from aletheia.dbc_converter import dbc_to_json

# Load the DBC file - handles scaling, byte order, multiplexing automatically
dbc_path = Path(__file__).parent / "vehicle.dbc"
dbc = dbc_to_json(str(dbc_path))

print(f"\nLoaded DBC: {dbc['version']}")
print(f"Messages: {[m['name'] for m in dbc['messages']]}")

# "Signals are resolved from the DBC."
speed = Signal("VehicleSpeed")
brake = Signal("BrakePressure")

print(f"\nSignals defined:")
print(f"  - {speed.name} (from VehicleDynamics message)")
print(f"  - {brake.name} (from BrakeStatus message)")


# =============================================================================
# SECTION 2: Expressing Intent - The Property (6-12 min)
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 2: Expressing Intent, Not Tests")
print("=" * 60)

# "Now the interesting part: expressing a requirement."

# Property 1: Speed limit - simple safety property
speed_limit = speed.less_than(120).always()

print("\nProperty 1 - Speed Limit (safety):")
print("  'Speed must always be under 120 kph'")
print("\n  Aletheia DSL:")
print("    speed.less_than(120).always()")

# Property 2: Brake response - temporal property with time bound
# "Whenever speed exceeds 80, braking must follow within 500 milliseconds"
brake_response = speed.greater_than(80).implies(
    brake.greater_than(0).within(500)
).always()

print("\nProperty 2 - Brake Response (temporal):")
print("  'Whenever speed exceeds 80 kph, braking must follow within 500ms'")
print("\n  Aletheia DSL:")
print("    speed.greater_than(80).implies(")
print("        brake.greater_than(0).within(500)")
print("    ).always()")

# Show the JSON representation
import json
print("\nSerialized to JSON (for the verified Agda core):")
print(json.dumps(speed_limit.to_dict(), indent=2))


# =============================================================================
# SECTION 3: Running on Real Data (12-15 min)
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 3: Running on Real Data")
print("=" * 60)

from aletheia import AletheiaClient
from drive_log import NORMAL_DRIVE

# No filtering needed! Three-valued semantics handles frames without the signal.
# Frames without VehicleSpeed return Unknown, which continues monitoring.

print(f"\nLoaded drive log: {len(NORMAL_DRIVE)} frames")
print(f"Duration: {NORMAL_DRIVE[-1].timestamp_ms}ms")
print("\nNote: Sending ALL frames (no filtering by CAN ID needed)")

# Check the speed limit property against the normal drive
print("\nChecking speed limit property (speed < 120 always)...")

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([speed_limit.to_dict()])
    client.start_stream()

    violations = []
    for frame in NORMAL_DRIVE:  # ALL frames - no filtering needed!
        response = client.send_frame(frame.timestamp_us, frame.can_id, frame.data)
        if response.get("status") == "violation":
            violations.append(response)

    result = client.end_stream()

if not violations:
    print("\n  Property HOLDS on this drive")
    print("  The speed never exceeded 120 kph throughout the recording.")
else:
    print(f"\n  Property VIOLATED: {len(violations)} violation(s)")


# =============================================================================
# SECTION 4: Fault Injection (15-20 min)
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 4: Fault Injection - Overspeed Event")
print("=" * 60)

from drive_log import OVERSPEED_DRIVE

print("\nSimulating a fault: vehicle exceeds 120 kph speed limit")
print(f"Loaded faulty drive log: {len(OVERSPEED_DRIVE)} frames")

# Check the same property against the overspeed drive
print("\nChecking speed limit against faulty drive...")

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([speed_limit.to_dict()])
    client.start_stream()

    violations = []
    for frame in OVERSPEED_DRIVE:  # ALL frames - no filtering needed!
        response = client.send_frame(frame.timestamp_us, frame.can_id, frame.data)
        if response.get("status") == "violation":
            violations.append(response)
            # Don't break - collect all violations

    result = client.end_stream()

if violations:
    print(f"\n  Property VIOLATED!")
    print(f"  {len(violations)} violation(s) detected")
    print("\n  The checker found the exact points where speed >= 120 kph.")
else:
    print("\n  Property holds (unexpected)")


# =============================================================================
# SECTION 5: Diagnostics (20-23 min)
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 5: Diagnostics - Not Just True/False")
print("=" * 60)

if violations:
    print("\nInstead of just saying 'false', Aletheia provides details:")
    for i, v in enumerate(violations[:3]):  # Show first 3
        print(f"\n  Violation {i+1}:")
        ts = v.get('timestamp', {})
        if isinstance(ts, dict):
            ts_us = ts.get('numerator', 0)
            print(f"    Timestamp: {ts_us // 1000}ms")
        print(f"    Property index: {v.get('property_index', {})}")
        if 'reason' in v:
            print(f"    Reason: {v['reason']}")

    if len(violations) > 3:
        print(f"\n  ... and {len(violations) - 3} more violations")

    print("\n  This pinpoints exactly where and when the requirement failed.")
    print("  Useful for debugging, not just pass/fail verification.")


# =============================================================================
# SECTION 6: More Properties (bonus examples)
# =============================================================================

print("\n" + "=" * 60)
print("BONUS: More Property Examples")
print("=" * 60)

# Safety property: speed must always be under 200 kph
speed_safety = speed.less_than(200).always()
print("\n1. Speed safety (absolute limit):")
print("   speed.less_than(200).always()")

# Range property: brake pressure must stay in valid range
brake_range = brake.between(0, 10000).always()
print("\n2. Sensor range (validity check):")
print("   brake.between(0, 10000).always()")

# Stability: brake pressure must stay high for 100ms once applied
brake_stable = brake.greater_than(100).for_at_least(100)
print("\n3. Brake stability (debounce/hold):")
print("   brake.greater_than(100).for_at_least(100)")

# Response time: brake must respond within 500ms
brake_response_time = speed.greater_than(80).implies(
    brake.greater_than(0).within(500)
).always()
print("\n4. Brake response time (temporal):")
print("   speed.greater_than(80).implies(")
print("       brake.greater_than(0).within(500)")
print("   ).always()")

# Complex: multiple conditions combined
from aletheia import Signal
accel = Signal("Acceleration")
safe_decel = speed.greater_than(100).implies(
    accel.less_than(0).within(1000)
).always()
print("\n5. Deceleration response (safety):")
print("   speed.greater_than(100).implies(")
print("       accel.less_than(0).within(1000)")
print("   ).always()")


# =============================================================================
# SUMMARY
# =============================================================================

print("\n" + "=" * 60)
print("SUMMARY")
print("=" * 60)
print("""
What you saw:
  - Load DBCs and define signals: standard Python
  - Express temporal requirements: readable, composable DSL
  - Check properties on CAN data: automatic, exhaustive
  - Get diagnostics: timestamps, violation details

Key points:
  - No sampling loops or hand-written state machines
  - No need to filter frames by CAN ID (three-valued semantics)
  - Properties are checked against the entire stream
  - The checker is proven correct (Agda core with formal proofs)
  - Python is just the interface; guarantees come from the verified core

Where this fits:
  - Offline analysis of recorded logs
  - CI/CD pipelines for regression testing
  - System testing and validation
  - Debugging timing-related issues
""")
