#!/usr/bin/env python3
"""Aletheia Demo — Verified CAN Signal Analysis

Sections:
    1. Integration    — load DBC, define signals
    2. Properties     — express temporal requirements via DSL
    3. Verification   — stream a normal drive log
    4. Fault injection — detect an overspeed event
    5. Diagnostics    — inspect violation details
    6. More examples  — additional property patterns

Requirements:
    - Aletheia built: `cabal run shake -- build`
    - Run from the examples/demo directory
"""

import json
from pathlib import Path

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json
from drive_log import NORMAL_DRIVE, OVERSPEED_DRIVE


# =============================================================================
# SECTION 1: Integration — Load DBC and Define Signals
# =============================================================================

print("=" * 60)
print("SECTION 1: Integration")
print("=" * 60)

dbc_path = Path(__file__).parent / "vehicle.dbc"
dbc = dbc_to_json(str(dbc_path))

print(f"\nLoaded DBC: {dbc['version']}")
print(f"Messages: {[m['name'] for m in dbc['messages']]}")

speed = Signal("VehicleSpeed")
brake = Signal("BrakePressure")

print(f"\nSignals:")
print(f"  - {speed.name} (from VehicleDynamics)")
print(f"  - {brake.name} (from BrakeStatus)")


# =============================================================================
# SECTION 2: Properties — Temporal Requirements
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 2: Properties")
print("=" * 60)

# Safety property: speed limit
speed_limit = speed.less_than(120).always()

print("\nProperty 1 — Speed limit:")
print("  speed.less_than(120).always()")

# Temporal property: brake response time
brake_response = speed.greater_than(80).implies(
    brake.greater_than(0).within(500)
).always()

print("\nProperty 2 — Brake response:")
print("  speed.greater_than(80).implies(")
print("      brake.greater_than(0).within(500)")
print("  ).always()")

print("\nSerialized to JSON:")
print(json.dumps(speed_limit.to_dict(), indent=2))


# =============================================================================
# SECTION 3: Verification — Normal Drive
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 3: Verification — Normal Drive")
print("=" * 60)

print(f"\nDrive log: {len(NORMAL_DRIVE)} frames, {NORMAL_DRIVE[-1].timestamp_ms}ms")
print("Checking: speed < 120 always")

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([speed_limit.to_dict()])
    client.start_stream()

    violations = []
    for frame in NORMAL_DRIVE:
        response = client.send_frame(frame.timestamp_us, frame.can_id, frame.data)
        if response.get("status") == "violation":
            violations.append(response)

    client.end_stream()

if not violations:
    print("\n  PASS — speed never exceeded 120 kph")
else:
    print(f"\n  FAIL — {len(violations)} violation(s)")


# =============================================================================
# SECTION 4: Fault Injection — Overspeed Event
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 4: Fault Injection — Overspeed Event")
print("=" * 60)

print(f"\nOverspeed drive log: {len(OVERSPEED_DRIVE)} frames")
print("Checking: speed < 120 always")

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([speed_limit.to_dict()])
    client.start_stream()

    violations = []
    for frame in OVERSPEED_DRIVE:
        response = client.send_frame(frame.timestamp_us, frame.can_id, frame.data)
        if response.get("status") == "violation":
            violations.append(response)

    client.end_stream()

if violations:
    print(f"\n  FAIL — {len(violations)} violation(s) detected")
else:
    print("\n  PASS (unexpected)")


# =============================================================================
# SECTION 5: Diagnostics — Violation Details
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 5: Diagnostics")
print("=" * 60)

if violations:
    for i, v in enumerate(violations[:3], 1):
        ts = v.get("timestamp", {})
        ts_us = ts.get("numerator", 0) if isinstance(ts, dict) else 0
        print(f"\n  Violation {i}:")
        print(f"    Timestamp: {ts_us // 1000}ms")
        print(f"    Property:  {v.get('property_index', {})}")
        if "reason" in v:
            print(f"    Reason:    {v['reason']}")

    if len(violations) > 3:
        print(f"\n  ... and {len(violations) - 3} more")


# =============================================================================
# SECTION 6: More Property Patterns
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 6: More Property Patterns")
print("=" * 60)

print("\n1. Absolute speed limit:")
print("   speed.less_than(200).always()")

print("\n2. Sensor range validity:")
print("   brake.between(0, 10000).always()")

print("\n3. Brake hold (debounce):")
print("   brake.greater_than(100).for_at_least(100)")

print("\n4. Brake response time:")
print("   speed.greater_than(80).implies(")
print("       brake.greater_than(0).within(500)")
print("   ).always()")

accel = Signal("Acceleration")
print("\n5. Deceleration response:")
print("   speed.greater_than(100).implies(")
print("       accel.less_than(0).within(1000)")
print("   ).always()")


# =============================================================================
# DONE
# =============================================================================

print("\n" + "=" * 60)
print("DONE")
print("=" * 60)
