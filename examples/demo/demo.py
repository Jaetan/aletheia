#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Aletheia Demo — Verified CAN Signal Analysis.

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

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from drive_log import NORMAL_DRIVE, OVERSPEED_DRIVE

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json
from aletheia.protocols import DLCCode, dump_json

if TYPE_CHECKING:
    from drive_log import CANFrame

    from aletheia.protocols import PropertyResultEntry

# Number of violations shown in the diagnostics section before eliding the rest.
_MAX_SHOWN = 3


def run_verification(
    stream_client: AletheiaClient, frames: list[CANFrame]
) -> list[PropertyResultEntry]:
    """Stream ``frames`` and return the per-frame property-violation entries.

    Each ``send_frame`` returns an ack, an error, or a property batch; only the
    batch carries ``results``, and a ``status == "fails"`` entry is a violation.
    """
    results: list[PropertyResultEntry] = []
    for frame in frames:
        response = stream_client.send_frame(
            timestamp=frame.timestamp_us,
            can_id=frame.can_id,
            dlc=DLCCode(len(frame.data)),
            data=frame.data,
        )
        if "results" in response:
            results.extend(e for e in response["results"] if e["status"] == "fails")
    return results


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

print("\nSignals:")
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
brake_response = speed.greater_than(80).implies(brake.greater_than(0).within(500)).always()

print("\nProperty 2 — Brake response:")
print("  speed.greater_than(80).implies(")
print("      brake.greater_than(0).within(500)")
print("  ).always()")

print("\nSerialized to JSON:")
print(dump_json(speed_limit.to_dict(), indent=2))


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
    violations = run_verification(client, NORMAL_DRIVE)
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
    violations = run_verification(client, OVERSPEED_DRIVE)
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
    for i, v in enumerate(violations[:_MAX_SHOWN], 1):
        ts = v.get("timestamp")
        ts_us = ts["numerator"] if ts is not None else 0
        print(f"\n  Violation {i}:")
        print(f"    Timestamp: {ts_us // 1000}ms")
        print(f"    Property:  {v['property_index']['numerator']}")
        reason = v.get("reason")
        if reason is not None:
            print(f"    Reason:    {reason}")

    if len(violations) > _MAX_SHOWN:
        print(f"\n  ... and {len(violations) - _MAX_SHOWN} more")


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
