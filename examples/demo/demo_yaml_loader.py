#!/usr/bin/env python3
"""YAML Loader Demo

Load signal checks from a YAML file — version-controllable, CI/CD-friendly
check definitions without writing Python.

No FFI or Agda build required — this demo only generates formulas.
"""

import json
from pathlib import Path

from aletheia import Check, load_checks


# =============================================================================
# SECTION 1: Load Checks from File
# =============================================================================

print("=" * 60)
print("SECTION 1: Load Checks from File")
print("=" * 60)

yaml_path = Path(__file__).parent / "demo_checks.yaml"
checks = load_checks(yaml_path)

print(f"\nLoaded {len(checks)} checks from {yaml_path.name}")

for i, check in enumerate(checks, 1):
    name = check.name or "<unnamed>"
    sev = check.check_severity or "-"
    print(f"\n  {i}. {name} [{sev}]")
    print(f"     {json.dumps(check.to_dict(), separators=(',', ':'))[:80]}...")


# =============================================================================
# SECTION 2: Inline YAML
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 2: Inline YAML")
print("=" * 60)

inline_checks = load_checks("""
checks:
  - name: "Quick speed check"
    signal: VehicleSpeed
    condition: never_exceeds
    value: 200
    severity: critical
""")

print(f"\nLoaded {len(inline_checks)} check(s) from inline YAML")
print(f"  Name: {inline_checks[0].name}")
print(f"  Severity: {inline_checks[0].check_severity}")
print(f"  Formula:\n{json.dumps(inline_checks[0].to_dict(), indent=2)}")


# =============================================================================
# SECTION 3: Equivalence with Check API
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 3: Equivalence with Check API")
print("=" * 60)

yaml_speed = checks[0].to_dict()
api_speed = Check.signal("VehicleSpeed").never_exceeds(220).to_dict()
print(f"\n  YAML 'Speed limit' == Check API: {yaml_speed == api_speed}")

yaml_brake = checks[6].to_dict()
api_brake = (
    Check.when("BrakePedal").exceeds(50)
    .then("BrakeLight").equals(1)
    .within(100)
    .to_dict()
)
print(f"  YAML 'Brake light response' == Check API: {yaml_brake == api_brake}")


# =============================================================================
# SECTION 4: YAML Schema Reference
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 4: YAML Schema Reference")
print("=" * 60)

print("""
Simple check:
  checks:
    - name: "..."
      signal: SignalName
      condition: never_exceeds | never_below | stays_between |
                 never_equals | equals | settles_between
      value: 220               # for value-based conditions
      min: 11.5                # for range-based conditions
      max: 14.5
      within_ms: 5000          # for settles_between
      severity: critical       # optional

When/Then check:
  checks:
    - name: "..."
      when:
        signal: BrakePedal
        condition: exceeds | equals | drops_below
        value: 50
      then:
        signal: BrakeLight
        condition: equals | exceeds | stays_between
        value: 1
      within_ms: 100
      severity: safety""")


# =============================================================================
# DONE
# =============================================================================

print("\n" + "=" * 60)
print("DONE")
print("=" * 60)
