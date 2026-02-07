#!/usr/bin/env python3
"""YAML Loader Demo

Load signal checks from a YAML file — the preferred format for
test engineers who want version-controllable, CI/CD-friendly check
definitions without writing Python.

No FFI or Agda build required — this demo only generates formulas.
"""

import json
import sys
from pathlib import Path

# Allow running from examples/demo/ or project root
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "python"))

from aletheia import Check, load_checks


# =============================================================================
# SECTION 1: Load Checks from File
# =============================================================================

print("=" * 70)
print("YAML LOADER — Declarative Check Definitions")
print("=" * 70)

print("""
YAML files let test engineers define checks in a declarative format:
- Version-controllable (git diff friendly)
- CI/CD integration (run checks as part of build pipeline)
- No Python scripting required
""")

print("-" * 70)
print("SECTION 1: Load Checks from File")
print("-" * 70)

yaml_path = Path(__file__).parent / "demo_checks.yaml"
checks = load_checks(yaml_path)

print(f"\nLoaded {len(checks)} checks from {yaml_path.name}")

for i, check in enumerate(checks, 1):
    name = check.name or "<unnamed>"
    sev = check.check_severity or "-"
    print(f"\n  {i}. {name}")
    print(f"     Severity: {sev}")
    print(f"     Formula:  {json.dumps(check.to_dict(), separators=(',', ':'))[:80]}...")


# =============================================================================
# SECTION 2: Inline YAML
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 2: Inline YAML")
print("-" * 70)

print("""
For quick scripting, load_checks() also accepts YAML strings directly:
""")

inline_checks = load_checks("""
checks:
  - name: "Quick speed check"
    signal: VehicleSpeed
    condition: never_exceeds
    value: 200
    severity: critical
""")

print(f"  Loaded {len(inline_checks)} check(s) from inline YAML")
print(f"  Name: {inline_checks[0].name}")
print(f"  Severity: {inline_checks[0].check_severity}")
print(f"  Formula: {json.dumps(inline_checks[0].to_dict(), indent=2)}")


# =============================================================================
# SECTION 3: Equivalence with Check API
# =============================================================================

print("\n" + "-" * 70)
print("SECTION 3: Equivalence with Check API")
print("-" * 70)

print("""
YAML checks compile through the same Check API. The formulas are identical:
""")

# Compare first check: speed limit
yaml_speed = checks[0].to_dict()
api_speed = Check.signal("VehicleSpeed").never_exceeds(220).to_dict()
print(f"  YAML 'Speed limit' == Check API: {yaml_speed == api_speed}")

# Compare when/then check: brake light response
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

print("\n" + "-" * 70)
print("SECTION 4: YAML Schema Reference")
print("-" * 70)

print("""
Simple check schema:
  checks:
    - name: "..."               # optional
      signal: SignalName
      condition: never_exceeds  # never_exceeds | never_below |
                                # stays_between | never_equals |
                                # equals | settles_between
      value: 220                # for value-based conditions
      min: 11.5                 # for range-based conditions
      max: 14.5
      within_ms: 5000           # required for settles_between
      severity: critical        # optional

When/Then check schema:
  checks:
    - name: "..."
      when:
        signal: BrakePedal
        condition: exceeds      # exceeds | equals | drops_below
        value: 50
      then:
        signal: BrakeLight
        condition: equals       # equals | exceeds | stays_between
        value: 1
      within_ms: 100
      severity: safety
""")


# =============================================================================
# SUMMARY
# =============================================================================

print("=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
The YAML loader provides:
  - File-based check definitions for version control
  - Inline YAML strings for scripting
  - Same 6 simple conditions and 3 when/then patterns as the Check API
  - Metadata (name, severity) for reporting
  - Identical output to the Check API and raw DSL

Workflow:
  1. Define checks in a .yaml file
  2. Load with load_checks("checks.yaml")
  3. Pass to client.set_properties([c.to_dict() for c in checks])
""")
