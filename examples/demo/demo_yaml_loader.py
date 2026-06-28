# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""YAML Loader Demo.

Load signal checks from a YAML file — version-controllable, CI/CD-friendly
check definitions without writing Python.

Decimal values are parsed exactly by the verified Agda kernel (the float
principle: a decimal is an exact rational, never a lossy float), so a live client
must be up while loading — hence the ``with AletheiaClient()`` blocks below. Build
the library first: ``cabal run shake -- build``.
"""

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

from pathlib import Path

from aletheia import AletheiaClient, load_checks
from aletheia.checks import signal, when
from aletheia.types import dump_json

# =============================================================================
# SECTION 1: Load Checks from File
# =============================================================================

print("=" * 60)
print("SECTION 1: Load Checks from File")
print("=" * 60)

yaml_path = Path(__file__).parent / "demo_checks.yaml"
# A live client brings up the verified kernel that parses the file's decimal
# values exactly — decimal parsing is RTS-gated.
with AletheiaClient():
    checks = load_checks(yaml_path)

print(f"\nLoaded {len(checks)} checks from {yaml_path.name}")

for i, check in enumerate(checks, 1):
    name = check.name or "<unnamed>"
    sev = check.check_severity or "-"
    print(f"\n  {i}. {name} [{sev}]")
    print(f"     {dump_json(check.to_dict())[:80]}...")


# =============================================================================
# SECTION 2: Inline YAML
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 2: Inline YAML")
print("=" * 60)

with AletheiaClient():
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
print(f"  Formula:\n{dump_json(inline_checks[0].to_dict(), indent=2)}")


# =============================================================================
# SECTION 3: Equivalence with Check API
# =============================================================================

print("\n" + "=" * 60)
print("SECTION 3: Equivalence with Check API")
print("=" * 60)

yaml_speed = checks[0].to_dict()
api_speed = signal("VehicleSpeed").never_exceeds(220).to_dict()
print(f"\n  YAML 'Speed limit' == Check API: {yaml_speed == api_speed}")

yaml_brake = checks[6].to_dict()
api_brake = when("BrakePedal").exceeds(50).then("BrakeLight").equals(1).within(100).to_dict()
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
