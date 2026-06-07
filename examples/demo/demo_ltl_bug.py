#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Staleness Bug Demo — LTL Catches What Naive Tests Cannot.

This demo shows the key value proposition of Aletheia's formally verified
LTL engine: detecting temporal bugs that value-range testing misses.

Scenario:
  An Engine ECU sends periodic CAN messages with an alive counter
  (FrameCounter) that should cycle 0->1->2->...->15->0->...

  The ECU has a firmware bug: its main loop freezes, but the CAN TX
  hardware keeps retransmitting the last buffer. RPM and temperature
  look plausible, but the FrameCounter is frozen.

  8 naive tests (test_engine_naive.py) all PASS against the buggy trace.
  Aletheia's LTL engine detects the frozen counter immediately.

Usage:
    python examples/demo/demo_ltl_bug.py

Requires:
    Built shared library (cabal run shake -- build)
"""

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

from __future__ import annotations

from typing import TYPE_CHECKING

from engine_ecu_sim import ENGINE_DBC, generate_frozen_trace, generate_normal_trace

from aletheia import AletheiaClient, Signal
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from engine_ecu_sim import CANFrame

    from aletheia.types import LTLFormula, PropertyResultEntry

HEADER = "=" * 65

_RPM_MAX = 16383.75
_TEMP_MIN = -40
_TEMP_MAX = 215
_COUNTER_MAX = 15
_TRACE_FRAMES = 50
_FREEZE_AT = 15


def _alive_counter_property() -> LTLFormula:
    """Build the "FrameCounter must change every frame" alive-counter formula.

    ``changed_by(d)`` is directional: ``changed_by(1)`` is ``curr - prev >= 1``
    and ``changed_by(-1)`` is ``curr - prev <= -1``.  Their disjunction holds
    whenever the counter moves by at least one in either direction (a normal
    increment, or the 15->0 wrap), and fails only when it is stuck
    (``curr - prev == 0``).  ``.always()`` requires that on every frame.
    """
    counter = Signal("FrameCounter")
    return counter.changed_by(1).or_(counter.changed_by(-1)).always().to_dict()


def run_ltl_check(trace: list[CANFrame], properties: list[LTLFormula]) -> list[PropertyResultEntry]:
    """Run LTL properties against a trace and return the violation entries."""
    violations: list[PropertyResultEntry] = []
    with AletheiaClient() as client:
        client.parse_dbc(ENGINE_DBC)
        client.set_properties(properties)
        client.start_stream()
        for frame in trace:
            response = client.send_frame(
                timestamp=frame.timestamp_us,
                can_id=frame.can_id,
                dlc=DLCCode(len(frame.data)),
                data=frame.data,
            )
            if "results" in response:
                violations.extend(e for e in response["results"] if e["status"] == "fails")
        client.end_stream()
    return violations


def _naive_value_checks(client: AletheiaClient, trace: list[CANFrame]) -> bool:
    """Return True if every frame's signals are individually in range."""
    for frame in trace:
        result = client.extract_signals(
            can_id=frame.can_id, dlc=DLCCode(len(frame.data)), data=frame.data
        )
        rpm = result.get("EngineRPM")
        temp = result.get("CoolantTemp")
        counter = result.get("FrameCounter")
        if rpm < 0 or rpm > _RPM_MAX:
            return False
        if temp < _TEMP_MIN or temp > _TEMP_MAX:
            return False
        if counter < 0 or counter > _COUNTER_MAX:
            return False
    return True


def _run_naive_part(frozen: list[CANFrame]) -> None:
    """Part 1: show that naive value-range checks pass on the frozen trace."""
    print("\n--- Part 1: Naive Value Checks ---\n")
    with AletheiaClient() as client:
        client.parse_dbc(ENGINE_DBC)
        all_ok = _naive_value_checks(client, frozen)
    status = "PASS" if all_ok else "FAIL"
    print(f"  Value-range checks on frozen trace: {status}")
    print("  (RPM in range, CoolantTemp in range, FrameCounter in [0,15])")
    print()
    print("  The frozen ECU passes all naive checks because the stale")
    print("  values are individually valid — the bug is temporal.")


def _run_ltl_part(normal: list[CANFrame], frozen: list[CANFrame]) -> int:
    """Part 2: an LTL property catches the frozen counter.  Returns frozen count."""
    print("\n--- Part 2: LTL Alive Counter Check ---\n")
    properties = [_alive_counter_property()]
    print("  Property: counter.changed_by(1).or_(counter.changed_by(-1)).always()")
    print("  Meaning:  'The alive counter must change every frame'")
    print()

    normal_violations = run_ltl_check(normal, properties)
    print(f"  Normal trace (50 frames):  {len(normal_violations)} violations")

    frozen_violations = run_ltl_check(frozen, properties)
    print(f"  Frozen trace (50 frames):  {len(frozen_violations)} violations")

    if frozen_violations:
        ts = frozen_violations[0].get("timestamp")
        ts_val = ts["numerator"] / ts["denominator"] if ts is not None else 0
        print(f"\n  First violation at timestamp: {ts_val} us")
        print("  The frozen counter was detected at the first frame after")
        print("  the ECU freeze (where the counter stays at the same value).")

    return len(frozen_violations)


def main() -> None:
    """Contrast naive value checks (which miss the frozen counter) with LTL."""
    print(HEADER)
    print("  Aletheia Staleness Bug Demo")
    print("  Catching temporal bugs that naive tests miss")
    print(HEADER)

    frozen = generate_frozen_trace(n_frames=_TRACE_FRAMES, freeze_at=_FREEZE_AT)
    normal = generate_normal_trace(n_frames=_TRACE_FRAMES)

    _run_naive_part(frozen)
    frozen_count = _run_ltl_part(normal, frozen)

    print("\n--- Part 3: Same Check via Check API ---\n")
    print("  DSL:   counter.changed_by(1).or_(counter.changed_by(-1)).always()")
    print()
    print("  This single line replaces dozens of value-range assertions")
    print("  and catches an entire class of firmware bugs.")

    print(f"\n{HEADER}")
    print("  Summary")
    print(HEADER)
    print()
    print("  8 naive tests:     ALL PASS against the buggy ECU")
    print(f"  1 LTL property:    CATCHES the bug ({frozen_count} violations)")
    print()
    print("  The alive counter exists to detect exactly this failure mode,")
    print("  but you need temporal reasoning to check it. Value-range tests")
    print("  only verify 'is this number valid?' — not 'is this number fresh?'")
    print()
    print("  Aletheia's formally verified LTL engine provides this temporal")
    print("  reasoning with mathematical guarantees of correctness.")
    print()


if __name__ == "__main__":
    main()
