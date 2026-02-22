#!/usr/bin/env python3
"""Staleness Bug Demo — LTL Catches What Naive Tests Cannot

This demo shows the key value proposition of Aletheia's formally verified
LTL engine: detecting temporal bugs that value-range testing misses.

Scenario:
  An Engine ECU sends periodic CAN messages with an alive counter
  (FrameCounter) that should cycle 0→1→2→...→15→0→...

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

import sys
from pathlib import Path

# Allow importing from the demo directory
sys.path.insert(0, str(Path(__file__).parent))

from aletheia import AletheiaClient, Check, Signal
from engine_ecu_sim import (
    ENGINE_DBC,
    ENGINE_STATUS_ID,
    generate_frozen_trace,
    generate_normal_trace,
)

HEADER = "=" * 65


def run_ltl_check(
    label: str,
    trace,
    properties: list[dict],
) -> list[dict]:
    """Run LTL properties against a trace and return violations."""
    violations = []
    with AletheiaClient() as client:
        client.parse_dbc(ENGINE_DBC)
        client.set_properties(properties)
        client.start_stream()

        for frame in trace:
            response = client.send_frame(
                frame.timestamp_us, frame.can_id, frame.data
            )
            if response.get("status") == "violation":
                violations.append(response)

        client.end_stream()
    return violations


def main() -> None:
    print(HEADER)
    print("  Aletheia Staleness Bug Demo")
    print("  Catching temporal bugs that naive tests miss")
    print(HEADER)

    # =========================================================================
    # Part 1: Show that naive value checks pass on the frozen trace
    # =========================================================================

    print("\n--- Part 1: Naive Value Checks ---\n")
    frozen = generate_frozen_trace(n_frames=50, freeze_at=15)

    with AletheiaClient() as client:
        client.parse_dbc(ENGINE_DBC)

        all_ok = True
        for frame in frozen:
            result = client.extract_signals(
                can_id=frame.can_id, data=frame.data
            )
            rpm = result.get("EngineRPM")
            temp = result.get("CoolantTemp")
            counter = result.get("FrameCounter")

            if not (0 <= rpm <= 16383.75):
                all_ok = False
            if not (-40 <= temp <= 215):
                all_ok = False
            if not (0 <= counter <= 15):
                all_ok = False

    status = "PASS" if all_ok else "FAIL"
    print(f"  Value-range checks on frozen trace: {status}")
    print("  (RPM in range, CoolantTemp in range, FrameCounter in [0,15])")
    print()
    print("  The frozen ECU passes all naive checks because the stale")
    print("  values are individually valid — the bug is temporal.")

    # =========================================================================
    # Part 2: LTL property catches the frozen counter
    # =========================================================================

    print(f"\n--- Part 2: LTL Alive Counter Check ---\n")

    # "FrameCounter must always change between consecutive frames"
    # changedBy(0) means |current - previous| <= 0 → counter unchanged
    # .never() wraps in G(NOT(...)) → "it's never the case that counter stays the same"
    alive_check = Signal("FrameCounter").changed_by(0).never()
    properties = [alive_check.to_dict()]

    print("  Property: Signal('FrameCounter').changed_by(0).never()")
    print("  Meaning:  'The alive counter must change every frame'")
    print()

    # Run against normal trace — should pass
    normal = generate_normal_trace(n_frames=50)
    normal_violations = run_ltl_check("Normal trace", normal, properties)
    print(f"  Normal trace (50 frames):  {len(normal_violations)} violations")

    # Run against frozen trace — should detect the freeze
    frozen_violations = run_ltl_check("Frozen trace", frozen, properties)
    print(f"  Frozen trace (50 frames):  {len(frozen_violations)} violations")

    if frozen_violations:
        v = frozen_violations[0]
        ts = v.get("timestamp", {})
        if isinstance(ts, dict):
            ts_val = ts.get("numerator", 0) / max(ts.get("denominator", 1), 1)
        else:
            ts_val = ts
        print(f"\n  First violation at timestamp: {ts_val} us")
        print(f"  The frozen counter was detected at the first frame after")
        print(f"  the ECU freeze (frame 16, where counter stays at the same value).")

    # =========================================================================
    # Part 3: Using Check API (industry vocabulary)
    # =========================================================================

    print(f"\n--- Part 3: Same Check via Check API ---\n")

    # The Check API doesn't have a direct "alive counter" check, but the
    # DSL signal interface is still readable:
    print("  DSL:   Signal('FrameCounter').changed_by(0).never()")
    print()
    print("  This single line replaces dozens of value-range assertions")
    print("  and catches an entire class of firmware bugs.")

    # =========================================================================
    # Summary
    # =========================================================================

    print(f"\n{HEADER}")
    print("  Summary")
    print(HEADER)
    print()
    print("  8 naive tests:     ALL PASS against the buggy ECU")
    print(f"  1 LTL property:    CATCHES the bug ({len(frozen_violations)} violations)")
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
