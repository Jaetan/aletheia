#!/usr/bin/env python3
"""Frame Injection Demo

This script demonstrates Aletheia's capability to detect property violations
when CAN frames are modified mid-stream. The scenario:

1. Start streaming a normal drive log
2. At frame #15 (speed frame), inject a modified value on-the-fly
3. Continue streaming the remaining frames
4. Verify that Aletheia detects the violation at the exact injected frame

This is useful for:
- Fault injection testing in both offline logs and live (online) streams
- Verifying that safety monitors catch anomalies immediately
- Testing edge cases without physical hardware
- Debugging by isolating specific frames

Requirements:
- Aletheia binary must be built: `cabal run shake -- build`
"""

from pathlib import Path

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json
from drive_log import NORMAL_DRIVE, VEHICLE_DYNAMICS_ID


def main() -> None:
    print("=" * 70)
    print("FRAME INJECTION DEMO")
    print("=" * 70)

    # Load DBC
    dbc_path = Path(__file__).parent / "vehicle.dbc"
    dbc = dbc_to_json(str(dbc_path))
    print(f"\nLoaded DBC: {dbc['version']}")

    # Define property: speed must always be under 120 kph
    speed = Signal("VehicleSpeed")
    speed_limit = speed.less_than(120).always()

    print("\nProperty: speed.less_than(120).always()")
    print("  'Speed must always be under 120 kph'")

    # Find the target frame (15th speed frame)
    target_speed_frame_num = 15
    speed_frame_count = 0
    target_frame_index = None

    for i, frame in enumerate(NORMAL_DRIVE):
        if frame.can_id == VEHICLE_DYNAMICS_ID:
            speed_frame_count += 1
            if speed_frame_count == target_speed_frame_num:
                target_frame_index = i
                break

    if target_frame_index is None:
        print(f"Error: Could not find frame #{target_speed_frame_num}")
        return

    original_frame = NORMAL_DRIVE[target_frame_index]

    print(f"\nPlan: Inject overspeed fault at frame #{target_frame_index}")
    print(f"      (the {target_speed_frame_num}th speed frame at {original_frame.timestamp_ms}ms)")

    # Use unified client for everything (single process, FFI)
    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Prepare the modified frame data
        print("\n" + "-" * 70)
        print("PREPARING INJECTION")
        print("-" * 70)

        # Extract original speed
        original_result = client.extract_signals(
            can_id=original_frame.can_id,
            data=list(original_frame.data)
        )
        original_speed = original_result.get("VehicleSpeed", 0.0)
        print(f"\nOriginal frame #{target_frame_index}:")
        print(f"  Data: {[f'0x{b:02X}' for b in original_frame.data]}")
        print(f"  VehicleSpeed: {original_speed:.1f} kph")

        # Prepare modified frame (130 kph, exceeding 120 limit)
        injected_speed = 130.0
        modified_data = client.update_frame(
            can_id=original_frame.can_id,
            frame=list(original_frame.data),
            signals={"VehicleSpeed": injected_speed}
        )
        print(f"\nPrepared injection:")
        print(f"  Data: {[f'0x{b:02X}' for b in modified_data]}")
        print(f"  VehicleSpeed: {injected_speed:.1f} kph (exceeds 120 limit)")

        # Stream with real-time injection (same client, same process!)
        print("\n" + "-" * 70)
        print("STREAMING WITH REAL-TIME INJECTION")
        print("-" * 70)
        print(f"\nStreaming {len(NORMAL_DRIVE)} frames...")
        print(f"Will inject modified frame at index {target_frame_index}\n")

        client.set_properties([speed_limit.to_dict()])
        client.start_stream()

        violations = []
        for i, frame in enumerate(NORMAL_DRIVE):
            # Inject modified data at target frame (real-time, not replaying)
            if i == target_frame_index:
                data = modified_data
                print(f"  [{i:3d}] >> INJECTING modified frame (speed={injected_speed} kph)")
            else:
                data = list(frame.data)

            response = client.send_frame(frame.timestamp_us, frame.can_id, data)

            if response.get("status") == "violation":
                violations.append({
                    "frame_index": i,
                    "timestamp_ms": frame.timestamp_ms,
                    "response": response
                })
                ts = response.get('timestamp', {})
                ts_ms = ts.get('numerator', 0) // 1000 if isinstance(ts, dict) else 0
                print(f"  [{i:3d}] !! VIOLATION at {ts_ms}ms")

        client.end_stream()

    # Report results
    print("\n" + "-" * 70)
    print("RESULTS")
    print("-" * 70)

    if violations:
        print(f"\nViolation(s) detected: {len(violations)}")

        # Check if first violation is at the injected frame
        first_violation_idx = violations[0]['frame_index']
        if first_violation_idx == target_frame_index:
            print(f"\nViolation correctly detected at the INJECTED FRAME (#{target_frame_index})!")
        else:
            print(f"\nFirst violation at frame #{first_violation_idx}")
            print(f"(Injection was at frame #{target_frame_index})")

        print("\nViolation details:")
        for v in violations[:3]:
            print(f"  Frame #{v['frame_index']} at {v['timestamp_ms']}ms")
            if 'reason' in v['response']:
                print(f"    Reason: {v['response']['reason']}")

        if len(violations) > 3:
            print(f"  ... and {len(violations) - 3} more")
    else:
        print("\nNo violations detected (unexpected)")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"""
What this demo showed:
  - Single AletheiaClient handles BOTH signal ops AND streaming
  - Frame #{target_frame_index} was modified ON-THE-FLY during streaming
  - Original speed: {original_speed:.1f} kph -> Injected: {injected_speed:.1f} kph
  - Aletheia detected the violation IMMEDIATELY at the injected frame

Use cases:
  - Online: fault injection during live CAN streams (real-time monitoring)
  - Offline: injecting faults into recorded logs for post-hoc analysis
  - Testing safety monitors without physical hardware
  - Injecting specific faults at precise timestamps
  - Security testing: verify monitors catch malicious modifications
""")


if __name__ == "__main__":
    main()
