#!/usr/bin/env python3
"""Frame Injection Demo

This script demonstrates Aletheia's capability to detect property violations
when CAN frames are modified mid-stream. The scenario:

1. Load a normal drive log that passes the speed limit property
2. Catch the 15th speed frame (around the middle of the drive)
3. Inject a modified value (speed = 130 kph, exceeding the 120 limit)
4. Verify that Aletheia detects the violation at the exact frame

This is useful for:
- Fault injection testing
- Verifying that safety monitors catch anomalies
- Testing edge cases without physical hardware
- Debugging by isolating specific frames

Requirements:
- Aletheia binary must be built: `cabal run shake -- build`
"""

from pathlib import Path

from aletheia import Signal, StreamingClient, SignalExtractor
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

    # First, verify the normal drive passes
    print("\n" + "-" * 70)
    print("STEP 1: Verify normal drive passes the property")
    print("-" * 70)

    print(f"\nDrive log: {len(NORMAL_DRIVE)} frames")

    with StreamingClient() as client:
        client.parse_dbc(dbc)
        client.set_properties([speed_limit.to_dict()])
        client.start_stream()

        for frame in NORMAL_DRIVE:
            response = client.send_frame(frame.timestamp_us, frame.can_id, frame.data)
            if response.get("status") == "violation":
                print(f"Unexpected violation at frame {frame.timestamp_ms}ms")
                return

        client.end_stream()

    print("Result: Property HOLDS on normal drive")

    # Now, inject a fault at a specific frame
    print("\n" + "-" * 70)
    print("STEP 2: Inject overspeed fault at frame #15 (speed frames only)")
    print("-" * 70)

    # Find the 15th speed frame
    speed_frame_count = 0
    target_frame_index = None
    target_speed_frame_num = 15

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
    print(f"\nTarget: Frame #{target_frame_index} at {original_frame.timestamp_ms}ms")
    print(f"Original data: {[f'0x{b:02X}' for b in original_frame.data]}")

    # Extract original speed value
    with SignalExtractor(dbc=dbc) as extractor:
        original_result = extractor.extract(
            can_id=original_frame.can_id,
            data=list(original_frame.data)
        )
        original_speed = original_result.get("VehicleSpeed", 0.0)
        print(f"Original VehicleSpeed: {original_speed:.1f} kph")

        # Inject overspeed value (130 kph, exceeding 120 limit)
        injected_speed = 130.0
        modified_data = extractor.update(
            can_id=original_frame.can_id,
            frame=list(original_frame.data),
            signals={"VehicleSpeed": injected_speed}
        )

        print(f"\nInjecting VehicleSpeed: {injected_speed:.1f} kph")
        print(f"Modified data: {[f'0x{b:02X}' for b in modified_data]}")

        # Verify the injection
        verify_result = extractor.extract(
            can_id=original_frame.can_id,
            data=modified_data
        )
        verify_speed = verify_result.get("VehicleSpeed", 0.0)
        print(f"Verified injected speed: {verify_speed:.1f} kph")

    # Now stream with the modified frame
    print("\n" + "-" * 70)
    print("STEP 3: Stream with injected fault and detect violation")
    print("-" * 70)

    with StreamingClient() as client:
        client.parse_dbc(dbc)
        client.set_properties([speed_limit.to_dict()])
        client.start_stream()

        violations = []
        for i, frame in enumerate(NORMAL_DRIVE):
            # Use modified data for the target frame
            if i == target_frame_index:
                data = modified_data
                print(f"\n  [Frame {i}] Injecting modified frame at {frame.timestamp_ms}ms")
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
                print(f"  [Frame {i}] VIOLATION DETECTED at {ts_ms}ms!")

        client.end_stream()

    # Report results
    print("\n" + "-" * 70)
    print("RESULTS")
    print("-" * 70)

    if violations:
        print(f"\nViolation(s) detected: {len(violations)}")
        for v in violations:
            print(f"\n  Frame #{v['frame_index']} at {v['timestamp_ms']}ms:")
            if 'reason' in v['response']:
                print(f"    Reason: {v['response']['reason']}")

        # Verify it's at the injected frame
        if violations[0]['frame_index'] == target_frame_index:
            print("\n  Violation correctly detected at the INJECTED FRAME!")
        else:
            print(f"\n  Note: First violation at frame #{violations[0]['frame_index']}, "
                  f"injected at #{target_frame_index}")
    else:
        print("\nNo violations detected (unexpected)")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("""
What this demo showed:
  - Normal drive passes the speed limit property
  - We injected an overspeed value (130 kph) at a specific frame
  - Aletheia detected the violation at the exact injected frame

Use cases:
  - Fault injection testing without physical hardware
  - Regression testing: inject known faults and verify detection
  - Debugging: isolate specific frames to reproduce issues
  - Security testing: verify monitors catch malicious modifications
""")


if __name__ == "__main__":
    main()
