#!/usr/bin/env python3
"""Frame Injection Demo

Injects a modified CAN frame mid-stream and verifies that Aletheia
detects the violation at the exact injected frame.

Requirements:
    - Aletheia built: `cabal run shake -- build`
    - Run from the examples/demo directory
"""

from pathlib import Path

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json
from drive_log import NORMAL_DRIVE, VEHICLE_DYNAMICS_ID


def main() -> None:
    print("=" * 60)
    print("FRAME INJECTION DEMO")
    print("=" * 60)

    # Load DBC and define property
    dbc_path = Path(__file__).parent / "vehicle.dbc"
    dbc = dbc_to_json(str(dbc_path))

    speed = Signal("VehicleSpeed")
    speed_limit = speed.less_than(120).always()

    print(f"\nDBC: {dbc['version']}")
    print("Property: speed.less_than(120).always()")

    # Find the 15th speed frame as injection target
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

    # =================================================================
    # PREPARING INJECTION
    # =================================================================

    print("\n" + "=" * 60)
    print("PREPARING INJECTION")
    print("=" * 60)

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Extract original speed
        original_result = client.extract_signals(
            can_id=original_frame.can_id,
            data=original_frame.data,
        )
        original_speed = original_result.get("VehicleSpeed", 0.0)
        print(f"\n  Frame #{target_frame_index} at {original_frame.timestamp_ms}ms")
        print(f"  Original speed: {original_speed:.1f} kph")

        # Build modified frame (130 kph, exceeds 120 limit)
        injected_speed = 130.0
        modified_data = client.update_frame(
            can_id=original_frame.can_id,
            frame=original_frame.data,
            signals={"VehicleSpeed": injected_speed},
        )
        print(f"  Injected speed: {injected_speed:.1f} kph")

        # =============================================================
        # STREAMING WITH INJECTION
        # =============================================================

        print("\n" + "=" * 60)
        print("STREAMING WITH INJECTION")
        print("=" * 60)

        print(f"\n  {len(NORMAL_DRIVE)} frames, injecting at index {target_frame_index}")

        client.set_properties([speed_limit.to_dict()])
        client.start_stream()

        violations = []
        for i, frame in enumerate(NORMAL_DRIVE):
            if i == target_frame_index:
                data = modified_data
                print(f"  [{i:3d}] >> INJECTING (speed={injected_speed} kph)")
            else:
                data = frame.data

            response = client.send_frame(frame.timestamp_us, frame.can_id, data)

            if response.get("status") == "violation":
                violations.append({"frame_index": i, "timestamp_ms": frame.timestamp_ms, "response": response})
                ts = response.get("timestamp", {})
                ts_ms = ts.get("numerator", 0) // 1000 if isinstance(ts, dict) else 0
                print(f"  [{i:3d}] !! VIOLATION at {ts_ms}ms")

        client.end_stream()

    # =================================================================
    # RESULTS
    # =================================================================

    print("\n" + "=" * 60)
    print("RESULTS")
    print("=" * 60)

    if violations:
        print(f"\n  {len(violations)} violation(s) detected")

        first_idx = violations[0]["frame_index"]
        if first_idx == target_frame_index:
            print(f"  First violation at injected frame #{target_frame_index}")
        else:
            print(f"  First violation at frame #{first_idx} (injection was #{target_frame_index})")

        for v in violations[:3]:
            print(f"    Frame #{v['frame_index']} at {v['timestamp_ms']}ms")
            if "reason" in v["response"]:
                print(f"      {v['response']['reason']}")

        if len(violations) > 3:
            print(f"    ... and {len(violations) - 3} more")
    else:
        print("\n  No violations detected (unexpected)")

    print("\n" + "=" * 60)
    print("DONE")
    print("=" * 60)


if __name__ == "__main__":
    main()
