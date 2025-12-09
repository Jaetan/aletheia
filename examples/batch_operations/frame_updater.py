#!/usr/bin/env python3
"""
Frame Updater Example

Demonstrates updating specific signals in existing CAN frames.

This example shows:
- Updating individual signals in a frame
- Updating multiple signals at once
- Verifying updates
- Preserving unchanged signals
- Processing frame sequences

Usage:
    python3 frame_updater.py
"""

from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "python"))

from aletheia import SignalExtractor, FrameBuilder
from aletheia.dbc_converter import dbc_to_json


def print_frame_signals(extractor, can_id, frame, label):
    """Helper to print all signals in a frame"""
    result = extractor.extract(can_id=can_id, data=frame)
    print(f"\n   {label}:")
    for name, value in sorted(result.values.items()):
        print(f"   - {name:20s}: {value:8.2f}")


def main():
    print("=" * 70)
    print("Frame Updater Example")
    print("=" * 70)

    # Load DBC file
    dbc_path = Path(__file__).parent.parent / "example.dbc"
    print(f"\n1. Loading DBC file: {dbc_path}")

    try:
        dbc = dbc_to_json(dbc_path)
        print("   ✓ DBC loaded successfully")
    except FileNotFoundError:
        print(f"   ✗ DBC file not found: {dbc_path}")
        return 1
    except Exception as e:
        print(f"   ✗ Failed to load DBC: {e}")
        return 1

    # Create initial frame
    print("\n2. Creating initial frame")

    with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
        original_frame = (builder
            .set("EngineSpeed", 2000)
            .set("EngineTemp", 85)
            .set("Throttle", 50)
            .build())

    print(f"   Original frame: {[f'0x{b:02X}' for b in original_frame]}")

    # Display original signals
    with SignalExtractor(dbc=dbc) as extractor:
        print_frame_signals(extractor, 0x100, original_frame, "Original signals")

    # Update a single signal
    print("\n3. Updating single signal (EngineSpeed: 2000 → 2500)")

    with SignalExtractor(dbc=dbc) as extractor:
        # Update only EngineSpeed, leave others unchanged
        updated_frame = extractor.update(
            can_id=0x100,
            frame=original_frame,
            signals={"EngineSpeed": 2500}
        )

        print(f"   Updated frame: {[f'0x{b:02X}' for b in updated_frame]}")

        # Verify the update
        result = extractor.extract(can_id=0x100, data=updated_frame)

        print("\n   Verification:")
        print(f"   - EngineSpeed: {result.get('EngineSpeed')} (✓ updated)")
        print(f"   - EngineTemp:  {result.get('EngineTemp')} (✓ unchanged)")
        print(f"   - Throttle:    {result.get('Throttle')} (✓ unchanged)")

    # Update multiple signals
    print("\n4. Updating multiple signals")

    with SignalExtractor(dbc=dbc) as extractor:
        updated_frame = extractor.update(
            can_id=0x100,
            frame=original_frame,
            signals={
                "EngineSpeed": 3000,
                "EngineTemp": 95,
                "Throttle": 75
            }
        )

        print(f"   Updated frame: {[f'0x{b:02X}' for b in updated_frame]}")

        # Show before and after
        print_frame_signals(extractor, 0x100, original_frame, "Before update")
        print_frame_signals(extractor, 0x100, updated_frame, "After update")

    # Demonstrate immutability
    print("\n5. Demonstrating immutability")

    with SignalExtractor(dbc=dbc) as extractor:
        # Original frame is unchanged by update()
        updated_frame = extractor.update(
            can_id=0x100,
            frame=original_frame,
            signals={"EngineSpeed": 9999}
        )

        # Extract from both frames
        original_result = extractor.extract(can_id=0x100, data=original_frame)
        updated_result = extractor.extract(can_id=0x100, data=updated_frame)

        print(f"   Original frame EngineSpeed: {original_result.get('EngineSpeed')}")
        print(f"   Updated frame EngineSpeed:  {updated_result.get('EngineSpeed')}")
        print("\n   ✓ Original frame unchanged (immutability preserved)")

    # Process a sequence of frames
    print("\n6. Processing frame sequence")
    print("   Scenario: Increase engine speed gradually over 10 frames")

    # Create initial frame sequence
    with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
        initial_frame = (builder
            .set("EngineSpeed", 1000)
            .set("EngineTemp", 80)
            .set("Throttle", 30)
            .build())

    print(f"\n   Starting frame: EngineSpeed = 1000 RPM")

    # Update sequence
    frames = [initial_frame]

    with SignalExtractor(dbc=dbc) as extractor:
        current_frame = initial_frame

        for i in range(1, 10):
            # Increase speed by 200 RPM each frame
            new_speed = 1000 + i * 200

            current_frame = extractor.update(
                can_id=0x100,
                frame=current_frame,
                signals={"EngineSpeed": new_speed}
            )

            frames.append(current_frame)

        print(f"   ✓ Generated sequence of {len(frames)} frames")

        # Verify sequence
        print("\n   Frame sequence:")
        for i, frame in enumerate(frames):
            result = extractor.extract(can_id=0x100, data=frame)
            speed = result.get("EngineSpeed")
            temp = result.get("EngineTemp")
            throttle = result.get("Throttle")
            print(f"   Frame {i:2d}: Speed={speed:5.0f} RPM, "
                  f"Temp={temp:4.0f}°C, Throttle={throttle:4.0f}%")

    # Simulate trace file modification
    print("\n7. Simulating trace file modification")
    print("   Scenario: Update EngineSpeed to 2000 in all frames of a trace")

    # Create sample trace
    trace = []
    with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
        for i in range(5):
            frame = (builder
                .set("EngineSpeed", 1000 + i * 300)
                .set("EngineTemp", 85 + i * 2)
                .set("Throttle", 40 + i * 5)
                .build())
            trace.append((i, 0x100, frame))

    print(f"\n   Original trace ({len(trace)} frames):")

    # Process trace
    modified_trace = []

    with SignalExtractor(dbc=dbc) as extractor:
        # Show original
        for frame_num, can_id, frame in trace:
            result = extractor.extract(can_id=can_id, data=frame)
            speed = result.get("EngineSpeed")
            print(f"   Frame {frame_num}: EngineSpeed = {speed:.0f} RPM")

        print("\n   Updating all frames to EngineSpeed = 2000 RPM...")

        # Update all frames
        for frame_num, can_id, frame in trace:
            updated_frame = extractor.update(
                can_id=can_id,
                frame=frame,
                signals={"EngineSpeed": 2000}
            )
            modified_trace.append((frame_num, can_id, updated_frame))

        # Show modified
        print(f"\n   Modified trace ({len(modified_trace)} frames):")
        for frame_num, can_id, frame in modified_trace:
            result = extractor.extract(can_id=can_id, data=frame)
            speed = result.get("EngineSpeed")
            temp = result.get("EngineTemp")
            throttle = result.get("Throttle")
            print(f"   Frame {frame_num}: Speed={speed:.0f} RPM "
                  f"(Temp={temp:.0f}°C, Throttle={throttle:.0f}% unchanged)")

    print("\n" + "=" * 70)
    print("Example completed successfully!")
    print("=" * 70)
    print("\nKey Takeaways:")
    print("- update() is immutable - returns new frame, original unchanged")
    print("- Can update single or multiple signals at once")
    print("- Unchanged signals preserve their original values")
    print("- Subprocess reused for efficient batch updates")
    print("- Perfect for modifying trace files or creating test sequences")
    print("\nNext Steps:")
    print("- Try multiplexed_signals.py for multiplexing examples")
    print("- See batch_trace_processing.py for full trace workflows")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
