#!/usr/bin/env python3
"""
Signal Extractor Example

Demonstrates signal extraction from CAN frames with rich error reporting.

This example shows:
- Extracting all signals from a frame
- Handling extraction results (values/errors/absent)
- Using default values safely
- Processing multiple frames
- Error handling patterns

Usage:
    python3 signal_extractor.py
"""

from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "python"))

from aletheia import SignalExtractor, FrameBuilder
from aletheia.dbc_converter import dbc_to_json


def main():
    print("=" * 70)
    print("Signal Extractor Example")
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

    # Create a test frame
    print("\n2. Creating test frame")
    with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
        test_frame = (builder
            .set("EngineSpeed", 2500)
            .set("EngineTemp", 95)
            .set("Throttle", 80)
            .build())

    print(f"   Test frame: {[f'0x{b:02X}' for b in test_frame]}")

    # Extract all signals from the frame
    print("\n3. Extracting all signals")

    with SignalExtractor(dbc=dbc) as extractor:
        result = extractor.extract(can_id=0x100, data=test_frame)

        print(f"   ✓ Extraction complete")
        print(f"   - Successfully extracted: {len(result.values)} signals")
        print(f"   - Extraction errors: {len(result.errors)} signals")
        print(f"   - Absent (multiplexed): {len(result.absent)} signals")

        # Display extracted values
        print("\n   Extracted signal values:")
        for name, value in sorted(result.values.items()):
            print(f"   - {name:20s}: {value:8.2f}")

        # Check for errors
        if result.has_errors():
            print("\n   Extraction errors:")
            for name, error in result.errors.items():
                print(f"   - {name}: {error}")
        else:
            print("\n   ✓ No extraction errors")

        # Display absent multiplexed signals
        if result.absent:
            print("\n   Absent multiplexed signals:")
            for name in result.absent:
                print(f"   - {name}")

    # Demonstrate safe value access with defaults
    print("\n4. Safe value access with defaults")

    with SignalExtractor(dbc=dbc) as extractor:
        result = extractor.extract(can_id=0x100, data=test_frame)

        # Get values with defaults (safe even if signal missing)
        speed = result.get("EngineSpeed", default=0.0)
        temp = result.get("EngineTemp", default=20.0)
        throttle = result.get("Throttle", default=0.0)
        unknown = result.get("NonExistentSignal", default=-1.0)

        print(f"   EngineSpeed: {speed} RPM")
        print(f"   EngineTemp: {temp}°C")
        print(f"   Throttle: {throttle}%")
        print(f"   NonExistentSignal: {unknown} (default)")

    # Process multiple frames
    print("\n5. Processing multiple frames")
    print("   Creating trace of 10 frames with varying speeds...")

    frames = []
    with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
        for i in range(10):
            speed = 1000 + i * 200
            temp = 80 + i * 2
            throttle = 50 + i * 3

            frame = (builder
                .set("EngineSpeed", speed)
                .set("EngineTemp", temp)
                .set("Throttle", throttle)
                .build())

            frames.append((i, speed, temp, throttle, frame))

    print(f"   ✓ Created {len(frames)} test frames")

    # Extract signals from all frames
    print("\n   Extracting signals from all frames...")

    with SignalExtractor(dbc=dbc) as extractor:
        speeds = []
        temps = []
        throttles = []
        error_count = 0

        for frame_num, expected_speed, expected_temp, expected_throttle, frame_data in frames:
            result = extractor.extract(can_id=0x100, data=frame_data)

            if result.has_errors():
                error_count += 1
                print(f"   ✗ Frame {frame_num}: Extraction errors")
                continue

            # Collect values
            speeds.append(result.get("EngineSpeed", 0.0))
            temps.append(result.get("EngineTemp", 0.0))
            throttles.append(result.get("Throttle", 0.0))

        print(f"\n   ✓ Processed {len(frames)} frames")
        print(f"   - Successful extractions: {len(speeds)}")
        print(f"   - Errors: {error_count}")

        # Display statistics
        if speeds:
            print("\n   Signal statistics:")
            print(f"   - EngineSpeed: {min(speeds):.0f} - {max(speeds):.0f} RPM")
            print(f"   - EngineTemp:  {min(temps):.0f} - {max(temps):.0f}°C")
            print(f"   - Throttle:    {min(throttles):.0f} - {max(throttles):.0f}%")

    # Demonstrate error handling patterns
    print("\n6. Error handling patterns")
    print("   Testing extraction with invalid frame data...")

    # Create frame with zeros (may cause out-of-bounds errors depending on DBC)
    invalid_frame = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

    with SignalExtractor(dbc=dbc) as extractor:
        result = extractor.extract(can_id=0x100, data=invalid_frame)

        if result.has_errors():
            print("\n   Extraction errors detected:")
            for signal_name, error_msg in result.errors.items():
                print(f"   - {signal_name}:")
                print(f"     Error: {error_msg}")

                # Classify error type
                if "out of bounds" in error_msg:
                    print("     Type: Value exceeds DBC min/max limits")
                elif "decoding failed" in error_msg:
                    print("     Type: Bit decoding error")
                else:
                    print("     Type: Unknown error")
        else:
            print("   ✓ No errors (all signals have valid default values)")

        # Still safe to access values with defaults
        print("\n   Values (with defaults for errors):")
        for signal_name in ["EngineSpeed", "EngineTemp", "Throttle"]:
            value = result.get(signal_name, default=0.0)
            status = "✓" if signal_name in result.values else "✗"
            print(f"   {status} {signal_name}: {value}")

    print("\n" + "=" * 70)
    print("Example completed successfully!")
    print("=" * 70)
    print("\nKey Takeaways:")
    print("- SignalExtractor partitions results into values/errors/absent")
    print("- Use .get() with defaults for safe value access")
    print("- Context manager ensures subprocess cleanup")
    print("- Subprocess reused for processing multiple frames")
    print("- Error messages explain what went wrong")
    print("\nNext Steps:")
    print("- Try frame_updater.py for frame modification")
    print("- See multiplexed_signals.py for multiplexing examples")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
