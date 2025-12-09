#!/usr/bin/env python3
"""
Simple Frame Builder Example

Demonstrates basic usage of FrameBuilder to construct CAN frames
from signal name-value pairs.

This example shows:
- Loading a DBC file
- Creating a frame builder
- Setting multiple signals
- Building the frame
- Verifying the result

Usage:
    python3 simple_frame_builder.py
"""

from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "python"))

from aletheia import FrameBuilder, SignalExtractor
from aletheia.dbc_converter import dbc_to_json


def main():
    print("=" * 70)
    print("Simple Frame Builder Example")
    print("=" * 70)

    # Load DBC file
    dbc_path = Path(__file__).parent.parent / "example.dbc"
    print(f"\n1. Loading DBC file: {dbc_path}")

    try:
        dbc = dbc_to_json(dbc_path)
        print("   ✓ DBC loaded successfully")
    except FileNotFoundError:
        print(f"   ✗ DBC file not found: {dbc_path}")
        print("   Please ensure example.dbc exists in the examples directory")
        return 1
    except Exception as e:
        print(f"   ✗ Failed to load DBC: {e}")
        return 1

    # Build a simple frame with engine signals
    print("\n2. Building CAN frame with engine signals")
    print("   Signals to encode:")
    print("   - EngineSpeed: 2000 RPM")
    print("   - EngineTemp: 90°C")
    print("   - Throttle: 75%")

    try:
        with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
            # Use fluent interface to set signals
            frame = (builder
                .set("EngineSpeed", 2000)
                .set("EngineTemp", 90)
                .set("Throttle", 75)
                .build())

            print(f"\n   ✓ Frame built successfully")
            print(f"   Frame bytes: {[f'0x{b:02X}' for b in frame]}")
            print(f"   Frame bytes (decimal): {frame}")

    except RuntimeError as e:
        print(f"   ✗ Failed to build frame: {e}")
        return 1

    # Verify the frame by extracting signals back
    print("\n3. Verifying frame by extracting signals")

    try:
        with SignalExtractor(dbc=dbc) as extractor:
            result = extractor.extract(can_id=0x100, data=frame)

            if result.has_errors():
                print(f"   ✗ Extraction errors: {result.errors}")
                return 1

            print("   ✓ All signals extracted successfully")
            print("\n   Extracted values:")
            for signal_name in ["EngineSpeed", "EngineTemp", "Throttle"]:
                value = result.get(signal_name)
                print(f"   - {signal_name}: {value}")

            # Verify values match what we encoded
            if (abs(result.get("EngineSpeed") - 2000) < 0.01 and
                abs(result.get("EngineTemp") - 90) < 0.01 and
                abs(result.get("Throttle") - 75) < 0.01):
                print("\n   ✓ All values match! Frame encoding/decoding successful")
            else:
                print("\n   ✗ Value mismatch - possible DBC issue")
                return 1

    except Exception as e:
        print(f"   ✗ Verification failed: {e}")
        return 1

    # Build multiple frames with different values
    print("\n4. Building multiple frames efficiently")
    print("   Building 5 frames with increasing engine speed...")

    try:
        with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
            frames = []

            for i, speed in enumerate(range(1000, 3500, 500), 1):
                frame = (builder
                    .set("EngineSpeed", speed)
                    .set("EngineTemp", 85 + i * 2)
                    .set("Throttle", 50 + i * 5)
                    .build())

                frames.append((speed, frame))

            print(f"\n   ✓ Built {len(frames)} frames")
            print("\n   Frame summary:")
            for speed, frame in frames:
                print(f"   - Speed {speed:4d}: {[f'{b:02X}' for b in frame]}")

    except Exception as e:
        print(f"   ✗ Failed to build frames: {e}")
        return 1

    print("\n" + "=" * 70)
    print("Example completed successfully!")
    print("=" * 70)
    print("\nKey Takeaways:")
    print("- FrameBuilder uses an immutable builder pattern")
    print("- Context manager (with) ensures proper cleanup")
    print("- Subprocess is reused for multiple frame builds")
    print("- Signals are validated against DBC definitions")
    print("- Extraction can verify frame correctness")
    print("\nNext Steps:")
    print("- Try signal_extractor.py for extraction examples")
    print("- See frame_updater.py for frame modification")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
