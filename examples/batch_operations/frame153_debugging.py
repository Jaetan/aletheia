#!/usr/bin/env python3
"""
Frame Debugging Example (Frame 153 / 0x99)

Demonstrates debugging signal encoding/decoding issues by:
- Building a frame with known values
- Extracting and verifying the values
- Comparing raw bytes
- Identifying encoding problems
- Testing boundary conditions

This example focuses on Frame 153 (0x99) as a concrete debugging scenario.

Usage:
    python3 frame153_debugging.py
"""

from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "python"))

from aletheia import SignalExtractor, FrameBuilder
from aletheia.dbc_converter import dbc_to_json


def print_frame_hex(frame, label):
    """Print frame in various formats for debugging"""
    print(f"\n   {label}:")
    print(f"   - Hex:     {' '.join(f'0x{b:02X}' for b in frame)}")
    print(f"   - Decimal: {' '.join(f'{b:3d}' for b in frame)}")
    print(f"   - Binary:  {' '.join(f'{b:08b}' for b in frame)}")


def main():
    print("=" * 70)
    print("Frame Debugging Example (Frame 0x99)")
    print("=" * 70)

    # Load DBC file
    dbc_path = Path(__file__).parent.parent / "example.dbc"
    print(f"\n1. Loading DBC file: {dbc_path}")

    try:
        dbc = dbc_to_json(dbc_path)
        print("   ✓ DBC loaded successfully")
    except FileNotFoundError:
        print(f"   ✗ DBC file not found: {dbc_path}")
        print("\n   ℹ This example demonstrates debugging concepts.")
        print("   If you have a different DBC, modify CAN_ID to match your file.")
        return 1
    except Exception as e:
        print(f"   ✗ Failed to load DBC: {e}")
        return 1

    # For this example, we'll use CAN ID 0x100 (common in example DBCs)
    # In a real scenario, this would be 0x99
    CAN_ID = 0x100

    print(f"\n2. Debugging Frame 0x{CAN_ID:X}")
    print("   Scenario: We suspect signal encoding/decoding issues")

    # Step 1: Build frame with known values
    print("\n   Step 1: Build frame with known signal values")

    test_signals = {
        "EngineSpeed": 2000,
        "EngineTemp": 90,
        "Throttle": 75
    }

    print("\n   Input signals:")
    for name, value in test_signals.items():
        print(f"   - {name}: {value}")

    try:
        with FrameBuilder(can_id=CAN_ID, dbc=dbc) as builder:
            frame = builder
            for name, value in test_signals.items():
                frame = frame.set(name, value)
            built_frame = frame.build()

        print_frame_hex(built_frame, "Built frame")

    except RuntimeError as e:
        print(f"\n   ✗ Frame building failed: {e}")
        print("\n   Possible causes:")
        print("   - Signal not found in DBC")
        print("   - Value out of bounds")
        print("   - Signal overlap detected")
        return 1

    # Step 2: Extract signals back and compare
    print("\n   Step 2: Extract signals and verify")

    with SignalExtractor(dbc=dbc) as extractor:
        result = extractor.extract(can_id=CAN_ID, data=built_frame)

        print("\n   Extraction results:")
        print(f"   - Successfully extracted: {len(result.values)} signals")
        print(f"   - Errors: {len(result.errors)}")
        print(f"   - Absent: {len(result.absent)}")

        # Compare input vs output
        print("\n   Value comparison:")
        all_match = True

        for signal_name, input_value in test_signals.items():
            output_value = result.get(signal_name, default=None)

            if output_value is None:
                print(f"   ✗ {signal_name:20s}: NOT EXTRACTED")
                all_match = False
            else:
                diff = abs(output_value - input_value)
                status = "✓" if diff < 0.01 else "✗"
                print(f"   {status} {signal_name:20s}: "
                      f"Input={input_value:8.2f}, "
                      f"Output={output_value:8.2f}, "
                      f"Diff={diff:8.4f}")

                if diff >= 0.01:
                    all_match = False

        if all_match:
            print("\n   ✓ All values match! Encoding/decoding is correct.")
        else:
            print("\n   ✗ Value mismatch detected!")
            print("\n   Debugging tips:")
            print("   - Check DBC scaling factors (factor/offset)")
            print("   - Verify signal bit positions (startBit + length)")
            print("   - Check byte order (little_endian vs big_endian)")
            print("   - Verify signed vs unsigned")

    # Step 3: Test boundary conditions
    print("\n3. Testing boundary conditions")
    print("   Testing min/max values to find encoding limits")

    # Find signal definitions in DBC
    signals_info = {}
    for message in dbc.get("messages", []):
        if message["id"] == CAN_ID:
            for sig in message.get("signals", []):
                signals_info[sig["name"]] = {
                    "min": sig.get("minimum", 0),
                    "max": sig.get("maximum", 0),
                    "factor": sig.get("factor", 1),
                    "offset": sig.get("offset", 0),
                    "length": sig.get("length", 0)
                }

    with FrameBuilder(can_id=CAN_ID, dbc=dbc) as builder:
        with SignalExtractor(dbc=dbc) as extractor:
            for signal_name, info in signals_info.items():
                print(f"\n   Testing {signal_name}:")
                print(f"   - DBC Min: {info['min']}")
                print(f"   - DBC Max: {info['max']}")
                print(f"   - Factor:  {info['factor']}")
                print(f"   - Offset:  {info['offset']}")
                print(f"   - Bits:    {info['length']}")

                # Test minimum value
                try:
                    frame_min = builder.set(signal_name, info['min']).build()
                    result_min = extractor.extract(can_id=CAN_ID, data=frame_min)
                    value_min = result_min.get(signal_name, None)
                    print(f"   - Min value test: {value_min} (✓ OK)")
                except Exception as e:
                    print(f"   - Min value test: ✗ FAILED ({e})")

                # Test maximum value
                try:
                    frame_max = builder.set(signal_name, info['max']).build()
                    result_max = extractor.extract(can_id=CAN_ID, data=frame_max)
                    value_max = result_max.get(signal_name, None)
                    print(f"   - Max value test: {value_max} (✓ OK)")
                except Exception as e:
                    print(f"   - Max value test: ✗ FAILED ({e})")

                # Test out-of-bounds (should fail)
                try:
                    frame_oob = builder.set(signal_name, info['max'] * 2).build()
                    print(f"   - Out-of-bounds: ✗ Accepted (should reject!)")
                except RuntimeError:
                    print(f"   - Out-of-bounds: ✓ Rejected (correct)")

    # Step 4: Compare with expected raw bytes
    print("\n4. Comparing with expected raw bytes")
    print("   Scenario: We have known-good frame from CAN trace")

    # Example: Known-good frame from trace
    known_good_frame = [0x00, 0x07, 0xD0, 0x5A, 0x00, 0x00, 0x00, 0x00]

    print_frame_hex(known_good_frame, "Known-good frame (from trace)")

    # Extract signals from known-good frame
    with SignalExtractor(dbc=dbc) as extractor:
        result_known = extractor.extract(can_id=CAN_ID, data=known_good_frame)

        print("\n   Extracted signals from known-good frame:")
        for name, value in sorted(result_known.values.items()):
            print(f"   - {name:20s}: {value:8.2f}")

        # Build frame with same values
        print("\n   Building frame with extracted values...")

        with FrameBuilder(can_id=CAN_ID, dbc=dbc) as builder:
            rebuild = builder
            for name, value in result_known.values.items():
                rebuild = rebuild.set(name, value)
            rebuilt_frame = rebuild.build()

        print_frame_hex(rebuilt_frame, "Rebuilt frame")

        # Compare byte-by-byte
        print("\n   Byte-by-byte comparison:")
        all_match = True
        for i, (original, rebuilt) in enumerate(zip(known_good_frame, rebuilt_frame)):
            status = "✓" if original == rebuilt else "✗"
            print(f"   Byte {i}: {status} Original=0x{original:02X}, Rebuilt=0x{rebuilt:02X}")
            if original != rebuilt:
                all_match = False

        if all_match:
            print("\n   ✓ Perfect match! DBC encoding is correct.")
        else:
            print("\n   ✗ Bytes differ! Possible issues:")
            print("   - DBC definition doesn't match actual CAN protocol")
            print("   - Signal bit positions incorrect")
            print("   - Byte order mismatch")
            print("   - Signals we don't know about in the frame")

    # Step 5: Debugging checklist
    print("\n" + "=" * 70)
    print("DEBUGGING CHECKLIST")
    print("=" * 70)
    print("""
When debugging signal encoding/decoding issues:

✓ 1. Verify DBC matches the actual CAN protocol version
   - Check if DBC is up-to-date
   - Confirm signal definitions match hardware

✓ 2. Test with known values
   - Build frame with simple values (e.g., 0, 100, 1000)
   - Extract and compare - should match exactly

✓ 3. Check signal properties in DBC:
   - startBit: Correct bit position?
   - length: Correct number of bits?
   - byteOrder: "little_endian" or "big_endian"?
   - signed: true or false?
   - factor: Scaling factor (default 1.0)
   - offset: Offset value (default 0.0)
   - minimum/maximum: Valid ranges

✓ 4. Test boundary conditions:
   - Minimum value
   - Maximum value
   - Out-of-bounds (should be rejected)
   - Zero
   - Mid-range values

✓ 5. Compare with known-good frames:
   - Capture frame from actual CAN bus
   - Extract signals from captured frame
   - Build new frame with same signals
   - Compare byte-by-byte

✓ 6. Check for signal overlap:
   - Agda validates that signals don't overlap
   - If build fails with "overlap" error, check DBC

✓ 7. Verify multiplexing:
   - Check if signal is multiplexed
   - Ensure correct multiplexor value
   - Absent signals are normal for multiplexing

Common Issues:
- Scaling: factor/offset incorrect → values scaled wrong
- Bit position: startBit wrong → completely wrong values
- Byte order: endianness mismatch → garbled multi-byte values
- Signed/unsigned: wrong sign interpretation → negative values wrong
- Length: wrong bit count → truncated or padded values
""")

    print("\n" + "=" * 70)
    print("Example completed!")
    print("=" * 70)
    print("\nKey Takeaways:")
    print("- Always test with known values first")
    print("- Compare built frames byte-by-byte with known-good frames")
    print("- Test boundary conditions to find limits")
    print("- Check all signal properties in DBC")
    print("- Agda validates overlap and bounds - trust the errors!")
    print("\nNext Steps:")
    print("- See batch_trace_processing.py for full trace workflows")
    print("- Review docs/tutorials/BATCH_OPERATIONS.md for more patterns")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
