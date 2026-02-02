#!/usr/bin/env python3
"""DBC Validation Demo

This script demonstrates Aletheia's DBC validation capabilities:

1. Signal overlap detection - signals that occupy the same bit positions
2. Range consistency - minimum must be <= maximum
3. Multiplexing awareness - overlapping signals are OK if mutually exclusive

The validation happens automatically when parsing a DBC. If validation fails,
a detailed error message explains exactly which signals overlap and their
bit positions.

This is useful for:
- Validating DBC files before deployment
- Catching copy-paste errors in signal definitions
- Ensuring consistent signal ranges
- Verifying multiplexed signal configurations

Requirements:
- Aletheia binary must be built: `cabal run shake -- build`
"""

import json
from aletheia import StreamingClient


def create_valid_dbc() -> dict:
    """Create a valid DBC with non-overlapping signals."""
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 256,  # 0x100
                "name": "SensorData",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "Temperature",
                        "startBit": 0,
                        "length": 16,
                        "byteOrder": "little_endian",
                        "signed": True,
                        "factor": 0.1,
                        "offset": -40,
                        "minimum": -40,
                        "maximum": 215,
                        "unit": "C",
                        "presence": "always"
                    },
                    {
                        "name": "Pressure",
                        "startBit": 16,  # Starts after Temperature (bits 0-15)
                        "length": 16,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 0.01,
                        "offset": 0,
                        "minimum": 0,
                        "maximum": 655.35,
                        "unit": "bar",
                        "presence": "always"
                    },
                    {
                        "name": "Status",
                        "startBit": 32,  # Starts after Pressure (bits 16-31)
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1,
                        "offset": 0,
                        "minimum": 0,
                        "maximum": 255,
                        "unit": "",
                        "presence": "always"
                    }
                ]
            }
        ]
    }


def create_overlapping_dbc() -> dict:
    """Create a DBC with overlapping signals (should fail validation)."""
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 256,  # 0x100
                "name": "SensorData",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "Temperature",
                        "startBit": 0,
                        "length": 16,  # Occupies bits 0-15
                        "byteOrder": "little_endian",
                        "signed": True,
                        "factor": 0.1,
                        "offset": -40,
                        "minimum": -40,
                        "maximum": 215,
                        "unit": "C",
                        "presence": "always"
                    },
                    {
                        "name": "Pressure",
                        "startBit": 8,  # OVERLAP! Starts at bit 8, but Temperature uses bits 0-15
                        "length": 16,  # Occupies bits 8-23
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 0.01,
                        "offset": 0,
                        "minimum": 0,
                        "maximum": 655.35,
                        "unit": "bar",
                        "presence": "always"
                    }
                ]
            }
        ]
    }


def create_inconsistent_range_dbc() -> dict:
    """Create a DBC with inconsistent signal range (min > max)."""
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 256,
                "name": "SensorData",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "Temperature",
                        "startBit": 0,
                        "length": 16,
                        "byteOrder": "little_endian",
                        "signed": True,
                        "factor": 0.1,
                        "offset": -40,
                        "minimum": 100,   # ERROR: minimum > maximum
                        "maximum": 50,
                        "unit": "C",
                        "presence": "always"
                    }
                ]
            }
        ]
    }


def create_multiplexed_dbc() -> dict:
    """Create a DBC with multiplexed signals that overlap but are mutually exclusive."""
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 256,
                "name": "MultiplexedData",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "MuxSelector",
                        "startBit": 0,
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1,
                        "offset": 0,
                        "minimum": 0,
                        "maximum": 3,
                        "unit": "",
                        "presence": "always"  # Multiplexor is always present
                    },
                    {
                        "name": "SensorA",
                        "startBit": 8,
                        "length": 16,  # Bits 8-23
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 0.1,
                        "offset": 0,
                        "minimum": 0,
                        "maximum": 6553.5,
                        "unit": "rpm",
                        "multiplexor": "MuxSelector",
                        "multiplex_value": 0  # Only active when MuxSelector = 0
                    },
                    {
                        "name": "SensorB",
                        "startBit": 8,
                        "length": 16,  # SAME bits 8-23 - but different mux value!
                        "byteOrder": "little_endian",
                        "signed": True,
                        "factor": 0.01,
                        "offset": 0,
                        "minimum": -327.68,
                        "maximum": 327.67,
                        "unit": "m/s",
                        "multiplexor": "MuxSelector",
                        "multiplex_value": 1  # Only active when MuxSelector = 1
                    }
                ]
            }
        ]
    }


def test_dbc(name: str, dbc: dict, expect_valid: bool) -> bool:
    """Test a DBC and report results."""
    print(f"\nTesting: {name}")
    print(f"Expected: {'Valid' if expect_valid else 'Invalid'}")

    try:
        with StreamingClient() as client:
            response = client.parse_dbc(dbc)

            if response.get("status") == "success":
                print(f"Result: VALID - {response.get('message', '')}")
                success = expect_valid
            else:
                print(f"Result: INVALID - {response.get('message', '')}")
                success = not expect_valid

            if success:
                print("Test: PASSED")
            else:
                print("Test: FAILED (unexpected result)")

            return success

    except Exception as e:
        print(f"Result: ERROR - {e}")
        return False


def main() -> None:
    print("=" * 70)
    print("DBC VALIDATION DEMO")
    print("=" * 70)
    print("""
Aletheia validates DBC files automatically when parsing:
- Signals must not overlap (unless multiplexed to different values)
- Signal ranges must be consistent (minimum <= maximum)
- All bounds are checked at parse time

This ensures that signal encoding/decoding is always well-defined.
""")

    results = []

    # Test 1: Valid DBC
    print("\n" + "-" * 70)
    print("TEST 1: Valid DBC (non-overlapping signals)")
    print("-" * 70)
    print("""
Signal layout:
  Temperature: bits 0-15  (16 bits)
  Pressure:    bits 16-31 (16 bits)
  Status:      bits 32-39 (8 bits)

No overlap - should pass validation.
""")
    results.append(test_dbc("Valid DBC", create_valid_dbc(), expect_valid=True))

    # Test 2: Overlapping signals
    print("\n" + "-" * 70)
    print("TEST 2: Overlapping Signals (should fail)")
    print("-" * 70)
    print("""
Signal layout:
  Temperature: bits 0-15  (16 bits)
  Pressure:    bits 8-23  (16 bits)  <- OVERLAP with Temperature!

The overlap region is bits 8-15.
""")
    results.append(test_dbc("Overlapping Signals", create_overlapping_dbc(), expect_valid=False))

    # Test 3: Inconsistent range
    print("\n" + "-" * 70)
    print("TEST 3: Inconsistent Range (min > max, should fail)")
    print("-" * 70)
    print("""
Signal range:
  Temperature: minimum=100, maximum=50  <- ERROR!

The minimum value cannot be greater than the maximum.
""")
    results.append(test_dbc("Inconsistent Range", create_inconsistent_range_dbc(), expect_valid=False))

    # Test 4: Multiplexed signals (overlapping but mutually exclusive)
    print("\n" + "-" * 70)
    print("TEST 4: Multiplexed Signals (overlapping but mutually exclusive)")
    print("-" * 70)
    print("""
Signal layout:
  MuxSelector: bits 0-7   (8 bits, multiplexor)
  SensorA:     bits 8-23  (16 bits, when MuxSelector=0)
  SensorB:     bits 8-23  (16 bits, when MuxSelector=1)

SensorA and SensorB use the SAME bits, but they are multiplexed
to different values of MuxSelector. They can never be active at
the same time, so this is valid.
""")
    results.append(test_dbc("Multiplexed Signals", create_multiplexed_dbc(), expect_valid=True))

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    passed = sum(results)
    total = len(results)
    print(f"\nTests passed: {passed}/{total}")

    if passed == total:
        print("\nAll validation tests passed!")
    else:
        print("\nSome tests failed - check the output above.")

    print("""
Key takeaways:
  - DBC validation happens automatically during parse_dbc()
  - Overlapping signals are detected with exact bit positions
  - Range consistency (min <= max) is verified
  - Multiplexed signals can overlap if mutually exclusive
  - Detailed error messages help identify the problem

This ensures your CAN protocol definitions are correct before
any signal encoding/decoding operations.
""")


if __name__ == "__main__":
    main()
