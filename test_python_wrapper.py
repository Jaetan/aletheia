#!/usr/bin/env python3
"""
Integration test for Python wrapper - Phase 1

Tests:
1. DBC parsing (ParseDBC command)
2. Signal extraction (ExtractSignal command)
3. Signal injection (InjectSignal command)
"""

from aletheia import CANDecoder

def test_extract_signal():
    """Test signal extraction from a CAN frame"""
    print("=" * 60)
    print("TEST 1: Extract Signal")
    print("=" * 60)

    # Load DBC - this calls ParseDBC command
    print("\n[1] Loading DBC file...")
    decoder = CANDecoder.from_dbc("test_dbc.yaml")
    print("✓ DBC loaded successfully")

    # Extract signal - this calls ExtractSignal command
    print("\n[2] Extracting EngineSpeed signal from frame...")
    frame_bytes = [0x10, 0x27, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    print(f"    Frame: {' '.join(f'0x{b:02X}' for b in frame_bytes)}")

    value = decoder.extract_signal("EngineData", "EngineSpeed", frame_bytes)
    print(f"✓ Extracted value: {value}")

    # Verify the result
    # Frame 0x10 0x27 = 0x2710 in little endian = 10000 decimal
    # With factor 0.25: 10000 * 0.25 = 2500 rpm
    expected = 2500.0
    if abs(value - expected) < 0.01:
        print(f"✓ Value matches expected: {expected}")
        return True
    else:
        print(f"✗ FAIL: Expected {expected}, got {value}")
        return False


def test_inject_signal():
    """Test signal injection into a CAN frame"""
    print("\n" + "=" * 60)
    print("TEST 2: Inject Signal")
    print("=" * 60)

    # Load DBC
    print("\n[1] Loading DBC file...")
    decoder = CANDecoder.from_dbc("test_dbc.yaml")
    print("✓ DBC loaded successfully")

    # Inject signal - this calls InjectSignal command
    print("\n[2] Injecting EngineSpeed=2500 rpm into frame...")
    frame_bytes = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    print(f"    Initial frame: {' '.join(f'0x{b:02X}' for b in frame_bytes)}")

    new_frame = decoder.inject_signal("EngineData", "EngineSpeed", 2500.0, frame_bytes)
    print(f"✓ Injected value: 2500.0")
    print(f"    Modified frame: {' '.join(f'0x{b:02X}' for b in new_frame)}")

    # Verify the result
    # 2500 rpm with factor 0.25 → raw = 2500 / 0.25 = 10000
    # 10000 in little endian 16-bit = 0x10 0x27
    expected = [0x10, 0x27, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    if new_frame == expected:
        print(f"✓ Frame matches expected: {' '.join(f'0x{b:02X}' for b in expected)}")
        return True
    else:
        print(f"✗ FAIL: Expected {expected}, got {new_frame}")
        return False


def test_round_trip():
    """Test extract → inject round-trip"""
    print("\n" + "=" * 60)
    print("TEST 3: Round-Trip (Extract → Inject)")
    print("=" * 60)

    # Load DBC
    print("\n[1] Loading DBC file...")
    decoder = CANDecoder.from_dbc("test_dbc.yaml")
    print("✓ DBC loaded successfully")

    # Original frame with value
    original_frame = [0x10, 0x27, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    print(f"\n[2] Original frame: {' '.join(f'0x{b:02X}' for b in original_frame)}")

    # Extract
    print("\n[3] Extracting signal...")
    extracted_value = decoder.extract_signal("EngineData", "EngineSpeed", original_frame)
    print(f"✓ Extracted: {extracted_value}")

    # Inject back into empty frame
    print("\n[4] Injecting extracted value into empty frame...")
    empty_frame = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    new_frame = decoder.inject_signal("EngineData", "EngineSpeed", extracted_value, empty_frame)
    print(f"    Injected frame: {' '.join(f'0x{b:02X}' for b in new_frame)}")

    # Verify round-trip (first 2 bytes should match)
    if new_frame[:2] == original_frame[:2]:
        print(f"✓ Round-trip successful: first 2 bytes match")
        return True
    else:
        print(f"✗ FAIL: Original {original_frame[:2]}, got {new_frame[:2]}")
        return False


def main():
    """Run all tests"""
    print("\n" + "═" * 60)
    print("  ALETHEIA PYTHON WRAPPER - INTEGRATION TESTS")
    print("═" * 60)

    results = []

    try:
        results.append(("Extract Signal", test_extract_signal()))
    except Exception as e:
        print(f"\n✗ TEST FAILED WITH EXCEPTION: {e}")
        import traceback
        traceback.print_exc()
        results.append(("Extract Signal", False))

    try:
        results.append(("Inject Signal", test_inject_signal()))
    except Exception as e:
        print(f"\n✗ TEST FAILED WITH EXCEPTION: {e}")
        import traceback
        traceback.print_exc()
        results.append(("Inject Signal", False))

    try:
        results.append(("Round-Trip", test_round_trip()))
    except Exception as e:
        print(f"\n✗ TEST FAILED WITH EXCEPTION: {e}")
        import traceback
        traceback.print_exc()
        results.append(("Round-Trip", False))

    # Summary
    print("\n" + "═" * 60)
    print("  SUMMARY")
    print("═" * 60)
    for name, passed in results:
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{status:8} {name}")

    total = len(results)
    passed = sum(1 for _, p in results if p)
    print(f"\nTotal: {passed}/{total} tests passed")

    if passed == total:
        print("\n🎉 All tests passed!")
        return 0
    else:
        print(f"\n❌ {total - passed} test(s) failed")
        return 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
