#!/usr/bin/env python3
"""Simple verification example"""

from pathlib import Path
from aletheia import CANDecoder, LTL, verify

def main():
    example_dir = Path(__file__).parent
    dbc_file = example_dir / "sample.dbc.yaml"
    trace_file = example_dir / "sample_trace.yaml"

    print("=== Aletheia Simple Verification Example ===\n")

    print(f"Loading DBC from: {dbc_file}")
    decoder = CANDecoder.from_dbc(str(dbc_file))
    print("✓ DBC loaded successfully\n")

    print("Defining temporal properties:")

    prop1 = LTL.always(decoder.signal("EngineSpeed") > 0)
    print("  1. Always: EngineSpeed > 0")

    prop2 = LTL.always(
        LTL.implies(
            decoder.signal("EngineSpeed") > 512,
            LTL.eventually(decoder.signal("EngineTemp") > 40, within=5.0)
        )
    )
    print("  2. Always: EngineSpeed > 512 → Eventually(EngineTemp > 40)")

    prop3 = LTL.never(
        LTL.both(
            decoder.signal("EngineSpeed") == 0,
            decoder.signal("BrakePressed") == 1
        )
    )
    print("  3. Never: (EngineSpeed = 0 AND BrakePressed = 1)\n")

    properties = [prop1, prop2, prop3]

    print(f"Verifying against trace: {trace_file}")
    print("(This will call the Agda/Haskell backend)\n")

    try:
        result = verify(decoder, str(trace_file), properties, log_level="info")
        print(result)

        if result.properties:
            print("\nDetailed results:")
            for i, prop_result in enumerate(result.properties, 1):
                status = "✓ PASS" if prop_result.get('satisfied') else "✗ FAIL"
                print(f"  Property {i}: {status}")

    except Exception as e:
        print(f"✗ Verification failed: {e}")
        print("\n" + "="*70)
        print("NOTE: This is expected in Phase 1!")
        print("="*70)
        print("\nThe Agda/Haskell backend is currently a stub that just echoes input.")
        print("Phase 2 will implement:")
        print("  - Command parsing in Agda")
        print("  - DBC processing")
        print("  - LTL verification")
        print("\nCurrent status:")
        print("  ✓ Build system working")
        print("  ✓ Agda compilation successful")
        print("  ✓ Haskell binary created")
        print("  ✓ Python-to-binary communication working")
        print("  ✗ Command processing (Phase 2)")
        print("\nTo continue development, see DEVELOPMENT.md")
        return 1

    return 0

if __name__ == '__main__':
    import sys
    sys.exit(main())
