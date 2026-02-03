#!/usr/bin/env python3
"""
Simple verification example using Aletheia's JSON streaming protocol.

This example demonstrates:
1. Converting a .dbc file to JSON format
2. Defining LTL properties using the Signal DSL
3. Streaming CAN frames for verification
4. Handling property violations
"""

from pathlib import Path
from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json


def main():
    """Run a simple verification example."""
    example_dir = Path(__file__).parent
    dbc_file = example_dir / "example.dbc"

    print("=== Aletheia Simple Verification Example ===\n")

    # Convert DBC to JSON format
    print(f"Loading DBC from: {dbc_file}")
    try:
        dbc_json = dbc_to_json(str(dbc_file))
        print("✓ DBC converted to JSON successfully\n")
    except Exception as e:
        print(f"✗ Failed to load DBC: {e}")
        return 1

    # Define temporal properties using Signal DSL
    print("Defining temporal properties:")

    # Property 1: Engine speed must always be within valid range
    prop1 = Signal("EngineSpeed").between(0, 8000).always()
    print("  1. Always: 0 ≤ EngineSpeed ≤ 8000")

    # Property 2: Engine temperature must be within operating range
    prop2 = Signal("EngineTemp").between(-40, 215).always()
    print("  2. Always: -40 ≤ EngineTemp ≤ 215")

    # Property 3: Brake pressure should not exceed maximum
    prop3 = Signal("BrakePressure").less_than(6553.5).always()
    print("  3. Always: BrakePressure < 6553.5\n")

    properties = [prop1.to_dict(), prop2.to_dict(), prop3.to_dict()]

    # Start streaming protocol
    print("Starting verification with streaming protocol...")
    try:
        with AletheiaClient() as client:
            # Initialize: parse DBC and set properties
            client.parse_dbc(dbc_json)
            client.set_properties(properties)
            client.start_stream()
            print("✓ Streaming session started\n")

            # Example: Send some test frames
            print("Sending test frames:")

            # Frame 1: Normal engine status (Speed=2000rpm, Temp=90°C)
            # EngineSpeed: 2000/0.25 = 8000 (0x1F40) → bytes [0x40, 0x1F]
            # EngineTemp: (90+40)/1 = 130 (0x82) → byte [0x82]
            frame1 = bytes([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
            response1 = client.send_frame(timestamp=100, can_id=0x100, data=frame1)
            print(f"  t=100ms, ID=0x100: {response1}")

            # Frame 2: Normal brake status (Pressure=50bar, Pressed=1)
            # BrakePressure: 50/0.1 = 500 (0x01F4) → bytes [0xF4, 0x01]
            # BrakePressed: 1 → byte [0x01]
            frame2 = bytes([0xF4, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00])
            response2 = client.send_frame(timestamp=200, can_id=0x200, data=frame2)
            print(f"  t=200ms, ID=0x200: {response2}")

            # End streaming
            client.end_stream()
            print("\n✓ Verification complete")

    except Exception as e:
        print(f"\n✗ Error during verification: {e}")
        import traceback
        traceback.print_exc()
        return 1

    return 0


if __name__ == '__main__':
    import sys
    sys.exit(main())
