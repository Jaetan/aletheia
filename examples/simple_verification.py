#!/usr/bin/env python3
"""Simple verification example using Aletheia's streaming protocol.

Demonstrates:
    1. Converting a .dbc file to JSON format
    2. Defining LTL properties using the Signal DSL
    3. Streaming CAN frames for verification
    4. Handling property violations
"""

from pathlib import Path
from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json


def main() -> int:
    """Run a simple verification example."""
    example_dir = Path(__file__).parent
    dbc_file = example_dir / "example.dbc"

    print("=== Aletheia Simple Verification ===\n")

    # Convert DBC to JSON format
    print(f"Loading DBC from: {dbc_file}")
    try:
        dbc_json = dbc_to_json(str(dbc_file))
    except Exception as e:
        print(f"Failed to load DBC: {e}")
        return 1
    print("DBC loaded\n")

    # Define temporal properties using Signal DSL
    print("Properties:")

    prop1 = Signal("EngineSpeed").between(0, 8000).always()
    print("  1. Always: 0 <= EngineSpeed <= 8000")

    prop2 = Signal("EngineTemp").between(-40, 215).always()
    print("  2. Always: -40 <= EngineTemp <= 215")

    prop3 = Signal("BrakePressure").less_than(6553.5).always()
    print("  3. Always: BrakePressure < 6553.5\n")

    properties = [prop1.to_dict(), prop2.to_dict(), prop3.to_dict()]

    # Start streaming protocol
    print("Streaming...")
    try:
        with AletheiaClient() as client:
            client.parse_dbc(dbc_json)
            client.set_properties(properties)
            client.start_stream()

            # Frame 1: Normal engine status (Speed=2000rpm, Temp=90C)
            frame1 = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
            response1 = client.send_frame(timestamp=100, can_id=0x100, data=frame1)
            print(f"  t=100ms, ID=0x100: {response1}")

            # Frame 2: Normal brake status (Pressure=50bar, Pressed=1)
            frame2 = bytearray([0xF4, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00])
            response2 = client.send_frame(timestamp=200, can_id=0x200, data=frame2)
            print(f"  t=200ms, ID=0x200: {response2}")

            client.end_stream()
            print("\nVerification complete")

    except Exception as e:
        print(f"\nError during verification: {e}")
        return 1

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
