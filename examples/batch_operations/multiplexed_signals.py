#!/usr/bin/env python3
"""
Multiplexed Signals Example

Demonstrates handling multiplexed CAN signals where multiple signals
share the same frame bits but are selected by a multiplexor value.

This example shows:
- Understanding multiplexing
- Building frames with multiplexed signals
- Extracting multiplexed signals
- Handling absent signals (normal, not an error)
- Switching between multiplexor modes

Note: This example uses a hypothetical multiplexed DBC. If your example.dbc
doesn't have multiplexing, this will demonstrate the concepts with synthetic data.

Usage:
    python3 multiplexed_signals.py
"""

from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "python"))

from aletheia import SignalExtractor, FrameBuilder
from aletheia.dbc_converter import dbc_to_json


def main():
    print("=" * 70)
    print("Multiplexed Signals Example")
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

    # Explain multiplexing concept
    print("\n" + "=" * 70)
    print("MULTIPLEXING CONCEPT")
    print("=" * 70)
    print("""
Multiplexed signals share the same frame bits, selected by a multiplexor:

Example CAN Message 0x153:
  - Mode (bits 0-7) = MULTIPLEXOR signal

  When Mode == 0x01:
    - SignalA (bits 8-15)  ← Present
    - SignalB (bits 16-23) ← Present
    - SignalC (bits 8-15)  ← Absent (wrong Mode)
    - SignalD (bits 16-23) ← Absent (wrong Mode)

  When Mode == 0x02:
    - SignalA (bits 8-15)  ← Absent (wrong Mode)
    - SignalB (bits 16-23) ← Absent (wrong Mode)
    - SignalC (bits 8-15)  ← Present
    - SignalD (bits 16-23) ← Present

SignalA and SignalC share bits 8-15, but only one is "present" at a time.
SignalB and SignalD share bits 16-23, but only one is "present" at a time.

Key Point: Absent signals are NOT errors - this is normal multiplexing behavior.
""")

    # Check if DBC has multiplexing
    print("\n2. Checking for multiplexed signals in DBC")

    has_multiplexing = False
    multiplexed_messages = []

    # Scan DBC for multiplexed signals
    for message in dbc.get("messages", []):
        multiplex_signals = [
            sig for sig in message.get("signals", [])
            if "multiplexor" in sig or sig.get("presence") == "multiplexed"
        ]
        if multiplex_signals:
            has_multiplexing = True
            multiplexed_messages.append(message)
            print(f"\n   Found multiplexed message: {message['name']} (ID 0x{message['id']:X})")
            for sig in multiplex_signals:
                if "multiplexor" in sig:
                    print(f"   - {sig['name']:20s} (multiplexed)")

    if not has_multiplexing:
        print("\n   ℹ This DBC doesn't have multiplexed signals.")
        print("   Demonstrating concepts with synthetic examples...")
        demonstrate_synthetic_multiplexing()
    else:
        print(f"\n   ✓ Found {len(multiplexed_messages)} message(s) with multiplexing")
        demonstrate_real_multiplexing(dbc, multiplexed_messages)

    print("\n" + "=" * 70)
    print("Example completed!")
    print("=" * 70)
    print("\nKey Takeaways:")
    print("- Multiplexed signals share frame bits, selected by multiplexor")
    print("- Absent signals appear in result.absent (NOT in result.errors)")
    print("- Absent signals are normal - not an error condition")
    print("- Only one 'set' of multiplexed signals is present per frame")
    print("- Always check result.absent when processing multiplexed frames")
    print("\nNext Steps:")
    print("- See batch_trace_processing.py for real-world workflows")
    print("- Try frame153_debugging.py for debugging examples")
    print("=" * 70)

    return 0


def demonstrate_synthetic_multiplexing():
    """Demonstrate multiplexing concepts with synthetic data"""
    print("\n" + "=" * 70)
    print("SYNTHETIC MULTIPLEXING DEMONSTRATION")
    print("=" * 70)

    print("""
Simulating a hypothetical multiplexed message 0x153:

Message Structure:
  - Mode (byte 0): Multiplexor signal
    - Mode = 0x01: Engineering mode
    - Mode = 0x02: Diagnostic mode

Engineering Mode (Mode = 0x01):
  - EngineRPM (bytes 1-2)
  - CoolantTemp (byte 3)

Diagnostic Mode (Mode = 0x02):
  - DiagnosticCode (bytes 1-2)
  - FaultCounter (byte 3)
""")

    print("\n3. Building Engineering Mode Frame (Mode = 0x01)")
    engineering_frame = [
        0x01,  # Mode = 0x01 (engineering)
        0x07, 0xD0,  # EngineRPM = 2000 (0x07D0)
        0x5A,  # CoolantTemp = 90
        0x00, 0x00, 0x00, 0x00
    ]
    print(f"   Frame: {[f'0x{b:02X}' for b in engineering_frame]}")
    print("   Signals present:")
    print("   - Mode: 1")
    print("   - EngineRPM: 2000")
    print("   - CoolantTemp: 90")
    print("   Signals absent (wrong mode):")
    print("   - DiagnosticCode")
    print("   - FaultCounter")

    print("\n4. Building Diagnostic Mode Frame (Mode = 0x02)")
    diagnostic_frame = [
        0x02,  # Mode = 0x02 (diagnostic)
        0x12, 0x34,  # DiagnosticCode = 0x1234
        0x05,  # FaultCounter = 5
        0x00, 0x00, 0x00, 0x00
    ]
    print(f"   Frame: {[f'0x{b:02X}' for b in diagnostic_frame]}")
    print("   Signals present:")
    print("   - Mode: 2")
    print("   - DiagnosticCode: 0x1234")
    print("   - FaultCounter: 5")
    print("   Signals absent (wrong mode):")
    print("   - EngineRPM")
    print("   - CoolantTemp")

    print("\n5. Key Observations")
    print("""
   - Same frame ID (0x153) carries different signals
   - Multiplexor (Mode) determines which signals are present
   - Absent signals are NOT errors - they're just inactive
   - Frame structure changes based on multiplexor value
   - Applications must check multiplexor before using signals

   Handling in Code:
   ```python
   result = extractor.extract(can_id=0x153, data=frame)

   # Check multiplexor to determine frame type
   if "Mode" in result.values:
       mode = result.get("Mode")

       if mode == 1:
           # Engineering mode - use EngineRPM, CoolantTemp
           rpm = result.get("EngineRPM", default=0)
           temp = result.get("CoolantTemp", default=0)

       elif mode == 2:
           # Diagnostic mode - use DiagnosticCode, FaultCounter
           code = result.get("DiagnosticCode", default=0)
           counter = result.get("FaultCounter", default=0)

   # Absent signals will be in result.absent (not an error!)
   ```
""")


def demonstrate_real_multiplexing(dbc, multiplexed_messages):
    """Demonstrate with real DBC multiplexing"""
    print("\n" + "=" * 70)
    print("REAL DBC MULTIPLEXING DEMONSTRATION")
    print("=" * 70)

    for message in multiplexed_messages:
        msg_id = message["id"]
        msg_name = message["name"]

        print(f"\n3. Processing Message: {msg_name} (ID 0x{msg_id:X})")

        # Find multiplexor signal
        multiplexor_name = None
        multiplexed_groups = {}

        for sig in message["signals"]:
            if "multiplexor" in sig:
                # This is a multiplexed signal
                mux_sig = sig["multiplexor"]
                mux_val = sig.get("multiplex_value", 0)

                if mux_sig not in multiplexed_groups:
                    multiplexor_name = mux_sig
                    multiplexed_groups[mux_val] = []

                multiplexed_groups[mux_val].append(sig["name"])

        if not multiplexor_name:
            print("   ℹ No multiplexor found")
            continue

        print(f"\n   Multiplexor signal: {multiplexor_name}")
        print(f"   Found {len(multiplexed_groups)} multiplexing modes:")

        for mux_val, signals in sorted(multiplexed_groups.items()):
            print(f"\n   Mode {mux_val}:")
            for sig_name in signals:
                print(f"   - {sig_name}")

        # Try to build and extract frames for each mode
        print(f"\n4. Testing each multiplexing mode")

        with FrameBuilder(can_id=msg_id, dbc=dbc) as builder:
            with SignalExtractor(dbc=dbc) as extractor:
                for mux_val, signals in sorted(multiplexed_groups.items()):
                    print(f"\n   Building frame for Mode {mux_val}:")

                    try:
                        # Build frame with multiplexor + first signal from group
                        frame_builder = builder.set(multiplexor_name, mux_val)

                        # Set first signal in the group
                        if signals:
                            frame_builder = frame_builder.set(signals[0], 100)

                        frame = frame_builder.build()

                        print(f"   Frame: {[f'0x{b:02X}' for b in frame]}")

                        # Extract and show results
                        result = extractor.extract(can_id=msg_id, data=frame)

                        print(f"   Present signals: {list(result.values.keys())}")
                        print(f"   Absent signals: {result.absent}")

                    except Exception as e:
                        print(f"   ✗ Error: {e}")


if __name__ == "__main__":
    sys.exit(main())
