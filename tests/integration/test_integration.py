#!/usr/bin/env python3
"""
Full integration test for Phase 2B.1 JSON streaming protocol.
Tests the complete flow: parseDBC → setProperties → startStream → data frames → endStream
"""

import json
import subprocess
import sys
from pathlib import Path

def send_command(proc, command):
    """Send a JSON command and receive response."""
    command_json = json.dumps(command)
    print(f"\n>>> Sending: {command_json}")
    proc.stdin.write(command_json + "\n")
    proc.stdin.flush()

    response_line = proc.stdout.readline().strip()
    print(f"<<< Received: {response_line}")

    try:
        response = json.loads(response_line)
        return response
    except json.JSONDecodeError as e:
        print(f"ERROR: Failed to parse response as JSON: {e}")
        print(f"Raw response: {response_line}")
        return None

def main():
    # Load test DBC JSON (relative to project root)
    project_root = Path(__file__).parent.parent.parent
    dbc_path = project_root / "tests" / "integration" / "fixtures" / "test_speed.dbc.json"
    if not dbc_path.exists():
        print(f"ERROR: {dbc_path} not found")
        return 1

    with open(dbc_path) as f:
        dbc_json = json.load(f)

    print("=" * 80)
    print("Phase 2B.1 Integration Test - JSON Streaming Protocol")
    print("=" * 80)

    # Start the binary (relative to project root)
    binary_path = project_root / "build" / "aletheia"
    if not binary_path.exists():
        print(f"ERROR: {binary_path} not found. Run 'cabal run shake -- build' first.")
        return 1

    proc = subprocess.Popen(
        [str(binary_path)],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        bufsize=1
    )

    try:
        # Step 1: Parse DBC
        print("\n" + "=" * 80)
        print("Step 1: Parse DBC")
        print("=" * 80)
        response = send_command(proc, {
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc_json
        })

        if not response or response.get("status") != "success":
            print(f"FAIL: Expected success response, got: {response}")
            return 1
        print("✓ DBC parsed successfully")

        # Step 2: Set LTL properties
        print("\n" + "=" * 80)
        print("Step 2: Set LTL Properties (Speed < 250)")
        print("=" * 80)
        response = send_command(proc, {
            "type": "command",
            "command": "setProperties",
            "properties": [
                {
                    "operator": "always",
                    "formula": {
                        "operator": "atomic",
                        "predicate": {
                            "predicate": "lessThan",
                            "signal": "Speed",
                            "value": 250
                        }
                    }
                }
            ]
        })

        if not response or response.get("status") != "success":
            print(f"FAIL: Expected success response, got: {response}")
            return 1
        print("✓ Properties set successfully")

        # Step 3: Start streaming
        print("\n" + "=" * 80)
        print("Step 3: Start Streaming")
        print("=" * 80)
        response = send_command(proc, {
            "type": "command",
            "command": "startStream"
        })

        if not response or response.get("status") != "success":
            print(f"FAIL: Expected success response, got: {response}")
            return 1
        print("✓ Streaming started")

        # Step 4: Send data frames
        print("\n" + "=" * 80)
        print("Step 4: Send Data Frames")
        print("=" * 80)

        # Frame 1: Speed = 100 km/h (raw value = 1000) - PASSES property (< 250)
        print("\nFrame 1: Speed = 100 km/h (should pass)")
        response = send_command(proc, {
            "type": "data",
            "timestamp": 100,
            "id": 256,
            "data": [0xE8, 0x03, 0, 0, 0, 0, 0, 0]  # 1000 little-endian = 0x03E8
        })
        print(f"Response type: {response.get('type') if response else 'None'}")

        # Frame 2: Speed = 200 km/h (raw value = 2000) - PASSES property (< 250)
        print("\nFrame 2: Speed = 200 km/h (should pass)")
        response = send_command(proc, {
            "type": "data",
            "timestamp": 200,
            "id": 256,
            "data": [0xD0, 0x07, 0, 0, 0, 0, 0, 0]  # 2000 little-endian = 0x07D0
        })
        print(f"Response type: {response.get('type') if response else 'None'}")

        # Frame 3: Speed = 260 km/h (raw value = 2600) - VIOLATES property (>= 250)
        print("\nFrame 3: Speed = 260 km/h (should VIOLATE property)")
        response = send_command(proc, {
            "type": "data",
            "timestamp": 300,
            "id": 256,
            "data": [0x28, 0x0A, 0, 0, 0, 0, 0, 0]  # 2600 little-endian = 0x0A28
        })

        if response and response.get("type") == "property":
            status = response.get("status")
            if status == "violation":
                print("✓ Property violation detected correctly!")
                print(f"  Property index: {response.get('property_index')}")
                print(f"  Timestamp: {response.get('timestamp')}")
                print(f"  Reason: {response.get('reason')}")
            else:
                print(f"FAIL: Expected violation, got status: {status}")
                return 1
        else:
            print(f"FAIL: Expected property response, got: {response}")
            return 1

        # Step 5: End streaming
        print("\n" + "=" * 80)
        print("Step 5: End Streaming")
        print("=" * 80)
        response = send_command(proc, {
            "type": "command",
            "command": "endStream"
        })

        if not response or response.get("status") != "complete":
            print(f"FAIL: Expected complete response, got: {response}")
            return 1
        print("✓ Streaming ended successfully")

        print("\n" + "=" * 80)
        print("ALL TESTS PASSED! ✓")
        print("=" * 80)

        return 0

    finally:
        proc.stdin.close()
        proc.wait(timeout=5)

if __name__ == "__main__":
    sys.exit(main())
