#!/usr/bin/env python3
"""
Simple test to verify basic protocol communication works.
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
    # Find binary relative to project root
    project_root = Path(__file__).parent.parent.parent
    binary_path = project_root / "build" / "aletheia"
    if not binary_path.exists():
        print(f"ERROR: {binary_path} not found")
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
        # Test 1: Try startStream (simplest command - no params)
        print("\n" + "=" * 80)
        print("Test 1: startStream (should fail - no DBC loaded yet)")
        print("=" * 80)
        response = send_command(proc, {
            "type": "command",
            "command": "startStream"
        })
        print(f"Response: {response}")
        print(f"Status field: {response.get('status')}")

        # Test 2: Try parseDBC with inline DBC JSON
        print("\n" + "=" * 80)
        print("Test 2: parseDBC with embedded DBC JSON")
        print("=" * 80)

        dbc_data = {
            "version": "1.0",
            "messages": [{
                "id": 256,
                "name": "TestMsg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [{
                    "name": "TestSignal",
                    "startBit": 0,
                    "length": 8,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 1.0,
                    "offset": 0.0,
                    "minimum": 0.0,
                    "maximum": 255.0,
                    "unit": "",
                    "presence": "always"
                }]
            }]
        }

        response = send_command(proc, {
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc_data
        })
        print(f"Response: {response}")
        print(f"Status field: {response.get('status')}")

        return 0

    finally:
        proc.stdin.close()
        proc.wait(timeout=5)

if __name__ == "__main__":
    sys.exit(main())
