"""Phase 2B JSON Streaming Client

Provides a streaming interface to the Aletheia binary using JSON line protocol.
Maintains a persistent subprocess for incremental LTL checking.
"""

import subprocess
import json
from pathlib import Path
from typing import Dict, Any, Optional, List


def get_binary_path() -> Path:
    """Locate the Aletheia binary

    Returns:
        Path to the binary

    Raises:
        FileNotFoundError: If binary not found
    """
    module_dir = Path(__file__).parent
    repo_root = module_dir.parent.parent
    binary = repo_root / "build" / "aletheia"

    if not binary.exists():
        raise FileNotFoundError(
            f"Aletheia binary not found at {binary}. "
            f"Please build it first with: cabal run shake -- build"
        )

    return binary


class StreamingClient:
    """JSON streaming client for incremental LTL checking

    Protocol:
    1. Send ParseDBC command
    2. Send SetProperties command
    3. Send StartStream command
    4. Send DataFrame messages (one per CAN frame)
    5. Receive PropertyResponse for violations or Ack for clean frames
    6. Send EndStream command when done

    Example:
        with StreamingClient() as client:
            client.parse_dbc(dbc_yaml)
            client.set_properties([prop1, prop2])
            client.start_stream()

            for frame in can_trace:
                response = client.send_frame(frame.timestamp, frame.can_id, frame.data)
                if response.get("type") == "property":
                    # Handle property violation
                    pass

            client.end_stream()
    """

    def __init__(self):
        """Initialize the streaming client (does not start subprocess yet)"""
        self.binary_path = get_binary_path()
        self.proc: Optional[subprocess.Popen] = None

    def __enter__(self):
        """Start the subprocess when entering context"""
        self.proc = subprocess.Popen(
            [str(self.binary_path)],  # No args = JSON streaming mode
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1  # Line buffered
        )
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Clean up the subprocess when exiting context"""
        if self.proc:
            self.proc.terminate()
            self.proc.wait(timeout=5)

    def _send_command(self, command: Dict[str, Any]) -> Dict[str, Any]:
        """Send a JSON command and receive response

        Args:
            command: Command dictionary

        Returns:
            Response dictionary

        Raises:
            RuntimeError: If subprocess is not running or communication fails
        """
        if not self.proc or not self.proc.stdin or not self.proc.stdout:
            raise RuntimeError("Subprocess not running")

        # Send command as JSON line
        json_line = json.dumps(command)
        self.proc.stdin.write(json_line + "\n")
        self.proc.stdin.flush()

        # Read response as JSON line
        response_line = self.proc.stdout.readline()
        if not response_line:
            # Check if process died
            if self.proc.poll() is not None:
                stderr = self.proc.stderr.read() if self.proc.stderr else ""
                raise RuntimeError(f"Binary process terminated unexpectedly: {stderr}")
            raise RuntimeError("No response from binary")

        try:
            return json.loads(response_line)
        except json.JSONDecodeError as e:
            raise RuntimeError(f"Invalid JSON response: {response_line!r} - {e}")

    def parse_dbc(self, dbc_yaml: str) -> Dict[str, Any]:
        """Parse DBC file

        Args:
            dbc_yaml: DBC YAML content

        Returns:
            Response: {"status": "success", "message": "DBC parsed successfully"}
        """
        return self._send_command({
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc_yaml
        })

    def set_properties(self, properties: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Set LTL properties to check

        Args:
            properties: List of LTL property JSON objects (from DSL)

        Returns:
            Response: {"status": "success", "message": "Properties set successfully"}
        """
        return self._send_command({
            "type": "command",
            "command": "setProperties",
            "properties": properties
        })

    def start_stream(self) -> Dict[str, Any]:
        """Start streaming data frames

        Returns:
            Response: {"status": "success", "message": "Streaming started"}
        """
        return self._send_command({
            "type": "command",
            "command": "startStream"
        })

    def send_frame(self, timestamp: int, can_id: int, data: List[int]) -> Dict[str, Any]:
        """Send a CAN frame for incremental checking

        Args:
            timestamp: Timestamp in microseconds
            can_id: CAN ID (11-bit standard)
            data: 8-byte payload as list of integers [0-255]

        Returns:
            Response: Either {"status": "ack"} or PropertyResponse
        """
        if len(data) != 8:
            raise ValueError(f"Data must be exactly 8 bytes, got {len(data)}")

        return self._send_command({
            "type": "data",
            "timestamp": timestamp,
            "id": can_id,
            "data": data
        })

    def end_stream(self) -> Dict[str, Any]:
        """End streaming and get final results

        Returns:
            Response: {"status": "complete"}
        """
        return self._send_command({
            "type": "command",
            "command": "endStream"
        })
