"""Phase 2B JSON Streaming Client

Provides a streaming interface to the Aletheia binary using JSON line protocol.
Maintains a persistent subprocess for incremental LTL checking.
"""

from __future__ import annotations

import subprocess
import json
from pathlib import Path
from typing import cast

from aletheia.protocols import (
    Command,
    Response,
    DBCDefinition,
    LTLFormula,
    SuccessResponse,
    CompleteResponse,
)


# ============================================================================
# CUSTOM EXCEPTIONS
# ============================================================================

class AletheiaError(Exception):
    """Base exception for all Aletheia errors"""


class ProcessError(AletheiaError):
    """Subprocess-related errors (not running, terminated unexpectedly, etc.)"""


class ProtocolError(AletheiaError):
    """Protocol-related errors (invalid JSON, missing response, etc.)"""


# ============================================================================
# BINARY LOCATION
# ============================================================================

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
            f"Aletheia binary not found at {binary}. " +
            "Please build it first with: cabal run shake -- build"
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
        from aletheia.dbc_converter import dbc_to_json

        dbc_json = dbc_to_json("example.dbc")
        property = Signal("Speed").less_than(220).always().to_dict()

        with StreamingClient() as client:
            client.parse_dbc(dbc_json)
            client.set_properties([property])
            client.start_stream()

            for frame in can_trace:
                response = client.send_frame(frame.timestamp, frame.can_id, frame.data)
                if response.get("type") == "property":
                    # Handle property violation
                    pass

            client.end_stream()
    """

    def __init__(self, shutdown_timeout: float = 5.0):
        """Initialize the streaming client (does not start subprocess yet)

        Args:
            shutdown_timeout: Timeout in seconds for graceful shutdown (default: 5.0)
        """
        self.binary_path: Path = get_binary_path()
        self.proc: subprocess.Popen[str] | None = None
        self.shutdown_timeout: float = shutdown_timeout

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

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: object
    ) -> None:
        """Clean up the subprocess when exiting context

        Tries graceful termination first, then force kill if needed.
        """
        if self.proc:
            self.proc.terminate()
            try:
                _ = self.proc.wait(timeout=self.shutdown_timeout)
            except subprocess.TimeoutExpired:
                # Graceful termination failed, force kill
                self.proc.kill()
                _ = self.proc.wait()  # Wait for kill to complete

    def _send_command(self, command: Command) -> Response:
        """Send a JSON command and receive response

        Args:
            command: Command object (ParseDBCCommand, SetPropertiesCommand, etc.)

        Returns:
            Response object (SuccessResponse, ErrorResponse, etc.)

        Raises:
            ProcessError: If subprocess is not running or terminated unexpectedly
            ProtocolError: If JSON communication fails
        """
        if not self.proc or not self.proc.stdin or not self.proc.stdout:
            raise ProcessError("Subprocess not running")

        # Send command as JSON line
        json_line = json.dumps(command)
        _ = self.proc.stdin.write(json_line + "\n")
        self.proc.stdin.flush()

        # Read response as JSON line
        response_line = self.proc.stdout.readline()
        if not response_line:
            # Check if process died
            if self.proc.poll() is not None:
                stderr = self.proc.stderr.read() if self.proc.stderr else ""
                raise ProcessError(f"Binary process terminated unexpectedly: {stderr}")
            raise ProtocolError("No response from binary")

        try:
            # Parse JSON and cast to Response type (runtime validation would happen here)
            return cast(Response, json.loads(response_line))
        except json.JSONDecodeError as e:
            raise ProtocolError(f"Invalid JSON response: {response_line!r} - {e}") from e

    def parse_dbc(self, dbc: DBCDefinition) -> SuccessResponse:
        """Parse DBC file

        Args:
            dbc: DBC structure (use dbc_converter.dbc_to_json())

        Returns:
            SuccessResponse: {"status": "success", "message": "DBC parsed successfully"}

        Example:
            from aletheia.dbc_converter import dbc_to_json
            dbc_json = dbc_to_json("example.dbc")
            client.parse_dbc(dbc_json)
        """
        response = self._send_command({
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        })
        return cast(SuccessResponse, response)

    def set_properties(self, properties: list[LTLFormula]) -> SuccessResponse:
        """Set LTL properties to check

        Args:
            properties: List of LTL formulas (from DSL)

        Returns:
            SuccessResponse: {"status": "success", "message": "Properties set successfully"}
        """
        response = self._send_command({
            "type": "command",
            "command": "setProperties",
            "properties": properties
        })
        return cast(SuccessResponse, response)

    def start_stream(self) -> SuccessResponse:
        """Start streaming data frames

        Returns:
            SuccessResponse: {"status": "success", "message": "Streaming started"}
        """
        response = self._send_command({
            "type": "command",
            "command": "startStream"
        })
        return cast(SuccessResponse, response)

    def send_frame(self, timestamp: int, can_id: int, data: list[int]) -> Response:
        """Send a CAN frame for incremental checking

        Args:
            timestamp: Timestamp in microseconds
            can_id: CAN ID (11-bit standard)
            data: 8-byte payload as list of integers [0-255]

        Returns:
            Response: Either AckResponse or PropertyViolationResponse
        """
        if len(data) != 8:
            raise ValueError(f"Data must be exactly 8 bytes, got {len(data)}")

        return self._send_command({
            "type": "data",
            "timestamp": timestamp,
            "id": can_id,
            "data": data
        })

    def end_stream(self) -> CompleteResponse:
        """End streaming and get final results

        Returns:
            CompleteResponse: {"status": "complete"}
        """
        response = self._send_command({
            "type": "command",
            "command": "endStream"
        })
        return cast(CompleteResponse, response)
