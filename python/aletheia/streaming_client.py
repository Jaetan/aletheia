"""Phase 2B JSON Streaming Client

Provides a streaming interface to the Aletheia binary using JSON line protocol.
Maintains a persistent subprocess for incremental LTL checking.
"""

from __future__ import annotations

import json
from typing import cast

from aletheia.binary_client import BinaryClient
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


class StreamingClient(BinaryClient):
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
        super().__init__(shutdown_timeout=shutdown_timeout)

    def __enter__(self):
        """Start the subprocess when entering context"""
        self._start_subprocess()
        return self

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
        if not self._proc or not self._proc.stdin or not self._proc.stdout:
            raise ProcessError("Subprocess not running")

        # Send command as JSON line
        json_line = json.dumps(command)
        _ = self._proc.stdin.write(json_line + "\n")
        self._proc.stdin.flush()

        # Read response as JSON line
        response_line = self._proc.stdout.readline()
        if not response_line:
            # Check if process died
            if self._proc.poll() is not None:
                stderr = self._proc.stderr.read() if self._proc.stderr else ""
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
