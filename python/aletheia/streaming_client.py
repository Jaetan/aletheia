"""Phase 2B JSON Streaming Client

Provides a streaming interface to the Aletheia binary using JSON line protocol.
Maintains a persistent subprocess for incremental LTL checking.
"""

from __future__ import annotations

from typing import override, cast

from .binary_client import BinaryClient
from .protocols import (
    DBCDefinition,
    LTLFormula,
    ResponseStatus,
    Command,
    Response,
    ParseDBCCommand,
    SetPropertiesCommand,
    StartStreamCommand,
    EndStreamCommand,
    DataFrame,
    SuccessResponse,
    CompleteResponse,
    AckResponse,
    PropertyViolationResponse,
    ErrorResponse,
    RationalNumber,
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

    @staticmethod
    def _validate_rational(field_name: str, raw_value: object) -> RationalNumber:
        """Validate and extract RationalNumber from response field

        Agda's formatRational outputs integers with denominator 1 as plain
        numbers (e.g. ``0``) and non-integers as
        ``{"numerator": n, "denominator": d}``.  This helper accepts both.

        Args:
            field_name: Name of field for error messages
            raw_value: Raw value from response.get()

        Returns:
            Validated RationalNumber

        Raises:
            AssertionError: If structure is invalid (protocol violation)
        """
        if isinstance(raw_value, int):
            return {"numerator": raw_value, "denominator": 1}
        assert isinstance(raw_value, dict), \
            f"Protocol error: expected {field_name} to be int or dict, got {type(raw_value).__name__}"
        value_dict = cast(dict[str, object], raw_value)
        numerator = value_dict.get("numerator")
        denominator = value_dict.get("denominator")
        assert isinstance(numerator, int), \
            f"Protocol error: expected {field_name}.numerator to be int"
        assert isinstance(denominator, int), \
            f"Protocol error: expected {field_name}.denominator to be int"
        return {"numerator": numerator, "denominator": denominator}

    def __init__(self, shutdown_timeout: float = 5.0):
        """Initialize the streaming client (does not start subprocess yet)

        Args:
            shutdown_timeout: Timeout in seconds for graceful shutdown (default: 5.0)
        """
        super().__init__(shutdown_timeout=shutdown_timeout)

    @override
    def __enter__(self):
        """Start the subprocess when entering context"""
        self._start_subprocess()
        return super().__enter__()

    @override
    def _send_command(self, command: Command) -> Response:
        """Send a command and receive response

        Args:
            command: Command (specific TypedDict type)

        Returns:
            Response (specific TypedDict type)

        Raises:
            ProcessError: If subprocess is not running or terminated unexpectedly
            ProtocolError: If JSON communication fails
        """
        try:
            # Use base class implementation
            return super()._send_command(command)
        except RuntimeError as e:
            # Convert RuntimeError to more specific exceptions
            error_msg = str(e)
            if "not running" in error_msg or "terminated" in error_msg:
                raise ProcessError(error_msg) from e
            raise ProtocolError(error_msg) from e

    def parse_dbc(self, dbc: DBCDefinition) -> SuccessResponse | ErrorResponse:
        """Parse DBC file

        Args:
            dbc: DBC structure (use dbc_converter.dbc_to_json())

        Returns:
            SuccessResponse or ErrorResponse

        Example:
            from aletheia.dbc_converter import dbc_to_json
            dbc_json = dbc_to_json("example.dbc")
            response = client.parse_dbc(dbc_json)
            if response["status"] == "error":
                print(f"Error: {response['message']}")
        """
        cmd: ParseDBCCommand = {
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        }
        response = self._send_command(cmd)
        status = response.get("status")
        message = response.get("message")

        if status == "success":
            result_success: SuccessResponse = {"status": ResponseStatus.SUCCESS}
            if isinstance(message, str):
                result_success["message"] = message
            return result_success

        if status == "error":
            result_error: ErrorResponse = {"status": ResponseStatus.ERROR, "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(f"Unexpected response status: {status}")

    def set_properties(self, properties: list[LTLFormula]) -> SuccessResponse | ErrorResponse:
        """Set LTL properties to check

        Args:
            properties: List of LTL formulas (from DSL)

        Returns:
            SuccessResponse or ErrorResponse
        """
        cmd: SetPropertiesCommand = {
            "type": "command",
            "command": "setProperties",
            "properties": properties
        }
        response = self._send_command(cmd)
        status = response.get("status")
        message = response.get("message")

        if status == "success":
            result_success: SuccessResponse = {"status": ResponseStatus.SUCCESS}
            if isinstance(message, str):
                result_success["message"] = message
            return result_success

        if status == "error":
            result_error: ErrorResponse = {"status": ResponseStatus.ERROR, "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(f"Unexpected response status: {status}")

    def start_stream(self) -> SuccessResponse | ErrorResponse:
        """Start streaming data frames

        Returns:
            SuccessResponse or ErrorResponse
        """
        cmd: StartStreamCommand = {
            "type": "command",
            "command": "startStream"
        }
        response = self._send_command(cmd)
        status = response.get("status")
        message = response.get("message")

        if status == "success":
            result_success: SuccessResponse = {"status": ResponseStatus.SUCCESS}
            if isinstance(message, str):
                result_success["message"] = message
            return result_success

        if status == "error":
            result_error: ErrorResponse = {"status": ResponseStatus.ERROR, "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(f"Unexpected response status: {status}")

    def send_frame(
        self,
        timestamp: int,
        can_id: int,
        data: list[int]
    ) -> AckResponse | PropertyViolationResponse | ErrorResponse:
        """Send a CAN frame for incremental checking

        Args:
            timestamp: Timestamp in microseconds
            can_id: CAN ID (11-bit standard)
            data: 8-byte payload as list of integers [0-255]

        Returns:
            AckResponse, PropertyViolationResponse, or ErrorResponse
        """
        if len(data) != 8:
            raise ValueError(f"Data must be exactly 8 bytes, got {len(data)}")

        frame: DataFrame = {
            "type": "data",
            "timestamp": timestamp,
            "id": can_id,
            "data": data
        }
        response = self._send_command(frame)

        # Check response type and construct appropriate response
        status = response.get("status")

        if status == "ack":
            result_ack: AckResponse = {"status": ResponseStatus.ACK}
            return result_ack

        if status == "violation":
            # PropertyViolationResponse - strict validation of internal protocol
            prop_type = response.get("type")
            if prop_type != "property":
                raise ProtocolError(f"Protocol error: expected type='property', got {prop_type}")

            # Validate and extract RationalNumber fields using helper
            prop_index: RationalNumber = self._validate_rational(
                "property_index", response.get("property_index")
            )
            ts_rational: RationalNumber = self._validate_rational(
                "timestamp", response.get("timestamp")
            )

            # Construct PropertyViolationResponse with validated RationalNumbers
            result_violation: PropertyViolationResponse = {
                "status": "violation",
                "type": "property",
                "property_index": prop_index,
                "timestamp": ts_rational
            }

            # Optional reason field
            reason = response.get("reason")
            if isinstance(reason, str):
                result_violation["reason"] = reason

            return result_violation

        if status == "error":
            # ErrorResponse
            message = response.get("message")
            result_error: ErrorResponse = {"status": ResponseStatus.ERROR, "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(f"Unexpected response status: {status}")

    def end_stream(self) -> CompleteResponse | ErrorResponse:
        """End streaming and get final results

        Returns:
            CompleteResponse or ErrorResponse
        """
        cmd: EndStreamCommand = {
            "type": "command",
            "command": "endStream"
        }
        response = self._send_command(cmd)
        status = response.get("status")
        message = response.get("message")

        if status == "complete":
            result_complete: CompleteResponse = {"status": ResponseStatus.COMPLETE}
            return result_complete

        if status == "error":
            result_error: ErrorResponse = {"status": ResponseStatus.ERROR, "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(f"Unexpected response status: {status}")
