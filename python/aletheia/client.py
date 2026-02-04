"""Unified Aletheia Client

Provides a single client that combines streaming LTL checking with signal
extraction and encoding operations over a single subprocess.

This is more efficient than using separate StreamingClient and SignalExtractor
instances, which each spawn their own subprocess.

Example:
    from aletheia import AletheiaClient, Signal
    from aletheia.dbc_converter import dbc_to_json

    dbc = dbc_to_json("vehicle.dbc")

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Signal operations work anytime after DBC is loaded
        result = client.extract_signals(can_id=0x100, data=[0x00] * 8)
        speed = result.get("VehicleSpeed", 0.0)

        # Build a frame from signal values
        frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 50.0})

        # Streaming LTL checking
        client.set_properties([Signal("VehicleSpeed").less_than(120).always().to_dict()])
        client.start_stream()

        for ts, can_id, data in frames:
            # Can still use signal operations while streaming!
            modified = client.update_frame(can_id, data, {"VehicleSpeed": 130.0})
            response = client.send_frame(ts, can_id, modified)

        client.end_stream()
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
    BuildFrameCommand,
    ExtractSignalsCommand,
    UpdateFrameCommand,
    SuccessResponse,
    CompleteResponse,
    AckResponse,
    PropertyViolationResponse,
    ErrorResponse,
    RationalNumber,
    SignalValue,
)


class AletheiaError(Exception):
    """Base exception for all Aletheia errors"""


class ProcessError(AletheiaError):
    """Subprocess-related errors (not running, terminated unexpectedly, etc.)"""


class ProtocolError(AletheiaError):
    """Protocol-related errors (invalid JSON, missing response, etc.)"""


class SignalExtractionResult:
    """
    Rich result object for signal extraction.

    Partitions extraction results into three categories:
    - values: Successfully extracted signal values
    - errors: Extraction errors with reasons
    - absent: Multiplexed signals not present in this frame
    """

    values: dict[str, float]
    errors: dict[str, str]
    absent: list[str]

    def __init__(
        self,
        values: dict[str, float],
        errors: dict[str, str],
        absent: list[str]
    ):
        self.values = values
        self.errors = errors
        self.absent = absent

    def get(self, signal_name: str, default: float = 0.0) -> float:
        """Get signal value with default fallback."""
        return self.values.get(signal_name, default)

    def has_errors(self) -> bool:
        """Check if any extraction errors occurred."""
        return len(self.errors) > 0

    @override
    def __repr__(self) -> str:
        return (
            f"SignalExtractionResult("
            f"values={len(self.values)}, "
            f"errors={len(self.errors)}, "
            f"absent={len(self.absent)})"
        )


class AletheiaClient(BinaryClient):
    """Unified client for streaming LTL checking and signal operations.

    Combines the functionality of StreamingClient, SignalExtractor, and
    FrameBuilder in a single subprocess for efficiency.

    Protocol state machine:
    1. parse_dbc() - Load DBC definition (required first)
    2. Signal operations available anytime after DBC loaded:
       - extract_signals() - Extract all signals from a frame
       - update_frame() - Update specific signals in a frame
       - build_frame() - Build a frame from signal values
    3. Streaming LTL checking:
       - set_properties() - Set LTL properties (before streaming)
       - start_stream() - Enter streaming mode
       - send_frame() - Send frames for incremental checking
       - end_stream() - Exit streaming mode

    Signal operations work both inside and outside streaming mode.
    """

    @staticmethod
    def _validate_rational(field_name: str, raw_value: object) -> RationalNumber:
        """Validate and extract RationalNumber from response field."""
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

    @staticmethod
    def _parse_rational(value_raw: object) -> float:
        """Parse a value that may be a number or a rational string like '72/1'."""
        if isinstance(value_raw, (int, float)):
            return float(value_raw)
        if isinstance(value_raw, str):
            if "/" in value_raw:
                parts = value_raw.split("/")
                if len(parts) == 2:
                    try:
                        numerator = int(parts[0])
                        denominator = int(parts[1])
                        if denominator != 0:
                            return numerator / denominator
                    except ValueError:
                        pass
            try:
                return float(value_raw)
            except ValueError:
                pass
        raise AssertionError(
            f"Protocol error: expected signal value to be number or rational string, "
            f"got {type(value_raw).__name__}: {value_raw!r}"
        )

    def __init__(self, shutdown_timeout: float = 5.0):
        """Initialize the client (does not start subprocess yet).

        Args:
            shutdown_timeout: Timeout in seconds for graceful shutdown (default: 5.0)
        """
        super().__init__(shutdown_timeout=shutdown_timeout)

    @override
    def __enter__(self) -> "AletheiaClient":
        """Start the subprocess when entering context."""
        self._start_subprocess()
        return self

    @override
    def _send_command(self, command: Command) -> Response:
        """Send a command and receive response."""
        try:
            return super()._send_command(command)
        except RuntimeError as e:
            error_msg = str(e)
            if "not running" in error_msg or "terminated" in error_msg:
                raise ProcessError(error_msg) from e
            raise ProtocolError(error_msg) from e

    # =========================================================================
    # DBC and Properties
    # =========================================================================

    def parse_dbc(self, dbc: DBCDefinition) -> SuccessResponse | ErrorResponse:
        """Parse DBC file. Must be called first.

        Args:
            dbc: DBC structure (use dbc_converter.dbc_to_json())

        Returns:
            SuccessResponse or ErrorResponse
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
        """Set LTL properties to check. Must be called before start_stream().

        Args:
            properties: List of LTL formulas (from DSL .to_dict())

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

    # =========================================================================
    # Streaming LTL Checking
    # =========================================================================

    def start_stream(self) -> SuccessResponse | ErrorResponse:
        """Start streaming mode for incremental LTL checking.

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
        """Send a CAN frame for incremental LTL checking.

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
        status = response.get("status")

        if status == "ack":
            return {"status": ResponseStatus.ACK}

        if status == "violation":
            prop_type = response.get("type")
            if prop_type != "property":
                raise ProtocolError(f"Protocol error: expected type='property', got {prop_type}")

            prop_index = self._validate_rational("property_index", response.get("property_index"))
            ts_rational = self._validate_rational("timestamp", response.get("timestamp"))

            result_violation: PropertyViolationResponse = {
                "status": "violation",
                "type": "property",
                "property_index": prop_index,
                "timestamp": ts_rational
            }

            reason = response.get("reason")
            if isinstance(reason, str):
                result_violation["reason"] = reason

            return result_violation

        if status == "error":
            message = response.get("message")
            result_error: ErrorResponse = {"status": ResponseStatus.ERROR, "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(f"Unexpected response status: {status}")

    def send_frames_batch(
        self,
        frames: list[tuple[int, int, list[int]]]
    ) -> list[AckResponse | PropertyViolationResponse | ErrorResponse]:
        """Send multiple CAN frames in a batch for better throughput.

        This method amortizes IPC overhead by sending all frames before reading
        responses. Use this for high-throughput scenarios.

        Args:
            frames: List of (timestamp, can_id, data) tuples where:
                - timestamp: Timestamp in microseconds
                - can_id: CAN ID (11-bit standard)
                - data: 8-byte payload as list of integers [0-255]

        Returns:
            List of responses (AckResponse, PropertyViolationResponse, or ErrorResponse)
            in same order as input frames.

        Raises:
            ValueError: If any frame data is not exactly 8 bytes
            ProtocolError: If response status is unexpected
        """
        # Validate all frames first
        for i, (_, _, data) in enumerate(frames):
            if len(data) != 8:
                raise ValueError(f"Frame {i}: data must be exactly 8 bytes, got {len(data)}")

        # Build all frame commands
        commands: list[DataFrame] = []
        for timestamp, can_id, data in frames:
            frame: DataFrame = {
                "type": "data",
                "timestamp": timestamp,
                "id": can_id,
                "data": data
            }
            commands.append(frame)

        # Send batch and get responses
        raw_responses = self._send_batch(commands)  # type: ignore[arg-type]

        # Parse responses
        results: list[AckResponse | PropertyViolationResponse | ErrorResponse] = []
        for response in raw_responses:
            status = response.get("status")

            if status == "ack":
                results.append({"status": ResponseStatus.ACK})
            elif status == "violation":
                prop_index = self._validate_rational("property_index", response.get("property_index"))
                ts_rational = self._validate_rational("timestamp", response.get("timestamp"))
                result_violation: PropertyViolationResponse = {
                    "status": "violation",
                    "type": "property",
                    "property_index": prop_index,
                    "timestamp": ts_rational
                }
                reason = response.get("reason")
                if isinstance(reason, str):
                    result_violation["reason"] = reason
                results.append(result_violation)
            elif status == "error":
                message = response.get("message")
                result_error: ErrorResponse = {"status": ResponseStatus.ERROR, "message": ""}
                if isinstance(message, str):
                    result_error["message"] = message
                results.append(result_error)
            else:
                raise ProtocolError(f"Unexpected response status: {status}")

        return results

    def end_stream(self) -> CompleteResponse | ErrorResponse:
        """End streaming mode.

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
            return {"status": ResponseStatus.COMPLETE}

        if status == "error":
            result_error: ErrorResponse = {"status": ResponseStatus.ERROR, "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(f"Unexpected response status: {status}")

    # =========================================================================
    # Signal Operations (available anytime after DBC loaded)
    # =========================================================================

    def extract_signals(self, can_id: int, data: list[int]) -> SignalExtractionResult:
        """Extract all signals from a CAN frame.

        Works both inside and outside streaming mode.

        Args:
            can_id: CAN message ID
            data: 8-byte frame data (list of integers 0-255)

        Returns:
            SignalExtractionResult with values/errors/absent partitioning

        Raises:
            ValueError: If data is not exactly 8 bytes
            RuntimeError: If extraction fails
        """
        if len(data) != 8:
            raise ValueError(f"Frame data must be 8 bytes, got {len(data)}")

        cmd: ExtractSignalsCommand = {
            "type": "command",
            "command": "extractAllSignals",
            "canId": can_id,
            "data": data
        }
        response = self._send_command(cmd)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise RuntimeError(f"Extract signals failed: {error_msg}")

        # Parse response
        values_raw = response.get("values", [])
        assert isinstance(values_raw, list), "Protocol error: expected 'values' to be a list"
        values = self._parse_values_list(cast(list[object], values_raw))

        errors_raw = response.get("errors", [])
        assert isinstance(errors_raw, list), "Protocol error: expected 'errors' to be a list"
        errors = self._parse_errors_list(cast(list[object], errors_raw))

        absent_raw = response.get("absent", [])
        assert isinstance(absent_raw, list), "Protocol error: expected 'absent' to be a list"
        absent = self._parse_absent_list(cast(list[object], absent_raw))

        return SignalExtractionResult(values=values, errors=errors, absent=absent)

    def update_frame(
        self,
        can_id: int,
        frame: list[int],
        signals: dict[str, float]
    ) -> list[int]:
        """Update specific signals in an existing frame.

        Works both inside and outside streaming mode.
        Immutable - returns new frame, original unchanged.

        Args:
            can_id: CAN message ID
            frame: Existing 8-byte frame data
            signals: Signal updates (name -> value)

        Returns:
            New 8-byte frame with updated signals

        Raises:
            ValueError: If frame is not exactly 8 bytes
            RuntimeError: If update fails
        """
        if len(frame) != 8:
            raise ValueError(f"Frame data must be 8 bytes, got {len(frame)}")

        signals_json: list[SignalValue] = [
            SignalValue(name=name, value=value)
            for name, value in signals.items()
        ]

        cmd: UpdateFrameCommand = {
            "type": "command",
            "command": "updateFrame",
            "canId": can_id,
            "data": frame,
            "signals": signals_json
        }
        response = self._send_command(cmd)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise RuntimeError(f"Update frame failed: {error_msg}")

        if "data" not in response:
            raise RuntimeError("Invalid response: missing 'data' field")

        frame_data = response["data"]
        if not isinstance(frame_data, list) or len(frame_data) != 8:  # pyright: ignore[reportUnnecessaryIsInstance]
            raise RuntimeError(f"Invalid frame data: expected 8-byte list, got {frame_data}")

        result: list[int] = []
        for b in frame_data:
            if not isinstance(b, int):  # pyright: ignore[reportUnnecessaryIsInstance]
                raise RuntimeError(f"Frame data must contain only integers, got {type(b).__name__}")
            result.append(b)
        return result

    def build_frame(self, can_id: int, signals: dict[str, float]) -> list[int]:
        """Build a CAN frame from signal values.

        Works both inside and outside streaming mode.
        Starts with a zero-filled frame and encodes the given signals.

        Args:
            can_id: CAN message ID
            signals: Signal values to encode (name -> value)

        Returns:
            8-byte CAN frame as list of integers (0-255)

        Raises:
            RuntimeError: If frame building fails
        """
        signals_json: list[SignalValue] = [
            SignalValue(name=name, value=value)
            for name, value in signals.items()
        ]

        cmd: BuildFrameCommand = {
            "type": "command",
            "command": "buildFrame",
            "canId": can_id,
            "signals": signals_json
        }
        response = self._send_command(cmd)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise RuntimeError(f"Build frame failed: {error_msg}")

        if "frame" not in response:
            # Try "data" field (protocol variation)
            if "data" in response:
                frame_data = response["data"]
            else:
                raise RuntimeError("Invalid response: missing 'frame' or 'data' field")
        else:
            frame_data = response["frame"]

        if not isinstance(frame_data, list) or len(frame_data) != 8:  # pyright: ignore[reportUnnecessaryIsInstance]
            raise RuntimeError(f"Invalid frame data: expected 8-byte list, got {frame_data}")

        result: list[int] = []
        for b in frame_data:
            if not isinstance(b, int):  # pyright: ignore[reportUnnecessaryIsInstance]
                raise RuntimeError(f"Frame data must contain only integers, got {type(b).__name__}")
            result.append(b)
        return result

    # =========================================================================
    # Helper methods for parsing responses
    # =========================================================================

    @staticmethod
    def _parse_values_list(values_data: list[object]) -> dict[str, float]:
        """Parse signal values list from response."""
        values: dict[str, float] = {}
        for item in values_data:
            assert isinstance(item, dict), \
                f"Protocol error: expected signal value to be dict, got {type(item)}"
            item_dict = cast(dict[str, object], item)
            name_raw = item_dict.get("name")
            assert isinstance(name_raw, str), \
                f"Protocol error: expected signal name to be str, got {type(name_raw)}"
            value_raw = item_dict.get("value")
            values[name_raw] = AletheiaClient._parse_rational(value_raw)
        return values

    @staticmethod
    def _parse_errors_list(errors_data: list[object]) -> dict[str, str]:
        """Parse signal errors list from response."""
        errors: dict[str, str] = {}
        for item in errors_data:
            assert isinstance(item, dict), \
                f"Protocol error: expected error item to be dict, got {type(item)}"
            item_dict = cast(dict[str, object], item)
            name_raw = item_dict.get("name")
            assert isinstance(name_raw, str), \
                f"Protocol error: expected error signal name to be str, got {type(name_raw)}"
            error_raw = item_dict.get("error")
            assert isinstance(error_raw, str), \
                f"Protocol error: expected error message to be str, got {type(error_raw)}"
            errors[name_raw] = error_raw
        return errors

    @staticmethod
    def _parse_absent_list(absent_data: list[object]) -> list[str]:
        """Parse absent signals list from response."""
        absent: list[str] = []
        for item in absent_data:
            assert isinstance(item, str), \
                f"Protocol error: expected absent signal name to be str, got {type(item)}"
            absent.append(item)
        return absent

    @override
    def __repr__(self) -> str:
        return "AletheiaClient()"
