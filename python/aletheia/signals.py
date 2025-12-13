"""
Signal encoding and extraction operations for CAN frames.

This module provides batch signal operations as an independent toolbox,
separate from streaming. Single-signal operations are special cases with
1-element lists.

Classes:
    FrameBuilder: Build CAN frames from signal name-value pairs
    SignalExtractionResult: Rich result object for batch extraction
    SignalExtractor: Extract and update signals in CAN frames
"""

from __future__ import annotations

import copy
from typing import override, cast

from .binary_client import BinaryClient
from .protocols import (
    DBCDefinition,
    SignalValue,
    ParseDBCCommand,
    BuildFrameCommand,
    ExtractSignalsCommand,
    UpdateFrameCommand,
)


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
        """
        Initialize extraction result.

        Args:
            values: Successfully extracted signal values (name -> value)
            errors: Extraction errors (signal name -> error message)
            absent: Multiplexed signals not present (signal names)
        """
        self.values = values
        self.errors = errors
        self.absent = absent

    def get(self, signal_name: str, default: float = 0.0) -> float:
        """
        Get signal value with default fallback.

        Args:
            signal_name: Name of the signal
            default: Default value if signal not in values

        Returns:
            Signal value or default
        """
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


class FrameBuilder(BinaryClient):
    """
    Build CAN frames from signal name-value pairs.

    Immutable builder pattern - each operation returns a new builder.
    Provides fluent interface for readable frame construction.

    Note: Manages a subprocess with DBC pre-loaded for efficiency.
    Use as context manager for proper cleanup, or call close() manually.

    Example:
        >>> with FrameBuilder(can_id=0x100, dbc=dbc_data) as builder:
        ...     frame = (builder
        ...         .set("EngineSpeed", 2000)
        ...         .set("EngineTemp", 90)
        ...         .build())
    """

    def __init__(self, can_id: int, dbc: DBCDefinition):
        """
        Initialize frame builder and start subprocess with DBC loaded.

        Args:
            can_id: CAN message ID
            dbc: DBC definition (from dbc_to_json)

        Raises:
            FileNotFoundError: If binary not found
            RuntimeError: If DBC parsing fails
        """
        super().__init__()
        self._can_id: int = can_id
        self._dbc: DBCDefinition = dbc
        self._signals: dict[str, float] = {}

        # Start subprocess and load DBC
        self._start_subprocess()
        # Send parseDBC command
        parse_cmd: ParseDBCCommand = {
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        }
        _ = self._send_command(parse_cmd)

    def _get_signals_copy(self) -> dict[str, float]:
        """Get a copy of the current signals dict

        Returns a new dict to maintain immutability.

        Returns:
            Copy of signals dictionary
        """
        return self._signals.copy()

    def set(self, signal_name: str, value: float) -> 'FrameBuilder':
        """
        Set a signal value (immutable - returns new builder).

        Note: The new builder shares the subprocess with the original for efficiency.
        Only close the original builder.

        Args:
            signal_name: Name of the signal
            value: Physical signal value (will be scaled/encoded)

        Returns:
            New FrameBuilder with signal added
        """
        # Create new builder sharing subprocess but with independent signals
        new_builder = copy.copy(self)
        # Get copy of signals and add new one
        new_signals = self._get_signals_copy()
        new_signals[signal_name] = value
        # Directly assign using object's __dict__ to avoid protected-access warning
        object.__setattr__(new_builder, '_signals', new_signals)
        return new_builder

    def build(self) -> list[int]:
        """
        Build CAN frame from configured signals.

        Returns:
            8-byte CAN frame as list of integers (0-255)

        Raises:
            RuntimeError: If frame building fails (signal overlap,
                         signal not found, value out of bounds, etc.)
        """
        # Convert signals to JSON format expected by Agda
        signals_json: list[SignalValue] = [
            SignalValue(name=name, value=value)
            for name, value in self._signals.items()
        ]

        # Send buildFrame command
        build_cmd: BuildFrameCommand = {
            "type": "command",
            "command": "buildFrame",
            "canId": self._can_id,
            "signals": signals_json
        }
        response = self._send_command(build_cmd)

        # Check for error response
        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise RuntimeError(f"Build frame failed: {error_msg}")

        # Extract frame bytes from response
        if "frame" not in response:
            raise RuntimeError("Invalid response: missing 'frame' field")

        frame_data = response["frame"]
        # Runtime validation of JSON data (response is from json.loads via _send_command)
        # TypedDict describes expected structure but json.loads can return anything
        if not isinstance(frame_data, list) or len(frame_data) != 8:  # pyright: ignore[reportUnnecessaryIsInstance]
            raise RuntimeError(f"Invalid frame data: expected 8-byte list, got {frame_data}")

        # Validate each byte is an integer (TypedDict doesn't guarantee runtime correctness)
        result: list[int] = []
        for b in frame_data:
            # JSON validation needed - TypedDict is static typing only
            if not isinstance(b, int):  # pyright: ignore[reportUnnecessaryIsInstance]
                raise RuntimeError(
                    f"Frame data must contain only integers, got {type(b).__name__}"
                )
            result.append(b)
        return result

    @override
    def __repr__(self) -> str:
        return (
            f"FrameBuilder("
            f"can_id=0x{self._can_id:X}, "
            f"signals={list(self._signals.keys())})"
        )


class SignalExtractor(BinaryClient):
    """
    Extract and update signals in CAN frames.

    Provides batch extraction and update operations with rich error reporting.
    Independent from streaming - can be used as a standalone toolbox.

    Note: Manages a subprocess with DBC pre-loaded for efficiency.
    Use as context manager for proper cleanup, or call close() manually.

    Example:
        >>> with SignalExtractor(dbc=dbc_data) as extractor:
        ...     result = extractor.extract(can_id=0x100, data=frame_bytes)
        ...     if result.has_errors():
        ...         print(f"Errors: {result.errors}")
        ...     speed = result.get("EngineSpeed", default=0.0)
    """

    @staticmethod
    def _parse_values_list(values_data: list[object]) -> dict[str, float]:
        """Parse signal values list from response"""
        values: dict[str, float] = {}
        for item in values_data:
            assert isinstance(item, dict), \
                f"Protocol error: expected signal value to be dict, got {type(item)}"
            item_dict = cast(dict[str, object], item)
            name_raw = item_dict.get("name")
            assert isinstance(name_raw, str), \
                f"Protocol error: expected signal name to be str, got {type(name_raw)}"
            value_raw = item_dict.get("value")
            assert isinstance(value_raw, (int, float)), \
                f"Protocol error: expected signal value to be number, got {type(value_raw)}"
            values[name_raw] = float(value_raw)
        return values

    @staticmethod
    def _parse_errors_list(errors_data: list[object]) -> dict[str, str]:
        """Parse signal errors list from response"""
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
        """Parse absent signals list from response"""
        absent: list[str] = []
        for item in absent_data:
            assert isinstance(item, str), \
                f"Protocol error: expected absent signal name to be str, got {type(item)}"
            absent.append(item)
        return absent

    def __init__(self, dbc: DBCDefinition):
        """
        Initialize signal extractor and start subprocess with DBC loaded.

        Args:
            dbc: DBC definition (from dbc_to_json)

        Raises:
            FileNotFoundError: If binary not found
            RuntimeError: If DBC parsing fails
        """
        super().__init__()
        self._dbc: DBCDefinition = dbc

        # Start subprocess and load DBC
        self._start_subprocess()
        # Send parseDBC command
        parse_cmd: ParseDBCCommand = {
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        }
        _ = self._send_command(parse_cmd)

    def extract(
        self,
        can_id: int,
        data: list[int]
    ) -> SignalExtractionResult:
        """
        Extract all signals from a CAN frame.

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

        # Send extractAllSignals command
        extract_cmd: ExtractSignalsCommand = {
            "type": "command",
            "command": "extractAllSignals",
            "canId": can_id,
            "data": data
        }
        response = self._send_command(extract_cmd)

        # Check for error response
        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise RuntimeError(f"Extract signals failed: {error_msg}")

        # Parse response into SignalExtractionResult (strict validation of internal protocol)
        # Response is union type, so .get() returns object - assert and cast to help type checker
        values_raw = response.get("values", [])
        assert isinstance(values_raw, list), "Protocol error: expected 'values' to be a list"
        values = self._parse_values_list(cast(list[object], values_raw))

        errors_raw = response.get("errors", [])
        assert isinstance(errors_raw, list), "Protocol error: expected 'errors' to be a list"
        errors = self._parse_errors_list(cast(list[object], errors_raw))

        absent_raw = response.get("absent", [])
        assert isinstance(absent_raw, list), "Protocol error: expected 'absent' to be a list"
        absent = self._parse_absent_list(cast(list[object], absent_raw))

        return SignalExtractionResult(
            values=values,
            errors=errors,
            absent=absent
        )

    def update(
        self,
        can_id: int,
        frame: list[int],
        signals: dict[str, float]
    ) -> list[int]:
        """
        Update specific signals in an existing frame.

        Immutable - returns new frame, original unchanged.

        Args:
            can_id: CAN message ID
            frame: Existing 8-byte frame data
            signals: Signal updates (name -> value)

        Returns:
            New 8-byte frame with updated signals

        Raises:
            ValueError: If frame is not exactly 8 bytes
            RuntimeError: If update fails (signal not found, value out of bounds)
        """
        if len(frame) != 8:
            raise ValueError(f"Frame data must be 8 bytes, got {len(frame)}")

        # Convert signals to JSON format
        signals_json: list[SignalValue] = [
            SignalValue(name=name, value=value)
            for name, value in signals.items()
        ]

        # Send updateFrame command
        update_cmd: UpdateFrameCommand = {
            "type": "command",
            "command": "updateFrame",
            "canId": can_id,
            "frame": frame,
            "signals": signals_json
        }
        response = self._send_command(update_cmd)

        # Check for error response
        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise RuntimeError(f"Update frame failed: {error_msg}")

        # Extract updated frame from response
        if "frame" not in response:
            raise RuntimeError("Invalid response: missing 'frame' field")

        frame_data = response["frame"]
        # Runtime validation of JSON data (response is from json.loads via _send_command)
        # TypedDict describes expected structure but json.loads can return anything
        if not isinstance(frame_data, list) or len(frame_data) != 8:  # pyright: ignore[reportUnnecessaryIsInstance]
            raise RuntimeError(f"Invalid frame data: expected 8-byte list, got {frame_data}")

        # Validate each byte is an integer (TypedDict doesn't guarantee runtime correctness)
        result: list[int] = []
        for b in frame_data:
            # JSON validation needed - TypedDict is static typing only
            if not isinstance(b, int):  # pyright: ignore[reportUnnecessaryIsInstance]
                raise RuntimeError(
                    f"Frame data must contain only integers, got {type(b).__name__}"
                )
            result.append(b)
        return result

    @override
    def __repr__(self) -> str:
        return "SignalExtractor(dbc=loaded)"
