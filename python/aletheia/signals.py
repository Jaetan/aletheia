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

from typing import Protocol, TypedDict

from .binary_client import BinaryClient
from .protocols import DBCDefinition


class SignalValue(TypedDict):
    """Signal name-value pair for encoding"""
    name: str
    value: float


class SignalError(TypedDict):
    """Signal name-error pair for extraction errors"""
    name: str
    error: str


class FrameResponse(Protocol):
    """Protocol for responses containing a frame field"""
    def get(self, key: str, default: object = None) -> object: ...
    def __getitem__(self, key: str) -> object: ...
    def __contains__(self, key: str) -> bool: ...


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
        _ = self._send_command({
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        })

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
        new_builder = object.__new__(FrameBuilder)
        # Copy base class attributes
        new_builder.binary_path = self.binary_path
        new_builder._proc = self._proc  # Share subprocess
        new_builder.shutdown_timeout = self.shutdown_timeout
        # Copy FrameBuilder-specific attributes
        new_builder._can_id = self._can_id
        new_builder._dbc = self._dbc
        new_builder._signals = self._signals.copy()
        new_builder._signals[signal_name] = value
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
        response = self._send_command({
            "type": "command",
            "command": "buildFrame",
            "canId": self._can_id,
            "signals": signals_json
        })

        # Extract frame bytes from response
        if "frame" not in response:
            raise RuntimeError("Invalid response: missing 'frame' field")

        frame_data = response["frame"]
        if not isinstance(frame_data, list) or len(frame_data) != 8:
            raise RuntimeError(f"Invalid frame data: expected 8-byte list, got {frame_data}")

        return frame_data  # type: ignore[return-value]

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
        _ = self._send_command({
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        })

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
        response = self._send_command({
            "type": "command",
            "command": "extractAllSignals",
            "canId": can_id,
            "data": data
        })

        # Parse response into SignalExtractionResult
        values_data = response.get("values", [])
        errors_data = response.get("errors", [])
        absent_data = response.get("absent", [])

        # Convert values list to dict
        values: dict[str, float] = {}
        if isinstance(values_data, list):
            for item in values_data:
                if isinstance(item, dict) and "name" in item and "value" in item:
                    values[str(item["name"])] = float(item["value"])  # type: ignore[arg-type]

        # Convert errors list to dict
        errors: dict[str, str] = {}
        if isinstance(errors_data, list):
            for item in errors_data:
                if isinstance(item, dict) and "name" in item and "error" in item:
                    errors[str(item["name"])] = str(item["error"])

        # Convert absent list
        absent: list[str] = []
        if isinstance(absent_data, list):
            absent = [str(item) for item in absent_data]

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
        response = self._send_command({
            "type": "command",
            "command": "updateFrame",
            "canId": can_id,
            "frame": frame,
            "signals": signals_json
        })

        # Extract updated frame from response
        if "frame" not in response:
            raise RuntimeError("Invalid response: missing 'frame' field")

        frame_data = response["frame"]
        if not isinstance(frame_data, list) or len(frame_data) != 8:
            raise RuntimeError(f"Invalid frame data: expected 8-byte list, got {frame_data}")

        return frame_data  # type: ignore[return-value]

    def __repr__(self) -> str:
        return f"SignalExtractor(dbc=loaded)"
