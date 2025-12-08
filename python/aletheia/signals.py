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

import subprocess
import json
from pathlib import Path
from typing import Dict, List, Optional, Any, cast
from .protocols import DBCDefinition


def _get_binary_path() -> Path:
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
            "Please build it first with: cabal run shake -- build"
        )

    return binary


class SignalExtractionResult:
    """
    Rich result object for signal extraction.

    Partitions extraction results into three categories:
    - values: Successfully extracted signal values
    - errors: Extraction errors with reasons
    - absent: Multiplexed signals not present in this frame
    """

    def __init__(
        self,
        values: Dict[str, float],
        errors: Dict[str, str],
        absent: List[str]
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


class FrameBuilder:
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
        self._can_id = can_id
        self._dbc = dbc
        self._signals: Dict[str, float] = {}
        self._proc: Optional[subprocess.Popen[str]] = None

        # Start subprocess and load DBC
        binary_path = _get_binary_path()
        self._proc = subprocess.Popen(
            [str(binary_path)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1
        )

        # Load DBC
        self._send_command({
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        })

    def __enter__(self):
        """Context manager entry"""
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        """Context manager exit - cleanup subprocess"""
        self.close()

    def close(self) -> None:
        """Close subprocess and cleanup resources"""
        if self._proc:
            self._proc.terminate()
            try:
                self._proc.wait(timeout=5.0)
            except subprocess.TimeoutExpired:
                self._proc.kill()
                self._proc.wait()
            self._proc = None

    def _send_command(self, command: Dict[str, Any]) -> Dict[str, Any]:
        """Send command to subprocess and get response

        Args:
            command: Command dictionary

        Returns:
            Response dictionary

        Raises:
            RuntimeError: If subprocess not running or command fails
        """
        if not self._proc or not self._proc.stdin or not self._proc.stdout:
            raise RuntimeError("Subprocess not running")

        # Send command
        json_line = json.dumps(command)
        self._proc.stdin.write(json_line + "\n")
        self._proc.stdin.flush()

        # Read response
        response_line = self._proc.stdout.readline()
        if not response_line:
            if self._proc.poll() is not None:
                stderr = self._proc.stderr.read() if self._proc.stderr else ""
                raise RuntimeError(f"Binary process terminated: {stderr}")
            raise RuntimeError("No response from binary")

        response = json.loads(response_line)

        # Check for errors
        if response.get("status") == "error":
            raise RuntimeError(f"Command failed: {response.get('message', 'Unknown error')}")

        return response

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
        new_builder._can_id = self._can_id
        new_builder._dbc = self._dbc
        new_builder._proc = self._proc  # Share subprocess
        new_builder._signals = self._signals.copy()
        new_builder._signals[signal_name] = value
        return new_builder

    def build(self) -> List[int]:
        """
        Build CAN frame from configured signals.

        Returns:
            8-byte CAN frame as list of integers (0-255)

        Raises:
            RuntimeError: If frame building fails (signal overlap,
                         signal not found, value out of bounds, etc.)
        """
        # Convert signals to JSON format expected by Agda
        signals_json = [
            {"name": name, "value": value}
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

        frame = response["frame"]
        if not isinstance(frame, list) or len(frame) != 8:
            raise RuntimeError(f"Invalid frame data: expected 8-byte list, got {frame}")

        return frame

    def __repr__(self) -> str:
        return (
            f"FrameBuilder("
            f"can_id=0x{self._can_id:X}, "
            f"signals={list(self._signals.keys())})"
        )


class SignalExtractor:
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
        self._dbc = dbc
        self._proc: Optional[subprocess.Popen[str]] = None

        # Start subprocess and load DBC
        binary_path = _get_binary_path()
        self._proc = subprocess.Popen(
            [str(binary_path)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1
        )

        # Load DBC
        self._send_command({
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        })

    def __enter__(self):
        """Context manager entry"""
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        """Context manager exit - cleanup subprocess"""
        self.close()

    def close(self) -> None:
        """Close subprocess and cleanup resources"""
        if self._proc:
            self._proc.terminate()
            try:
                self._proc.wait(timeout=5.0)
            except subprocess.TimeoutExpired:
                self._proc.kill()
                self._proc.wait()
            self._proc = None

    def _send_command(self, command: Dict[str, Any]) -> Dict[str, Any]:
        """Send command to subprocess and get response

        Args:
            command: Command dictionary

        Returns:
            Response dictionary

        Raises:
            RuntimeError: If subprocess not running or command fails
        """
        if not self._proc or not self._proc.stdin or not self._proc.stdout:
            raise RuntimeError("Subprocess not running")

        # Send command
        json_line = json.dumps(command)
        self._proc.stdin.write(json_line + "\n")
        self._proc.stdin.flush()

        # Read response
        response_line = self._proc.stdout.readline()
        if not response_line:
            if self._proc.poll() is not None:
                stderr = self._proc.stderr.read() if self._proc.stderr else ""
                raise RuntimeError(f"Binary process terminated: {stderr}")
            raise RuntimeError("No response from binary")

        response = json.loads(response_line)

        # Check for errors
        if response.get("status") == "error":
            raise RuntimeError(f"Command failed: {response.get('message', 'Unknown error')}")

        return response

    def extract(
        self,
        can_id: int,
        data: List[int]
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
        values_list = response.get("values", [])
        errors_list = response.get("errors", [])
        absent_list = response.get("absent", [])

        # Convert values list to dict
        values = {item["name"]: item["value"] for item in values_list}

        # Convert errors list to dict
        errors = {item["name"]: item["error"] for item in errors_list}

        return SignalExtractionResult(
            values=values,
            errors=errors,
            absent=absent_list
        )

    def update(
        self,
        can_id: int,
        frame: List[int],
        signals: Dict[str, float]
    ) -> List[int]:
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
        signals_json = [
            {"name": name, "value": value}
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

        updated_frame = response["frame"]
        if not isinstance(updated_frame, list) or len(updated_frame) != 8:
            raise RuntimeError(f"Invalid frame data: expected 8-byte list, got {updated_frame}")

        return updated_frame

    def __repr__(self) -> str:
        return f"SignalExtractor(dbc=loaded)"
