"""Base class for Aletheia binary client interactions

This module provides a common base class for all clients that interact with
the Aletheia binary via subprocess (StreamingClient, FrameBuilder, SignalExtractor).

Centralizes:
- Subprocess lifecycle management
- JSON command/response protocol
- Context manager support
- Graceful shutdown logic
"""

import json
import subprocess
from pathlib import Path
from typing import Any

from .binary_utils import get_binary_path


# JSON type definition (recursive composite type)
# JSON values can be: None, bool, int, float, str, list of JSON, or dict of str to JSON
JSON = None | bool | int | float | str | list["JSON"] | dict[str, "JSON"]
JSONObject = dict[str, JSON]


class BinaryClient:
    """Base class for clients that interact with Aletheia binary

    Provides:
    - Subprocess lifecycle management (start, stop, cleanup)
    - JSON command/response protocol
    - Context manager support
    - Graceful shutdown with timeout

    Subclasses should:
    - Call super().__init__() in their __init__
    - Call _start_subprocess() when ready to launch binary
    - Implement custom business logic using _send_command()
    """

    def __init__(self, shutdown_timeout: float = 5.0):
        """Initialize binary client (does not start subprocess yet)

        Args:
            shutdown_timeout: Timeout in seconds for graceful shutdown (default: 5.0)
        """
        self.binary_path: Path = get_binary_path()
        self._proc: subprocess.Popen[str] | None = None
        self.shutdown_timeout: float = shutdown_timeout

    def _start_subprocess(self) -> None:
        """Start the binary subprocess

        Raises:
            RuntimeError: If subprocess already running
        """
        if self._proc is not None:
            raise RuntimeError("Subprocess already running")

        self._proc = subprocess.Popen(
            [str(self.binary_path)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1  # Line buffered
        )

    def __enter__(self):
        """Context manager entry"""
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: object
    ) -> None:
        """Context manager exit - cleanup subprocess"""
        self.close()

    def close(self) -> None:
        """Close subprocess and cleanup resources

        Tries graceful termination first, then force kill if needed.
        """
        if self._proc:
            self._proc.terminate()
            try:
                self._proc.wait(timeout=self.shutdown_timeout)
            except subprocess.TimeoutExpired:
                # Graceful termination failed, force kill
                self._proc.kill()
                self._proc.wait()  # Wait for kill to complete
            self._proc = None

    def _send_command(self, command: JSONObject) -> JSONObject:
        """Send JSON command to binary and receive response

        Args:
            command: Command dictionary (must have JSON-serializable structure)

        Returns:
            Response dictionary from binary

        Raises:
            RuntimeError: If subprocess not running or command fails
        """
        if not self._proc or not self._proc.stdin or not self._proc.stdout:
            raise RuntimeError("Subprocess not running")

        # Send command as JSON line
        json_line = json.dumps(command)
        self._proc.stdin.write(json_line + "\n")
        self._proc.stdin.flush()

        # Read response line
        response_line = self._proc.stdout.readline()
        if not response_line:
            # Check if process terminated
            if self._proc.poll() is not None:
                stderr = self._proc.stderr.read() if self._proc.stderr else ""
                raise RuntimeError(f"Binary process terminated: {stderr}")
            raise RuntimeError("No response from binary")

        # Parse JSON response
        response_data: JSON = json.loads(response_line)
        response: JSONObject = response_data if isinstance(response_data, dict) else {}

        # Check for error status
        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise RuntimeError(f"Command failed: {error_msg}")

        return response
