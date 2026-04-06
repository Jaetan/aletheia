"""Client types, exceptions, and result containers."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import override

from ..protocols import AckResponse, ErrorResponse, PropertyViolationResponse

type FrameResponse = AckResponse | PropertyViolationResponse | ErrorResponse


class AletheiaError(Exception):
    """Base exception for all Aletheia errors"""


class ProcessError(AletheiaError):
    """FFI or shared library errors"""


class ProtocolError(AletheiaError):
    """Protocol-related errors (invalid JSON, missing response, etc.)

    Attributes:
        code: Machine-readable error code from Agda (None for client-side errors).
    """
    code: str | None

    def __init__(self, message: str, code: str | None = None) -> None:
        super().__init__(message)
        self.code = code


class BatchError(AletheiaError):
    """Raised by send_frames_batch when a frame fails mid-batch.

    Attributes:
        cause: The underlying exception that caused the batch to stop.
        partial_results: Responses from frames processed before the error.
    """

    cause: Exception
    partial_results: Sequence[FrameResponse]

    def __init__(self, cause: Exception, partial_results: Sequence[FrameResponse]) -> None:
        super().__init__(str(cause))
        self.cause = cause
        self.partial_results = partial_results


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
        return bool(self.errors)

    @override
    def __repr__(self) -> str:
        return (
            "SignalExtractionResult("
            f"values={len(self.values)}, "
            f"errors={len(self.errors)}, "
            f"absent={len(self.absent)})"
        )


# (can_id, raw_bytes) uniquely identifies a CAN frame for extraction caching.
type FrameKey = tuple[int, bytes]
type ExtractionCache = dict[FrameKey, SignalExtractionResult]

MAX_EXTRACT_CACHE: int = 256


_MAX_STANDARD_ID = (1 << 11) - 1  # 11-bit CAN ID
_MAX_EXTENDED_ID = (1 << 29) - 1  # 29-bit CAN ID


def validate_can_id(can_id: int, *, extended: bool) -> None:
    """Validate that a CAN ID is within the legal range.

    Raises:
        ValueError: If can_id is outside the valid range.
    """
    max_id = _MAX_EXTENDED_ID if extended else _MAX_STANDARD_ID
    kind = "extended" if extended else "standard"
    if can_id < 0 or can_id > max_id:
        raise ValueError(
            f"Invalid {kind} CAN ID: {can_id} (must be 0-{max_id})"
        )


_DLC_TO_BYTES: dict[int, int] = {
    0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8,
    9: 12, 10: 16, 11: 20, 12: 24, 13: 32, 14: 48, 15: 64,
}


def dlc_to_bytes(dlc: int) -> int:
    """Convert a DLC code (0-15) to payload byte count.

    CAN 2.0B: DLC 0-8 maps directly.
    CAN-FD: DLC 9-15 maps to 12, 16, 20, 24, 32, 48, 64.
    """
    try:
        return _DLC_TO_BYTES[dlc]
    except KeyError:
        raise ValueError(f"Invalid DLC code: {dlc} (must be 0-15)") from None


_BYTES_TO_DLC: dict[int, int] = {v: k for k, v in _DLC_TO_BYTES.items()}


def bytes_to_dlc(byte_count: int) -> int:
    """Convert a payload byte count to a DLC code (0-15).

    CAN 2.0B: byte counts 0-8 map directly.
    CAN-FD: byte counts 12, 16, 20, 24, 32, 48, 64 map to DLC 9-15.
    """
    try:
        return _BYTES_TO_DLC[byte_count]
    except KeyError:
        raise ValueError(
            f"Invalid byte count: {byte_count}"
            + " (must be 0-8, 12, 16, 20, 24, 32, 48, or 64)"
        ) from None


@dataclass(slots=True)
class PropertyDiagnostic:
    """Per-property diagnostic metadata for violation enrichment."""
    signals: list[str]
    formula_desc: str
