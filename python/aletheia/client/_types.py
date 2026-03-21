"""Client types, exceptions, and result containers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import override


class AletheiaError(Exception):
    """Base exception for all Aletheia errors"""


class ProcessError(AletheiaError):
    """FFI or shared library errors"""


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


@dataclass(slots=True)
class CheckDiag:
    """Per-check diagnostic metadata for violation enrichment."""
    signal_name: str
    condition_desc: str
