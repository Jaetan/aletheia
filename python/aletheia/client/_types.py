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


@dataclass(slots=True)
class PropertyDiagnostic:
    """Per-property diagnostic metadata for violation enrichment."""
    signals: list[str]
    formula_desc: str
