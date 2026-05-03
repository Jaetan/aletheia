"""Client types, exceptions, and result containers."""

import dataclasses
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction
from types import MappingProxyType
from typing import NamedTuple, cast, override

from ..protocols import AckResponse, ErrorResponse, PropertyViolationResponse

type FrameResponse = AckResponse | PropertyViolationResponse | ErrorResponse


class AletheiaError(Exception):
    """Base exception for all Aletheia errors.

    Attributes:
        code: Machine-readable error code from the Agda core
            (``aletheia.error_codes.ErrorCode``).  ``None`` for errors raised
            purely client-side (e.g. "library not loaded", "null pointer
            from FFI") — those surface as a plain Python exception without
            an Agda wire value.
    """

    code: str | None

    def __init__(self, message: str, code: str | None = None) -> None:
        super().__init__(message)
        self.code = code


class ProcessError(AletheiaError):
    """FFI or shared library errors.

    Carries ``code`` (from :class:`AletheiaError`) so callers can
    distinguish e.g. ``extraction_bit_extraction_failed`` from
    ``frame_signal_not_found`` without parsing the message string.
    The Go binding's ``*ProcessError`` and C++'s ``ExtractionError``
    expose the same field; keep the three surfaces in sync.
    """


class ProtocolError(AletheiaError):
    """Protocol-related errors (invalid JSON, missing response, etc.).

    ``code`` is inherited from :class:`AletheiaError`; kept as its own
    subclass so ``except ProtocolError`` remains narrower than
    ``except AletheiaError`` where the distinction matters.
    """


class BatchError(AletheiaError):
    """Raised by send_frames / send_frames_iter when a frame fails or is cancelled mid-batch.

    Attributes:
        cause: The underlying exception that caused the batch to stop.
        partial_results: Frame responses the caller has not already received.
            For ``send_frames`` (batch) this is the full committed prefix.
            For ``send_frames_iter`` (sync gen / async iter) this is **empty**
            because every committed result was already yielded to the consumer
            — duplicating them here would invite double-handling.
        frame_index: Zero-based index of the frame that caused the error.
    """

    cause: Exception
    partial_results: Sequence[AckResponse | PropertyViolationResponse]
    frame_index: int

    def __init__(
        self,
        cause: Exception,
        partial_results: Sequence[AckResponse | PropertyViolationResponse],
        frame_index: int,
    ) -> None:
        super().__init__(f"frame {frame_index}: {cause}")
        self.cause = cause
        self.partial_results = partial_results
        self.frame_index = frame_index


def raise_on_error_response(
    resp: FrameResponse,
    partial: Sequence[AckResponse | PropertyViolationResponse],
    frame_index: int,
) -> AckResponse | PropertyViolationResponse:
    """Raise :class:`BatchError` if ``resp`` is an ErrorResponse; else return it narrowed.

    Shared between sync ``send_frames`` / ``send_frames_iter`` and the async
    counterparts on :class:`aletheia.asyncio.AletheiaClient`. Iter-mode
    callers pass ``partial=[]`` since their committed prefix has already
    been yielded to the consumer; batch-mode callers pass the live results
    list. See the ``BatchError`` docstring for the per-call contract.
    """
    if resp["status"] == "error":
        err = ProcessError(
            f"error code={resp['code']}: {resp['message']}",
            code=resp["code"],
        )
        raise BatchError(err, partial, frame_index=frame_index) from err
    return resp


def call_send_frame(
    send_fn: Callable[..., FrameResponse],
    frame_index: int,
    frame: "CANFrameTuple",
    partial: Sequence[AckResponse | PropertyViolationResponse],
) -> AckResponse | PropertyViolationResponse:
    """Send one frame via ``send_fn`` and return the committed response.

    ``send_fn`` is the underlying ``send_frame`` (sync) or sync-via-
    ``asyncio.to_thread`` callable. Raises :class:`BatchError` with
    ``partial`` (committed prefix for batch mode, ``[]`` for iter mode)
    on a Python exception or an ``ErrorResponse`` from the FFI; returns
    the narrowed AckResponse / PropertyViolationResponse otherwise.
    """
    try:
        resp = send_fn(frame.timestamp, frame.can_id, frame.dlc, frame.data,
                       extended=frame.extended)
    except Exception as exc:
        raise BatchError(exc, partial, frame_index=frame_index) from exc
    return raise_on_error_response(resp, partial, frame_index)


def validate_payload_length(dlc: int, data: bytes | bytearray) -> int:
    """Return ``dlc_to_bytes(dlc)``; raise :class:`ProcessError` on mismatch.

    Shared between ``send_frame`` / ``extract_signals`` / ``update_frame``
    so the validation + error message stay in lock-step at every payload
    boundary.
    """
    expected_bytes = dlc_to_bytes(dlc)
    if len(data) != expected_bytes:
        raise ProcessError(
            f"payload length {len(data)} does not match DLC {dlc}"
            + f" (expected {expected_bytes} bytes)"
        )
    return expected_bytes


@dataclass(slots=True, frozen=True)
class FrameResult:
    """Per-frame outcome yielded by ``send_frames_iter``.

    Carries the index, timestamp, and CAN-ID identity of the source frame
    plus its outcome — not the full payload, since the consumer already
    holds the input ``CANFrameTuple`` if it needs the bytes back. Mirrors
    the partial-results semantics of ``BatchError`` and the per-frame
    response carried in C++ ``BatchResult.responses[i]`` / Go's
    ``[]FrameResponse``.

    The ``violation`` property returns the response only when it is a
    ``fails`` verdict, supporting the canonical iter pattern from
    docs/architecture/CANCELLATION.md §4.1::

        async for result in client.send_frames_iter(frames):
            if result.violation is not None:
                handle(result.violation)
    """
    frame_index: int
    timestamp: int
    can_id: int
    extended: bool
    response: AckResponse | PropertyViolationResponse

    @property
    def violation(self) -> PropertyViolationResponse | None:
        """The PropertyViolationResponse if this frame violated a property, else None."""
        if self.response.get("status") == "fails":
            return cast(PropertyViolationResponse, self.response)
        return None


class SignalExtractionResult:
    """Rich result object for signal extraction.

    Partitions extraction results into three categories:
    - values: Successfully extracted signal values (Fraction preserves exact
      rational precision from the Agda core)
    - errors: Extraction errors with reasons
    - absent: Multiplexed signals not present in this frame
    """

    values: Mapping[str, Fraction]
    errors: Mapping[str, str]
    absent: tuple[str, ...]

    def __init__(
        self,
        values: dict[str, Fraction],
        errors: dict[str, str],
        absent: tuple[str, ...],
    ) -> None:
        self.values = MappingProxyType(values)
        self.errors = MappingProxyType(errors)
        self.absent = absent

    def get(self, signal_name: str, default: Fraction = Fraction(0)) -> Fraction:
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


# (can_id, extended, raw_bytes) uniquely identifies a CAN frame for extraction caching.
type FrameKey = tuple[int, bool, bytes]
type ExtractionCache = dict[FrameKey, SignalExtractionResult]

# (can_id, extended) → (can_id, dlc, data) for EOS signal extraction.
type LastFrameKey = tuple[int, bool]
type LastFrameData = tuple[int, bytearray]

MAX_EXTRACT_CACHE: int = 256


@dataclass(slots=True)
class StreamCaches:
    """Per-stream mutable caches, cleared together on start_stream/parse_dbc."""
    extraction: ExtractionCache = dataclasses.field(default_factory=dict)
    last_frames: dict[LastFrameKey, LastFrameData] = dataclasses.field(default_factory=dict)

    def clear(self) -> None:
        """Reset all caches for a new stream."""
        self.extraction.clear()
        self.last_frames.clear()


class CANFrameTuple(NamedTuple):
    """CAN frame tuple matching ``send_frame()`` positional args.

    Fields:
        timestamp: Timestamp in microseconds.
        can_id: CAN arbitration ID (11-bit standard or 29-bit extended).
        dlc: DLC code (0-8 for CAN 2.0B, 0-15 for CAN-FD).
        data: Frame payload (length must equal ``dlc_to_bytes(dlc)``).
        extended: ``True`` for 29-bit extended CAN ID.
    """
    timestamp: int
    can_id: int
    dlc: int
    # Either ``bytes`` (immutable read-only payload) or ``bytearray`` (mutable
    # buffer filled from a SocketCAN read).  Both work at the ctypes boundary;
    # ``bytes`` is preferred for precomputed frame constants in benchmarks and
    # tests so the module-level data cannot be mutated between iterations.
    data: bytes | bytearray
    extended: bool

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


@dataclass(slots=True, frozen=True)
class PropertyDiagnostic:
    """Per-property diagnostic metadata for violation enrichment."""
    signals: tuple[str, ...]
    formula_desc: str


@dataclass(slots=True, frozen=True)
class SignalLookup:
    """Per-message signal name/index cache populated after ``parse_dbc``.

    ``indices`` maps signal name to its position within the DBC message's
    signal list; ``names`` is the parallel array used to resolve indices
    back to names when decoding the binary extraction response.
    """
    names: tuple[str, ...]
    indices: dict[str, int]
