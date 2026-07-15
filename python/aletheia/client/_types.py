# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Client types, exceptions, and result containers."""

# DEFERRED:
# Finding: This file (432 LOC, shrunk organically from a higher mark)
#   mixes the public exception hierarchy (already re-exported at the top-level
#   `aletheia` package) with client-internal scaffolding.  If it regrows, the
#   natural split is to move the internal scaffolding to a
#   `python/aletheia/client/_internals.py`; the exception hierarchy stays
#   re-exported from the top-level `aletheia` package — the sole public path
#   (`aletheia.client` is internal, and `aletheia.types` is now the wire-types
#   namespace, so neither is available as a split target).
# Why: Organic shrinkage keeps urgency low; the AletheiaError canonical-path
#   question is already resolved (top-level `aletheia` is the single public path).
# Revisit when: This file re-grows past ~600 LOC.

import dataclasses
from dataclasses import dataclass
from fractions import Fraction
from types import MappingProxyType
from typing import TYPE_CHECKING, NamedTuple, cast, override

from aletheia.limits import BOUND_KIND_INPUT_LENGTH_BYTES, MAX_DBC_TEXT_BYTES
from aletheia.types import (
    AckResponse,
    DLCByteCount,
    DLCCode,
    ErrorResponse,
    PropertyBatchResponse,
    PropertyResultEntry,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence

    from aletheia.codes import ValidationIssue

type FrameResponse = AckResponse | PropertyBatchResponse | ErrorResponse


class AletheiaError(Exception):
    """Base exception for all Aletheia errors.

    Attributes:
        code: Machine-readable error code from the Agda core
            (``aletheia.ErrorCode``).  ``None`` for errors raised
            purely client-side (e.g. "library not loaded", "null pointer
            from FFI") — those surface as a plain Python exception without
            an Agda wire value.

    """

    code: str | None

    def __init__(self, message: str, code: str | None = None) -> None:
        super().__init__(message)
        self.code = code


class FFIError(AletheiaError):
    """Library-load / RTS-init / FFI-null-pointer failures.

    Mirrors Go ``ErrFFI`` and C++ ``ErrorKind::Ffi`` — the kind for
    `dlopen` / `dlsym` / `hs_init` / `aletheia_init() → null` failures
    where the boundary itself failed before any Agda code ran.
    """


class StateError(AletheiaError):
    """Operation attempted in the wrong client lifecycle state.

    Mirrors Go ``ErrState`` and C++ ``ErrorKind::State`` — covers
    "client not initialized (use ``with``)", "DBC not loaded",
    "stream already / not started", and the equivalent Agda-side
    handler-state rejections (``handler_no_dbc`` / ``handler_not_streaming`` /
    ``handler_stream_active`` etc.).
    """


class ProtocolError(AletheiaError):
    """Wire-protocol failures.

    Mirrors Go ``ErrProtocol`` and C++ ``ErrorKind::Protocol`` — covers
    invalid JSON, missing response fields, FFI-returned-null where a
    response was expected, AND the Agda kernel returning an
    ``ErrorResponse`` with a wire ``code`` (e.g. ``frame_signal_not_found``,
    ``extraction_bit_extraction_failed``).  Callers can branch on
    :attr:`AletheiaError.code` to discriminate kernel error codes
    without parsing the message string.
    """


class ValidationError(AletheiaError):
    """Caller-supplied argument failed a Python-side validity check.

    Examples: negative timestamp, malformed CAN ID, unknown signal name,
    payload length mismatch.

    Mirrors Go ``ErrValidation`` and C++ ``ErrorKind::Validation`` —
    cross-binding parity for argument-rejection paths.  Replaces ad-hoc
    ``ValueError`` raises that escaped the typed ``AletheiaError``
    hierarchy.
    """


class InputBoundExceededError(AletheiaError):
    """Raised when an input exceeds an adversarial-input bound.

    Mirrors the Agda ``InputBoundExceeded`` constructor on
    ``ParseError`` / ``DBCTextParseError`` / ``FrameError``.  Attributes
    carry the bound kind (e.g. ``"input_length_bytes"``), the observed
    value, and the canonical limit per :mod:`aletheia.limits`.

    The Go and C++ bindings expose the equivalent type
    (``*aletheia.InputBoundExceededError`` / ``aletheia::InputBoundExceededError``);
    keep the three surfaces in sync.
    """

    kind: str
    observed: int
    limit: int

    def __init__(self, kind: str, observed: int, limit: int, code: str | None = None) -> None:
        message = f"{kind} {observed} exceeds limit {limit}"
        super().__init__(message, code=code)
        self.kind = kind
        self.observed = observed
        self.limit = limit


def check_dbc_text_size_bound(observed: int) -> None:
    """Raise :class:`InputBoundExceededError` if observed > MAX_DBC_TEXT_BYTES.

    Defense-in-depth size cap shared by every parser surface that reads DBC
    text, YAML check definitions, or Excel workbooks.  Re-exported from
    :mod:`aletheia.limits` — non-client modules should import via the
    public path; this canonical definition stays here so
    InputBoundExceededError lives next to its raiser.
    """
    if observed > MAX_DBC_TEXT_BYTES:
        raise InputBoundExceededError(
            BOUND_KIND_INPUT_LENGTH_BYTES,
            observed,
            MAX_DBC_TEXT_BYTES,
        )


class DBCValidationFailedError(AletheiaError):
    """Raised when the Agda core rejects a DBC that parsed but failed validation.

    Mirrors the ``handler_validation_failed`` error envelope emitted by
    ``parseDBC`` / ``parseDBCText``: ``issues`` carries the full issue
    list (the exact element shape of the ``validation`` response —
    severity / code / detail) and ``has_errors`` echoes the decoded wire
    flag rather than being recomputed.  Envelopes whose ``issues`` /
    ``has_errors`` payload is absent or ill-typed degrade to the
    pre-existing generic errors instead of this type.

    The Go, C++, and Rust bindings expose the equivalent typed error;
    keep the surfaces in sync.
    """

    issues: list[ValidationIssue]
    has_errors: bool

    def __init__(
        self,
        message: str,
        issues: list[ValidationIssue],
        *,
        has_errors: bool,
        code: str | None = None,
    ) -> None:
        super().__init__(message, code=code)
        self.issues = issues
        self.has_errors = has_errors


class TextRoundTripFailedError(AletheiaError):
    """Raised when ``format_dbc_text`` refuses because its emitted text does not round-trip.

    ``format_dbc_text`` is always strict: it returns a ``DBCTextResponse`` ONLY
    when re-parsing the emitted text reproduces the input DBC.  When the exact
    round-trip check fails, the kernel emits the ``handler_text_roundtrip_failed``
    envelope instead; this typed error carries the full ``issues`` list (led by
    the error-severity ``text_roundtrip_divergence`` issue the handler prepends)
    and ``has_errors`` echoes the decoded wire flag rather than being recomputed.
    Distinct from :class:`DBCValidationFailedError` (a validation failure, not a
    round-trip failure) though the wire shape is identical.  Envelopes whose
    ``issues`` / ``has_errors`` payload is absent or ill-typed degrade to the
    pre-existing generic errors instead of this type.

    The Go, C++, and Rust bindings expose the equivalent typed error; keep the
    surfaces in sync.
    """

    issues: list[ValidationIssue]
    has_errors: bool

    def __init__(
        self,
        message: str,
        issues: list[ValidationIssue],
        *,
        has_errors: bool,
        code: str | None = None,
    ) -> None:
        super().__init__(message, code=code)
        self.issues = issues
        self.has_errors = has_errors


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
    partial_results: Sequence[AckResponse | PropertyBatchResponse]
    frame_index: int

    def __init__(
        self,
        cause: Exception,
        partial_results: Sequence[AckResponse | PropertyBatchResponse],
        frame_index: int,
    ) -> None:
        super().__init__(f"frame {frame_index}: {cause}")
        self.cause = cause
        self.partial_results = partial_results
        self.frame_index = frame_index


def raise_on_error_response(
    resp: FrameResponse,
    partial: Sequence[AckResponse | PropertyBatchResponse],
    frame_index: int,
) -> AckResponse | PropertyBatchResponse:
    """Raise :class:`BatchError` if ``resp`` is an ErrorResponse; else return it narrowed.

    Shared between sync ``send_frames`` / ``send_frames_iter`` and the async
    counterparts on :class:`aletheia.asyncio.AletheiaClient`. Iter-mode
    callers pass ``partial=[]`` since their committed prefix has already
    been yielded to the consumer; batch-mode callers pass the live results
    list. See the ``BatchError`` docstring for the per-call contract.
    """
    # PropertyBatchResponse has no top-level "status" field (it
    # discriminates on `type == "property_batch"`), so use ``.get()``
    # to avoid KeyError on non-error batches.
    if resp.get("status") == "error":
        err_resp = cast("ErrorResponse", resp)
        err = ProtocolError(
            f"error code={err_resp['code']}: {err_resp['message']}",
            code=err_resp["code"],
        )
        raise BatchError(err, partial, frame_index=frame_index) from err
    return cast("AckResponse | PropertyBatchResponse", resp)


def call_send_frame(
    send_fn: Callable[..., FrameResponse],
    frame_index: int,
    frame: CANFrameTuple,
    partial: Sequence[AckResponse | PropertyBatchResponse],
) -> AckResponse | PropertyBatchResponse:
    """Send one frame via ``send_fn`` and return the committed response.

    ``send_fn`` is the underlying ``send_frame`` (sync) or sync-via-
    ``asyncio.to_thread`` callable. Raises :class:`BatchError` with
    ``partial`` (committed prefix for batch mode, ``[]`` for iter mode)
    on a Python exception or an ``ErrorResponse`` from the FFI; returns
    the narrowed AckResponse / PropertyBatchResponse otherwise.
    """
    try:
        resp = send_fn(
            frame.timestamp,
            frame.can_id,
            frame.dlc,
            frame.data,
            extended=frame.extended,
            brs=frame.brs,
            esi=frame.esi,
        )
    except Exception as exc:
        raise BatchError(exc, partial, frame_index=frame_index) from exc
    return raise_on_error_response(resp, partial, frame_index)


def validate_payload_length(dlc: DLCCode, data: bytes | bytearray) -> DLCByteCount:
    """Return ``dlc_to_bytes(dlc)``; raise :class:`ValidationError` on mismatch.

    Shared between ``send_frame`` / ``extract_signals`` / ``update_frame``
    so the validation + error message stay in lock-step at every payload
    boundary.
    """
    expected_bytes = dlc_to_bytes(dlc)
    if len(data) != expected_bytes:
        raise ValidationError(
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
    response: AckResponse | PropertyBatchResponse

    @property
    def violation(self) -> PropertyResultEntry | None:
        """The first violating event from the batch, else None.

        A frame's response may carry multiple property events (any
        mid-stream satisfactions that completed before a halting
        violation, in source-order, followed by the violation).  Per
        the Agda invariant in dispatchIterResult, violations always
        close a batch — there is at most one violation per frame, and
        if present it is the last result.
        """
        if self.response.get("type") != "property_batch":
            return None
        results = cast("PropertyBatchResponse", self.response).get("results", [])
        for entry in results:
            if entry.get("status") == "fails":
                return entry
        return None

    @property
    def satisfactions(self) -> list[PropertyResultEntry]:
        """Mid-stream satisfaction events from the batch.

        Properties that completed (became Satisfied) on this frame are
        surfaced here in source-order.  Empty list for ack-only frames
        and for violation-only frames.
        """
        if self.response.get("type") != "property_batch":
            return []
        return [
            entry
            for entry in cast("PropertyBatchResponse", self.response).get("results", [])
            if entry.get("status") == "holds"
        ]


def make_frame_result(
    frame_index: int,
    frame: CANFrameTuple,
    response: AckResponse | PropertyBatchResponse,
) -> FrameResult:
    """Build a :class:`FrameResult` from a source frame's identity + response.

    Shared by the sync (``send_frames_iter``) and async per-frame generators,
    which otherwise restate the same five-field construction on every yield.
    """
    return FrameResult(
        frame_index=frame_index,
        timestamp=frame.timestamp,
        can_id=frame.can_id,
        extended=frame.extended,
        response=response,
    )


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
type LastFrameData = tuple[DLCCode, bytearray]

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
        brs: Bit Rate Switch (ISO 11898-1:2015 §10.4.2) — ``True`` if the
            CAN-FD data phase ran at the faster bit rate, ``False`` if it
            stayed at the arbitration bit rate, ``None`` for CAN 2.0B
            frames where the bit does not exist.
        esi: Error State Indicator (ISO 11898-1:2015 §10.4.3) — ``True``
            if the transmitter is in error-passive state, ``False`` if
            error-active, ``None`` for CAN 2.0B frames.
    """

    timestamp: int
    can_id: int
    dlc: DLCCode
    # Either ``bytes`` (immutable read-only payload) or ``bytearray`` (mutable
    # buffer filled from a SocketCAN read).  Both work at the ctypes boundary;
    # ``bytes`` is preferred for precomputed frame constants in benchmarks and
    # tests so the module-level data cannot be mutated between iterations.
    data: bytes | bytearray
    extended: bool
    brs: bool | None = None
    esi: bool | None = None


_MAX_STANDARD_ID = (1 << 11) - 1  # 11-bit CAN ID
_MAX_EXTENDED_ID = (1 << 29) - 1  # 29-bit CAN ID


def validate_can_id(can_id: int, *, extended: bool) -> None:
    """Validate that a CAN ID is within the legal range.

    Raises:
        ValidationError: If can_id is outside the valid range.

    """
    max_id = _MAX_EXTENDED_ID if extended else _MAX_STANDARD_ID
    kind = "extended" if extended else "standard"
    if can_id < 0 or can_id > max_id:
        msg = f"Invalid {kind} CAN ID: {can_id} (must be 0-{max_id})"
        raise ValidationError(msg)


_DLC_TO_BYTES: dict[int, int] = {
    0: 0,
    1: 1,
    2: 2,
    3: 3,
    4: 4,
    5: 5,
    6: 6,
    7: 7,
    8: 8,
    9: 12,
    10: 16,
    11: 20,
    12: 24,
    13: 32,
    14: 48,
    15: 64,
}


def dlc_to_bytes(dlc: DLCCode) -> DLCByteCount:
    """Convert a DLC code (0-15) to payload byte count.

    CAN 2.0B: DLC 0-8 maps directly.
    CAN-FD: DLC 9-15 maps to 12, 16, 20, 24, 32, 48, 64.

    Raises:
        ValidationError: If dlc is outside 0-15.

    """
    try:
        return DLCByteCount(_DLC_TO_BYTES[dlc])
    except KeyError:
        msg = f"Invalid DLC code: {dlc} (must be 0-15)"
        raise ValidationError(msg) from None


_BYTES_TO_DLC: dict[int, int] = {v: k for k, v in _DLC_TO_BYTES.items()}


def encode_maybe_bool(*, b: bool | None) -> tuple[int, int]:
    """Encode an Optional[bool] as the (present, value) byte pair.

    Used by the binary FFI for CAN-FD BRS / ESI metadata.

    ``None`` → ``(0, 0)`` (the bit is absent on the wire);
    ``False`` → ``(1, 0)``; ``True`` → ``(1, 1)``.

    Inverse of the Haskell shim's ``mkMaybeBool`` (see
    ``haskell-shim/src/AletheiaFFI/Marshal.hs``).
    """
    if b is None:
        return (0, 0)
    return (1, 1 if b else 0)


def bytes_to_dlc(byte_count: DLCByteCount) -> DLCCode:
    """Convert a payload byte count to a DLC code (0-15).

    CAN 2.0B: byte counts 0-8 map directly.
    CAN-FD: byte counts 12, 16, 20, 24, 32, 48, 64 map to DLC 9-15.

    Raises:
        ValidationError: If byte_count is not one of the valid lengths above.

    """
    try:
        return DLCCode(_BYTES_TO_DLC[byte_count])
    except KeyError:
        raise ValidationError(
            f"Invalid byte count: {byte_count}" + " (must be 0-8, 12, 16, 20, 24, 32, 48, or 64)"
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
