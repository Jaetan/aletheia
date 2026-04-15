"""Binary FFI helpers for signal extraction, frame update, and frame build.

Wraps the three C entry points (``aletheia_extract_signals_bin``,
``aletheia_update_frame_bin``, ``aletheia_build_frame_bin``) behind a
small class that owns references to the loaded library and the opaque
state pointer.  Separating these out of ``_client.py`` keeps the main
client module focused on high-level protocol flow and lets the
binary-path helpers stay under pylint's complexity thresholds.
"""

import ctypes
import struct
from collections.abc import Sequence
from dataclasses import dataclass
from enum import IntEnum
from fractions import Fraction
from typing import NoReturn

from ._types import ProcessError, SignalExtractionResult


class ExtractionErrorCode(IntEnum):
    """Binary-FFI extraction error codes shared with the Agda core.

    Values are a permanent part of the wire format — each constructor of
    ``Aletheia.CAN.BatchExtraction.ExtractionErrorCode`` serializes to a
    single ``u8`` in the ``<HB`` errors segment of the binary response,
    and ``extractionErrorCodeToℕ`` pins them to the integers below.

    Changing a value or removing a member is a breaking change; any new
    Agda constructor must be mirrored here (and in the Go/C++ bindings)
    *before* the Haskell layer emits the new code, or all three bindings
    will surface ``"Unknown error code N"`` instead of the real message.
    """

    # Agda: ``Aletheia.CAN.BatchExtraction.NotInDBC``
    NOT_IN_DBC = 0
    # Agda: ``Aletheia.CAN.BatchExtraction.OutOfBounds``
    OUT_OF_BOUNDS = 1
    # Agda: ``Aletheia.CAN.BatchExtraction.ExtractionFailed``
    EXTRACTION_FAILED = 2


# Human-readable message for each code — keyed on the enum so a renamed
# Agda constructor surfaces as an ``IntEnum`` membership error rather than
# a silently shifted message.  The tuple alias below keeps the ``[code]``
# lookup shape used by ``_parse_errors_segment``.
EXTRACTION_ERROR_MESSAGES_BY_CODE: dict[ExtractionErrorCode, str] = {
    ExtractionErrorCode.NOT_IN_DBC: "Signal not found in DBC",
    ExtractionErrorCode.OUT_OF_BOUNDS: "Value out of bounds",
    ExtractionErrorCode.EXTRACTION_FAILED: "Extraction failed",
}

# Legacy positional alias preserved for the existing ``_parse_errors_segment``
# fast path and for any external caller indexing by integer.  ``ExtractionError
# Code(i)`` validates membership so a wire code outside the enum raises
# ``ValueError`` before the tuple index is taken.
EXTRACTION_ERROR_MESSAGES: tuple[str, ...] = tuple(
    EXTRACTION_ERROR_MESSAGES_BY_CODE[ExtractionErrorCode(i)]
    for i in range(len(ExtractionErrorCode))
)


@dataclass(frozen=True, slots=True)
class FrameIdentity:
    """CAN frame identity (ID + ID width + DLC) used by all binary calls."""
    can_id: int
    extended: bool
    dlc: int


@dataclass(frozen=True, slots=True)
class SignalValues:
    """Parallel lists of signal indices and rational values (num/den)."""
    indices: list[int]
    numerators: list[int]
    denominators: list[int]


def _decode_and_raise(
    lib: ctypes.CDLL,
    out_err: ctypes.c_char_p,
    prefix: str,
) -> NoReturn:
    """Decode a C error string out-parameter, free it, and raise ProcessError.

    Raises ``ProcessError`` with the decoded UTF-8 message prefixed by
    *prefix*, or ``"Unknown error"`` if the pointer is null.
    """
    # ctypes.cast narrows to bytes|None correctly for pylint (direct
    # out_err.value flags .decode as no-member).
    raw_err = ctypes.cast(out_err, ctypes.c_char_p).value
    if raw_err is None:
        raise ProcessError(f"{prefix}: Unknown error")
    err_msg = raw_err.decode("utf-8")
    lib.aletheia_free_str(out_err)
    raise ProcessError(f"{prefix}: {err_msg}")


def _parse_values_segment(
    buf: bytes, off: int, count: int, names: Sequence[str],
) -> tuple[dict[str, Fraction], int]:
    """Parse the values segment: ``count`` × ``<Hqq`` (18 bytes each).

    Returns Fraction values to preserve exact rational precision from the
    Agda core — the wire format already carries int64 numerator/denominator
    pairs, so no quantization is needed.
    """
    needed = off + count * 18
    if len(buf) < needed:
        raise ProcessError(
            f"Truncated values segment: need {needed} bytes, have {len(buf)}"
        )
    values: dict[str, Fraction] = {}
    for _ in range(count):
        idx, num, den = map(int, struct.unpack_from("<Hqq", buf, off))
        off += 18
        name = names[idx] if idx < len(names) else f"signal_{idx}"
        values[name] = Fraction(num, den) if den != 0 else Fraction(0)
    return values, off


def _parse_errors_segment(
    buf: bytes, off: int, count: int, names: Sequence[str],
) -> tuple[dict[str, str], int]:
    """Parse the errors segment: ``count`` × ``<HB`` (3 bytes each)."""
    needed = off + count * 3
    if len(buf) < needed:
        raise ProcessError(
            f"Truncated errors segment: need {needed} bytes, have {len(buf)}"
        )
    errors: dict[str, str] = {}
    for _ in range(count):
        idx, code = map(int, struct.unpack_from("<HB", buf, off))
        off += 3
        name = names[idx] if idx < len(names) else f"signal_{idx}"
        # Validate against the Agda-mirrored enum; unknown codes are
        # surfaced verbatim so a binding/Agda skew is visible in logs
        # rather than silently coerced to an existing message.
        try:
            errors[name] = EXTRACTION_ERROR_MESSAGES_BY_CODE[ExtractionErrorCode(code)]
        except ValueError:
            errors[name] = f"Unknown error code {code}"
    return errors, off


def _parse_absent_segment(
    buf: bytes, off: int, count: int, names: Sequence[str],
) -> tuple[list[str], int]:
    """Parse the absent segment: ``count`` × ``<H`` (2 bytes each)."""
    needed = off + count * 2
    if len(buf) < needed:
        raise ProcessError(
            f"Truncated absent segment: need {needed} bytes, have {len(buf)}"
        )
    absent: list[str] = []
    for _ in range(count):
        (idx,) = map(int, struct.unpack_from("<H", buf, off))
        off += 2
        absent.append(names[idx] if idx < len(names) else f"signal_{idx}")
    return absent, off


def parse_extraction_buffer(
    buf: bytes, names: Sequence[str],
) -> SignalExtractionResult:
    """Parse the packed binary extraction response.

    Layout: 6-byte header (three ``u16`` counts: values / errors / absent)
    followed by each segment in that order.
    """
    if len(buf) < 6:
        raise ProcessError(
            f"Binary extraction buffer too short: {len(buf)} bytes (need >= 6)"
        )
    nvals, nerrs, nabss = map(int, struct.unpack_from("<HHH", buf, 0))
    values, off = _parse_values_segment(buf, 6, nvals, names)
    errors, off = _parse_errors_segment(buf, off, nerrs, names)
    absent, _ = _parse_absent_segment(buf, off, nabss, names)
    return SignalExtractionResult(values=values, errors=errors, absent=tuple(absent))


class BinaryFFI:
    """Wraps the three binary-path C entry points.

    Holds references to the loaded shared library and the opaque state
    pointer.  Instances are cheap to create (no cached state) so the
    client constructs a fresh wrapper per binary-path call rather than
    holding one as an instance attribute.
    """

    def __init__(
        self, lib: ctypes.CDLL, state: ctypes.c_void_p,
    ) -> None:
        self._lib = lib
        self._state = state

    def extract_signals(
        self,
        frame_id: FrameIdentity,
        data: ctypes.Array[ctypes.c_uint8],
        names: Sequence[str],
    ) -> SignalExtractionResult:
        """Extract signals via the binary path (no JSON on in/out)."""
        out_buf = ctypes.POINTER(ctypes.c_uint8)()
        out_size = ctypes.c_uint32()
        out_err = ctypes.c_char_p()
        status = self._lib.aletheia_extract_signals_bin(
            self._state,
            ctypes.c_uint32(frame_id.can_id),
            ctypes.c_uint8(1 if frame_id.extended else 0),
            ctypes.c_uint8(frame_id.dlc),
            data,
            ctypes.c_uint8(len(data)),
            ctypes.byref(out_buf),
            ctypes.byref(out_size),
            ctypes.byref(out_err),
        )
        if status != 0:
            _decode_and_raise(self._lib, out_err, "extract_signals failed")
        try:
            buf = bytes(
                ctypes.cast(
                    out_buf, ctypes.POINTER(ctypes.c_uint8 * out_size.value),
                ).contents
            )
        finally:
            self._lib.aletheia_free_buf(out_buf)
        return parse_extraction_buffer(buf, names)

    def update_frame(
        self,
        frame_id: FrameIdentity,
        frame_data: ctypes.Array[ctypes.c_uint8],
        signals: SignalValues,
        expected_bytes: int,
    ) -> bytearray:
        """Update specific signals in an existing frame via the binary path."""
        out_buf = (ctypes.c_uint8 * expected_bytes)()
        out_err = ctypes.c_char_p()
        n = len(signals.indices)
        status = self._lib.aletheia_update_frame_bin(
            self._state,
            ctypes.c_uint32(frame_id.can_id),
            ctypes.c_uint8(1 if frame_id.extended else 0),
            ctypes.c_uint8(frame_id.dlc),
            frame_data,
            ctypes.c_uint8(len(frame_data)),
            ctypes.c_uint32(n),
            (ctypes.c_uint32 * n)(*signals.indices),
            (ctypes.c_int64 * n)(*signals.numerators),
            (ctypes.c_int64 * n)(*signals.denominators),
            out_buf,
            ctypes.byref(out_err),
        )
        if status != 0:
            _decode_and_raise(self._lib, out_err, "update_frame failed")
        return bytearray(out_buf)

    def build_frame(
        self,
        frame_id: FrameIdentity,
        signals: SignalValues,
        expected_bytes: int,
    ) -> bytearray:
        """Build a frame from signal values via the binary path."""
        out_buf = (ctypes.c_uint8 * expected_bytes)()
        out_err = ctypes.c_char_p()
        n = len(signals.indices)
        status = self._lib.aletheia_build_frame_bin(
            self._state,
            ctypes.c_uint32(frame_id.can_id),
            ctypes.c_uint8(1 if frame_id.extended else 0),
            ctypes.c_uint8(frame_id.dlc),
            ctypes.c_uint32(n),
            (ctypes.c_uint32 * n)(*signals.indices),
            (ctypes.c_int64 * n)(*signals.numerators),
            (ctypes.c_int64 * n)(*signals.denominators),
            out_buf,
            ctypes.byref(out_err),
        )
        if status != 0:
            _decode_and_raise(self._lib, out_err, "build_frame failed")
        return bytearray(out_buf)
