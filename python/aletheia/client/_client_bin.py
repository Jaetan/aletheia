"""Binary FFI helpers for signal extraction, frame update, and frame build.

Wraps the three C entry points (``aletheia_extract_signals_bin``,
``aletheia_update_frame_bin``, ``aletheia_build_frame_bin``) behind a
small class that owns references to the loaded library and the opaque
state pointer.  Separating these out of ``_client.py`` keeps the main
client module focused on high-level protocol flow and lets the
binary-path helpers stay under pylint's complexity thresholds.
"""

from __future__ import annotations

import ctypes
import struct
from collections.abc import Sequence
from dataclasses import dataclass
from typing import NoReturn

from ._types import ProcessError, SignalExtractionResult


# Positional mapping of Agda's binary extraction error codes to human-readable
# messages.  The index matches the ``ExtractionError`` constructor order in
# ``Aletheia.CAN.Encoding``: 0 = SignalNotFound, 1 = ValueOutOfBounds,
# 2 = ExtractionFailed.  The binary FFI encodes these as a single ``u8``
# in the ``<HB`` errors segment (see ``_parse_errors_segment``).
EXTRACTION_ERROR_MESSAGES: tuple[str, ...] = (
    "Signal not found in DBC",     # 0
    "Value out of bounds",          # 1
    "Extraction failed",            # 2
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
) -> tuple[dict[str, float], int]:
    """Parse the values segment: ``count`` × ``<Hqq`` (18 bytes each)."""
    values: dict[str, float] = {}
    for _ in range(count):
        idx, num, den = map(int, struct.unpack_from("<Hqq", buf, off))
        off += 18
        name = names[idx] if idx < len(names) else f"signal_{idx}"
        values[name] = num / den if den != 0 else 0.0
    return values, off


def _parse_errors_segment(
    buf: bytes, off: int, count: int, names: Sequence[str],
) -> tuple[dict[str, str], int]:
    """Parse the errors segment: ``count`` × ``<HB`` (3 bytes each)."""
    errors: dict[str, str] = {}
    for _ in range(count):
        idx, code = map(int, struct.unpack_from("<HB", buf, off))
        off += 3
        name = names[idx] if idx < len(names) else f"signal_{idx}"
        if code < len(EXTRACTION_ERROR_MESSAGES):
            errors[name] = EXTRACTION_ERROR_MESSAGES[code]
        else:
            errors[name] = f"Unknown error code {code}"
    return errors, off


def _parse_absent_segment(
    buf: bytes, off: int, count: int, names: Sequence[str],
) -> tuple[list[str], int]:
    """Parse the absent segment: ``count`` × ``<H`` (2 bytes each)."""
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
        buf = bytes(
            ctypes.cast(
                out_buf, ctypes.POINTER(ctypes.c_uint8 * out_size.value),
            ).contents
        )
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
