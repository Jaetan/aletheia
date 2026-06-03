# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Binary-FFI response parsing helpers for signal extraction.

Hosts the packed-binary parser for ``aletheia_extract_signals_bin``'s
response buffer (3 segments × ``<HHH`` count header), the
:class:`ExtractionErrorCode` enum mirroring the Agda core's wire-format
constants, and the small dataclasses (:class:`FrameIdentity` /
:class:`SignalValues`) callers thread through the Backend's binary-FFI
methods.

Originally this module also hosted the ``BinaryFFI`` class that owned
the ``ctypes`` plumbing for the three binary entry points; that
responsibility moved to :class:`aletheia.client.FFIBackend` in
``_backend.py`` so the Backend Protocol owns the FFI boundary uniformly.
What remains here is wire-format parsing — independent of how the bytes
were obtained.
"""

import struct
from dataclasses import dataclass
from enum import IntEnum
from fractions import Fraction
from typing import TYPE_CHECKING

from aletheia.client._types import ProtocolError, SignalExtractionResult

if TYPE_CHECKING:
    from collections.abc import Sequence

    from aletheia.protocols import DLCCode

# The binary extraction response opens with a three-``u16`` count header
# (values / errors / absent); ``<HHH`` is 6 bytes.
_HEADER_BYTES = struct.calcsize("<HHH")


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
    dlc: DLCCode


@dataclass(frozen=True, slots=True)
class SignalValues:
    """Parallel tuples of signal indices and rational values (num/den)."""

    indices: tuple[int, ...]
    numerators: tuple[int, ...]
    denominators: tuple[int, ...]


def _parse_values_segment(
    buf: bytes,
    off: int,
    count: int,
    names: Sequence[str],
) -> tuple[dict[str, Fraction], int]:
    """Parse the values segment: ``count`` × ``<Hqq`` (18 bytes each).

    Returns Fraction values to preserve exact rational precision from the
    Agda core — the wire format already carries int64 numerator/denominator
    pairs, so no quantization is needed.
    """
    needed = off + count * 18
    if len(buf) < needed:
        msg = f"Truncated values segment: need {needed} bytes, have {len(buf)}"
        raise ProtocolError(msg)
    values: dict[str, Fraction] = {}
    for _ in range(count):
        idx, num, den = map(int, struct.unpack_from("<Hqq", buf, off))
        off += 18
        name = names[idx] if idx < len(names) else f"signal_{idx}"
        if den == 0:
            msg = f"Zero denominator in extraction value for {name!r}"
            raise ProtocolError(msg)
        values[name] = Fraction(num, den)
    return values, off


def _parse_errors_segment(
    buf: bytes,
    off: int,
    count: int,
    names: Sequence[str],
) -> tuple[dict[str, str], int]:
    """Parse the errors segment: ``count`` × ``<HB`` (3 bytes each)."""
    needed = off + count * 3
    if len(buf) < needed:
        msg = f"Truncated errors segment: need {needed} bytes, have {len(buf)}"
        raise ProtocolError(msg)
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
    buf: bytes,
    off: int,
    count: int,
    names: Sequence[str],
) -> tuple[list[str], int]:
    """Parse the absent segment: ``count`` × ``<H`` (2 bytes each)."""
    needed = off + count * 2
    if len(buf) < needed:
        msg = f"Truncated absent segment: need {needed} bytes, have {len(buf)}"
        raise ProtocolError(msg)
    absent: list[str] = []
    for _ in range(count):
        (idx,) = map(int, struct.unpack_from("<H", buf, off))
        off += 2
        absent.append(names[idx] if idx < len(names) else f"signal_{idx}")
    return absent, off


def parse_extraction_buffer(
    buf: bytes,
    names: Sequence[str],
) -> SignalExtractionResult:
    """Parse the packed binary extraction response.

    Layout: 6-byte header (three ``u16`` counts: values / errors / absent)
    followed by each segment in that order.
    """
    if len(buf) < _HEADER_BYTES:
        msg = f"Binary extraction buffer too short: {len(buf)} bytes (need >= {_HEADER_BYTES})"
        raise ProtocolError(msg)
    nvals, nerrs, nabss = map(int, struct.unpack_from("<HHH", buf, 0))
    values, off = _parse_values_segment(buf, _HEADER_BYTES, nvals, names)
    errors, off = _parse_errors_segment(buf, off, nerrs, names)
    absent, _ = _parse_absent_segment(buf, off, nabss, names)
    return SignalExtractionResult(values=values, errors=errors, absent=tuple(absent))


__all__ = [
    "EXTRACTION_ERROR_MESSAGES",
    "EXTRACTION_ERROR_MESSAGES_BY_CODE",
    "ExtractionErrorCode",
    "FrameIdentity",
    "SignalValues",
    "parse_extraction_buffer",
]
