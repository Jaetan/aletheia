# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Binary-FFI response parsing helpers for signal extraction.

Hosts the packed-binary parser for ``aletheia_extract_signals_bin``'s
response buffer, the :class:`ExtractionErrorCode` enum mirroring the Agda
core's wire-format constants, and the small dataclasses
(:class:`FrameIdentity` / :class:`SignalValues`) callers thread through
the Backend's binary-FFI methods.  Wire-format parsing only — independent
of how the bytes were obtained (the ``ctypes`` plumbing lives in
:class:`aletheia.FFIBackend`).

The canonical wire doc is the ``processExtractBin`` header comment in
``Aletheia.Main.Binary``; the layout parsed here:

- Header:  ``<HHHI`` — nValues, nErrors, nAbsent (``u16`` each) +
  reasonBytes (``u32``)
- Values:  nValues × (idx ``u16``, numerator ``i64``, denominator ``i64``)
- Errors:  nErrors × (idx ``u16``, code ``u8``)
- Offsets: (nErrors + 1) × ``u32`` cumulative byte offsets into Reasons —
  always present (a single 0 when nErrors is 0)
- Reasons: reasonBytes of UTF-8; error *i*'s reason is the byte slice
  ``[off[i], off[i+1])``
- Absent:  nAbsent × (idx ``u16``)

The error reason strings come from the wire verbatim — kernel-minted,
byte-identical to what the JSON path surfaces for the same error (shared
``resultToString``; machine-checked reason-parity).
"""

import struct
from dataclasses import dataclass
from enum import IntEnum
from fractions import Fraction
from typing import TYPE_CHECKING

from aletheia.client._types import ProtocolError, SignalExtractionResult

if TYPE_CHECKING:
    from collections.abc import Sequence

    from aletheia.types import DLCCode

# The binary extraction response opens with three ``u16`` counts
# (values / errors / absent) plus the ``u32`` reasons-blob byte length;
# ``<HHHI`` is 10 bytes.
_HEADER_FMT = "<HHHI"
_HEADER_BYTES = struct.calcsize(_HEADER_FMT)

# Fixed per-entry sizes of the four count-driven segments.
_VALUE_ENTRY_BYTES = struct.calcsize("<Hqq")
_ERROR_ENTRY_BYTES = struct.calcsize("<HB")
_OFFSET_ENTRY_BYTES = struct.calcsize("<I")
_ABSENT_ENTRY_BYTES = struct.calcsize("<H")


class ExtractionErrorCode(IntEnum):
    """Binary-FFI extraction error codes shared with the Agda core.

    Documents the wire vocabulary: each constructor of
    ``Aletheia.CAN.BatchExtraction.ExtractionErrorCode`` serializes to a
    single ``u8`` in the ``<HB`` errors segment of the binary response,
    and ``extractionErrorCodeToℕ`` (injectivity machine-checked) pins the
    constructors to the integers below.

    The ``u8`` code travels the wire for machine consumption only — the
    decoder surfaces the kernel-minted reason string carried alongside it
    and does not map codes to messages, so a code outside this enum is
    transported without rejection (the wire reason is authoritative).
    Changing a value or removing a member is a breaking wire change; any
    new Agda constructor must be mirrored here (and in the Go / C++ / Rust
    bindings) so the vocabulary stays in sync across bindings.
    """

    # Agda: ``Aletheia.CAN.BatchExtraction.NotInDBC``
    NOT_IN_DBC = 0
    # Agda: ``Aletheia.CAN.BatchExtraction.OutOfBounds``
    OUT_OF_BOUNDS = 1
    # Agda: ``Aletheia.CAN.BatchExtraction.BitExtractionFailed``
    BIT_EXTRACTION_FAILED = 2
    # Agda: ``Aletheia.CAN.BatchExtraction.ValueExceedsWireRange`` — the
    # exact value's reduced numerator or denominator exceeds the signed
    # 64-bit range of the wire's rational slots; the FFI shim reroutes the
    # signal here instead of letting the int64 slot wrap silently.
    VALUE_EXCEEDS_WIRE_RANGE = 3
    # Agda: ``Aletheia.CAN.BatchExtraction.MuxSignalNotFound``
    MUX_SIGNAL_NOT_FOUND = 4
    # Agda: ``Aletheia.CAN.BatchExtraction.MuxChainCycle``
    MUX_CHAIN_CYCLE = 5
    # Agda: ``Aletheia.CAN.BatchExtraction.MuxExtractionFailed``
    MUX_EXTRACTION_FAILED = 6
    # Agda: ``Aletheia.CAN.BatchExtraction.MuxValueMismatch`` — never
    # emitted by the kernel (that condition routes to the absent
    # partition); listed so every Agda constructor owns a distinct code.
    MUX_VALUE_MISMATCH = 7


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


def _signal_name(names: Sequence[str], idx: int) -> str:
    """Resolve a wire signal index against the caller's name table.

    Used by the error / absent segment parsers; the values loop inlines the
    same conditional because a per-entry helper call is measurable on the
    per-frame extraction hot path.
    """
    return names[idx] if idx < len(names) else f"signal_{idx}"


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
    values: dict[str, Fraction] = {}
    n_names = len(names)
    for _ in range(count):
        idx, num, den = map(int, struct.unpack_from("<Hqq", buf, off))
        off += _VALUE_ENTRY_BYTES
        name = names[idx] if idx < n_names else f"signal_{idx}"
        if den == 0:
            msg = f"Zero denominator in extraction value for {name!r}"
            raise ProtocolError(msg)
        values[name] = Fraction(num, den)
    return values, off


def _parse_error_entries(
    buf: bytes,
    off: int,
    count: int,
    names: Sequence[str],
) -> tuple[list[str], int]:
    """Parse the errors segment: ``count`` × ``<HB`` (3 bytes each).

    Returns the per-entry signal names in wire order.  The ``u8`` code is
    transported for machine consumption only and never rejected — the
    reason string delimited by the offsets table is authoritative, so an
    unknown code still decodes to its wire reason.
    """
    entry_names: list[str] = []
    for _ in range(count):
        idx, _code = map(int, struct.unpack_from("<HB", buf, off))
        off += _ERROR_ENTRY_BYTES
        entry_names.append(_signal_name(names, idx))
    return entry_names, off


def _parse_reasons(
    buf: bytes,
    off: int,
    count: int,
    reason_bytes: int,
) -> tuple[list[str], int]:
    """Parse the offsets table + UTF-8 reasons blob for ``count`` errors.

    The offsets table ((count + 1) × ``<I``, present even when ``count``
    is 0) carries cumulative byte offsets into the reasons blob; entry *i*
    of the returned list is the UTF-8 decode of ``blob[off[i] : off[i+1]]``.
    """
    offsets = tuple(map(int, struct.unpack_from(f"<{count + 1}I", buf, off)))
    off += (count + 1) * _OFFSET_ENTRY_BYTES
    if offsets[0] != 0:
        msg = f"Extraction reason offsets must start at 0, got {offsets[0]}"
        raise ProtocolError(msg)
    for i in range(count):
        if offsets[i] > offsets[i + 1]:
            msg = (
                "Extraction reason offsets not monotone non-decreasing: "
                f"offset[{i}] = {offsets[i]} > offset[{i + 1}] = {offsets[i + 1]}"
            )
            raise ProtocolError(msg)
    if offsets[count] != reason_bytes:
        msg = (
            f"Extraction reason offsets end at {offsets[count]}, "
            f"expected reasonBytes {reason_bytes}"
        )
        raise ProtocolError(msg)
    blob = buf[off : off + reason_bytes]
    reasons: list[str] = []
    for i in range(count):
        try:
            reasons.append(blob[offsets[i] : offsets[i + 1]].decode("utf-8"))
        except UnicodeDecodeError as exc:
            msg = f"Invalid UTF-8 in extraction error reason {i}: {exc}"
            raise ProtocolError(msg) from exc
    return reasons, off + reason_bytes


def _parse_absent_segment(
    buf: bytes,
    off: int,
    count: int,
    names: Sequence[str],
) -> tuple[list[str], int]:
    """Parse the absent segment: ``count`` × ``<H`` (2 bytes each)."""
    absent: list[str] = []
    for _ in range(count):
        (idx,) = map(int, struct.unpack_from("<H", buf, off))
        off += _ABSENT_ENTRY_BYTES
        absent.append(_signal_name(names, idx))
    return absent, off


def parse_extraction_buffer(
    buf: bytes,
    names: Sequence[str],
) -> SignalExtractionResult:
    """Parse the packed binary extraction response.

    Layout: 10-byte ``<HHHI`` header (values / errors / absent counts +
    reasons-blob byte length) followed by the Values, Errors, Offsets,
    Reasons, and Absent segments in that order (see the module docstring
    and the ``processExtractBin`` header comment in
    ``Aletheia.Main.Binary``).  The buffer length must equal the total
    the header implies exactly — shorter and longer are both rejected.
    """
    if len(buf) < _HEADER_BYTES:
        msg = f"Binary extraction buffer too short: {len(buf)} bytes (need >= {_HEADER_BYTES})"
        raise ProtocolError(msg)
    nvals, nerrs, nabss, reason_bytes = map(int, struct.unpack_from(_HEADER_FMT, buf, 0))
    expected = (
        _HEADER_BYTES
        + nvals * _VALUE_ENTRY_BYTES
        + nerrs * _ERROR_ENTRY_BYTES
        + (nerrs + 1) * _OFFSET_ENTRY_BYTES
        + reason_bytes
        + nabss * _ABSENT_ENTRY_BYTES
    )
    if len(buf) < expected:
        msg = f"Truncated binary extraction buffer: need {expected} bytes, have {len(buf)}"
        raise ProtocolError(msg)
    if len(buf) > expected:
        msg = (
            "Binary extraction buffer has trailing bytes: "
            f"expected {expected} bytes, have {len(buf)}"
        )
        raise ProtocolError(msg)
    values, off = _parse_values_segment(buf, _HEADER_BYTES, nvals, names)
    # Zero-error fast path (the per-frame hot case): with no errors and an
    # empty reasons blob, the three offsets-table invariants collapse to the
    # single entry being 0 — one read instead of the general machinery.  Any
    # other shape (including a malformed one) takes the general path below,
    # which raises the canonical invariant errors.
    if nerrs == 0 and reason_bytes == 0 and buf[off : off + 4] == b"\x00\x00\x00\x00":
        errors: dict[str, str] = {}
        off += _OFFSET_ENTRY_BYTES
    else:
        error_names, off = _parse_error_entries(buf, off, nerrs, names)
        reasons, off = _parse_reasons(buf, off, nerrs, reason_bytes)
        errors = dict(zip(error_names, reasons, strict=True))
    absent, _ = _parse_absent_segment(buf, off, nabss, names)
    return SignalExtractionResult(values=values, errors=errors, absent=tuple(absent))


__all__ = [
    "ExtractionErrorCode",
    "FrameIdentity",
    "SignalValues",
    "parse_extraction_buffer",
]
