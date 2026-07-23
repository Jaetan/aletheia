# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for binary extraction buffer parsing (_client_bin.py).

Crafted-byte vectors lock the packed wire layout (``<HHHI`` header,
values / errors / offsets / reasons / absent segments) and the decoder's
protocol-error rejects; the real-FFI class at the bottom pins reason
parity between the binary wire and the JSON fallback path.
"""

import struct
from fractions import Fraction
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, BinaryPathUnsupportedError, FFIBackend, ProtocolError
from aletheia.client._client_bin import (
    ExtractionErrorCode,
    parse_extraction_buffer,
)
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from collections.abc import Sequence

NAMES = ("Speed", "RPM", "Temp", "Mode")

_AGDA_EXTRACTION = (
    Path(__file__).resolve().parents[2] / "src" / "Aletheia" / "CAN" / "BatchExtraction.agda"
)
_AGDA_EXTRACTION_MISSING = not _AGDA_EXTRACTION.exists()
_AGDA_SKIP_REASON = (
    "Agda source required for ExtractionErrorCode drift test but not at "
    f"{_AGDA_EXTRACTION} — skip from installed-wheel test runs; "
    "``pytest.fail`` stays for structural parse failures."
)


def _extraction_buffer(
    values: Sequence[tuple[int, int, int]] = (),
    errors: Sequence[tuple[int, int, str]] = (),
    absent: Sequence[int] = (),
) -> bytes:
    """Pack a wire-conformant extraction response buffer.

    ``values`` entries are (signal_index, numerator, denominator);
    ``errors`` entries are (signal_index, code, reason).  The offsets
    table and reasons blob are derived from the reasons' UTF-8 byte
    lengths, matching the layout in the ``processExtractBin`` header
    comment of ``Aletheia.Main.Binary``.
    """
    reason_blobs = [reason.encode("utf-8") for _, _, reason in errors]
    offsets = [0]
    for blob in reason_blobs:
        offsets.append(offsets[-1] + len(blob))
    parts = [struct.pack("<HHHI", len(values), len(errors), len(absent), offsets[-1])]
    parts.extend(struct.pack("<Hqq", idx, num, den) for idx, num, den in values)
    parts.extend(struct.pack("<HB", idx, code) for idx, code, _ in errors)
    parts.append(struct.pack(f"<{len(errors) + 1}I", *offsets))
    parts.extend(reason_blobs)
    parts.extend(struct.pack("<H", idx) for idx in absent)
    return b"".join(parts)


class TestParseExtractionBuffer:
    """Test parse_extraction_buffer on the packed binary format."""

    def test_single_value(self) -> None:
        """One value, no errors (offsets table is the single 0), no absent."""
        result = parse_extraction_buffer(_extraction_buffer(values=[(0, 100, 1)]), NAMES)
        assert result.values == {"Speed": 100.0}
        assert result.errors == {}
        assert result.absent == ()

    def test_multiple_values(self) -> None:
        """Three values extracted."""
        buf = _extraction_buffer(values=[(0, 220, 1), (1, 3500, 1), (2, 85, 2)])
        result = parse_extraction_buffer(buf, NAMES)
        assert result.values == {"Speed": 220.0, "RPM": 3500.0, "Temp": 42.5}

    def test_denominator_zero_raises(self) -> None:
        """Denominator zero raises ProtocolError (not silent coercion)."""
        buf = _extraction_buffer(values=[(0, 999, 0)])
        with pytest.raises(ProtocolError, match="Zero denominator"):
            parse_extraction_buffer(buf, NAMES)

    def test_signal_index_out_of_range(self) -> None:
        """Index beyond names list uses fallback name."""
        result = parse_extraction_buffer(_extraction_buffer(values=[(99, 42, 1)]), NAMES)
        assert result.values == {"signal_99": 42.0}

    def test_all_segments_with_multibyte_utf8_reason(self) -> None:
        """Value + two distinct wire reasons (one multi-byte UTF-8) + absent.

        The first reason contains multi-byte UTF-8 characters, so the
        second reason's slice only decodes correctly if the offsets are
        byte counts (not character counts) — decoding both exactly pins
        that.
        """
        multibyte = "signal 'Törnwächter' not found in message"
        bounds = "value out of bounds: 16383.75 not in [0, 8000]"
        buf = _extraction_buffer(
            values=[(0, 220, 1)],
            errors=[
                (1, int(ExtractionErrorCode.NOT_IN_DBC), multibyte),
                (2, int(ExtractionErrorCode.OUT_OF_BOUNDS), bounds),
            ],
            absent=[3],
        )
        result = parse_extraction_buffer(buf, NAMES)
        assert result.values == {"Speed": 220.0}
        assert result.errors == {"RPM": multibyte, "Temp": bounds}
        assert result.absent == ("Mode",)

    def test_unknown_error_code_transported_with_wire_reason(self) -> None:
        """A code outside the enum is not rejected — the reason is authoritative."""
        buf = _extraction_buffer(errors=[(0, 255, "reason minted by a future kernel")])
        result = parse_extraction_buffer(buf, NAMES)
        assert result.errors == {"Speed": "reason minted by a future kernel"}

    def test_known_code_surfaces_wire_reason_verbatim(self) -> None:
        """The decoder surfaces the wire reason, not a code-derived message."""
        reason = "extracted value's numerator or denominator exceeds the Int64 wire range"
        buf = _extraction_buffer(
            errors=[(0, int(ExtractionErrorCode.VALUE_EXCEEDS_WIRE_RANGE), reason)]
        )
        result = parse_extraction_buffer(buf, NAMES)
        assert result.errors == {"Speed": reason}

    def test_absent_segment(self) -> None:
        """Absent entries decoded."""
        result = parse_extraction_buffer(_extraction_buffer(absent=[1, 2]), NAMES)
        assert result.absent == ("RPM", "Temp")

    def test_empty_buffer_too_short(self) -> None:
        """Buffer shorter than 10 bytes raises ProtocolError."""
        with pytest.raises(ProtocolError, match="too short"):
            parse_extraction_buffer(b"", NAMES)

    def test_nine_byte_buffer_too_short(self) -> None:
        """9-byte buffer is still too short for the header."""
        with pytest.raises(ProtocolError, match="too short"):
            parse_extraction_buffer(b"\x00" * 9, NAMES)

    def test_empty_result(self) -> None:
        """Zero counts: the offsets table is the single u32 0, reasonBytes 0."""
        buf = _extraction_buffer()
        assert buf == struct.pack("<HHHI", 0, 0, 0, 0) + struct.pack("<I", 0)
        result = parse_extraction_buffer(buf, NAMES)
        assert result.values == {}
        assert result.errors == {}
        assert result.absent == ()

    def test_trailing_byte_rejected(self) -> None:
        """One byte past the header-implied total raises ProtocolError."""
        buf = _extraction_buffer(values=[(0, 100, 1)])
        with pytest.raises(ProtocolError, match="trailing"):
            parse_extraction_buffer(buf + b"\x00", NAMES)

    def test_truncated_buffer_rejected(self) -> None:
        """One byte short of the header-implied total raises ProtocolError."""
        buf = _extraction_buffer(values=[(0, 100, 1)])
        with pytest.raises(ProtocolError, match="Truncated"):
            parse_extraction_buffer(buf[:-1], NAMES)

    def test_first_offset_nonzero_rejected(self) -> None:
        """off[0] != 0 raises ProtocolError."""
        buf = (
            struct.pack("<HHHI", 0, 1, 0, 1)
            + struct.pack("<HB", 0, 0)
            + struct.pack("<II", 1, 1)
            + b"x"
        )
        with pytest.raises(ProtocolError, match="start at 0"):
            parse_extraction_buffer(buf, NAMES)

    def test_non_monotone_offsets_rejected(self) -> None:
        """A decreasing offset pair raises ProtocolError."""
        buf = (
            struct.pack("<HHHI", 0, 2, 0, 1)
            + struct.pack("<HB", 0, 0)
            + struct.pack("<HB", 1, 1)
            + struct.pack("<III", 0, 2, 1)
            + b"x"
        )
        with pytest.raises(ProtocolError, match="monotone"):
            parse_extraction_buffer(buf, NAMES)

    def test_final_offset_reason_bytes_mismatch_rejected(self) -> None:
        """off[nErrors] != reasonBytes raises ProtocolError."""
        buf = (
            struct.pack("<HHHI", 0, 1, 0, 2)
            + struct.pack("<HB", 0, 0)
            + struct.pack("<II", 0, 1)
            + b"xy"
        )
        with pytest.raises(ProtocolError, match="reasonBytes"):
            parse_extraction_buffer(buf, NAMES)

    def test_invalid_utf8_reason_rejected(self) -> None:
        """Invalid UTF-8 inside a reason slice raises ProtocolError."""
        buf = (
            struct.pack("<HHHI", 0, 1, 0, 2)
            + struct.pack("<HB", 0, 0)
            + struct.pack("<II", 0, 2)
            + b"\xff\xfe"
        )
        with pytest.raises(ProtocolError, match="Invalid UTF-8"):
            parse_extraction_buffer(buf, NAMES)

    def test_fraction_exact_roundtrip(self) -> None:
        """Extraction preserves exact rationals (no float quantization)."""
        # 1/3 is not representable as IEEE 754 double
        result = parse_extraction_buffer(_extraction_buffer(values=[(0, 1, 3)]), NAMES)
        assert result.values["Speed"] == Fraction(1, 3)
        # Verify it's an exact Fraction, not a float approximation
        assert isinstance(result.values["Speed"], Fraction)
        assert result.values["Speed"].numerator == 1
        assert result.values["Speed"].denominator == 3


def _agda_constructors() -> list[str]:
    """Parse the Agda source for ``ExtractionErrorCode`` constructors."""
    lines = _AGDA_EXTRACTION.read_text(encoding="utf-8").splitlines()
    # Find the data block; constructors follow with 2-space indent until
    # a non-indented line or blank line is reached.
    try:
        start = next(
            i for i, line in enumerate(lines) if line.startswith("data ExtractionErrorCode")
        )
    except StopIteration:
        pytest.fail("``data ExtractionErrorCode`` block not found in Agda source")
    ctors: list[str] = []
    for line in lines[start + 1 :]:
        stripped = line.strip()
        if not stripped or not line.startswith(" "):
            break
        # Documentation comments interleave with constructors inside
        # the data block — they are not constructor lines.
        if stripped.startswith("--"):
            continue
        # Constructor lines look like ``Name : ExtractionErrorCode ...``
        head = stripped.split(":", 1)[0].strip()
        if head:
            ctors.append(head)
    return ctors


@pytest.mark.skipif(_AGDA_EXTRACTION_MISSING, reason=_AGDA_SKIP_REASON)
def test_enum_matches_agda_constructor_order() -> None:
    """Guard the Python enum against Agda drift.

    ``ExtractionErrorCode`` mirrors ``Aletheia.CAN.BatchExtraction.
    ExtractionErrorCode`` (enum values match ``extractionErrorCodeToℕ``).
    The Agda source is the authoritative manifest; this test reads the
    constructor order directly from ``src/Aletheia/CAN/BatchExtraction.agda``
    so that adding, removing, or reordering an Agda constructor breaks
    this test instead of silently skewing the wire vocabulary the enum
    documents.
    """
    # Agda → Python name mapping: both are stable by design; adding a
    # new Agda constructor forces a parallel addition here AND in the
    # Go/C++/Rust bindings (see AGENTS.md cross-binding parity rule).
    expected_name_for_code = {
        "NotInDBC": "NOT_IN_DBC",
        "OutOfBounds": "OUT_OF_BOUNDS",
        "BitExtractionFailed": "BIT_EXTRACTION_FAILED",
        "ValueExceedsWireRange": "VALUE_EXCEEDS_WIRE_RANGE",
        "MuxSignalNotFound": "MUX_SIGNAL_NOT_FOUND",
        "MuxChainCycle": "MUX_CHAIN_CYCLE",
        "MuxExtractionFailed": "MUX_EXTRACTION_FAILED",
        "MuxValueMismatch": "MUX_VALUE_MISMATCH",
    }
    agda_ctors = _agda_constructors()
    assert agda_ctors, "no constructors parsed from Agda source"
    assert len(agda_ctors) == len(ExtractionErrorCode), (
        f"Agda has {len(agda_ctors)} constructors, Python enum has "
        f"{len(ExtractionErrorCode)} — update Python to match"
    )
    for i, agda_name in enumerate(agda_ctors):
        py_name = expected_name_for_code.get(agda_name)
        assert py_name is not None, (
            f"Agda constructor {agda_name!r} has no Python mirror; add it to ExtractionErrorCode"
        )
        py_member = ExtractionErrorCode[py_name]
        assert py_member.value == i, (
            f"{agda_name} is Agda constructor #{i} but Python {py_name} = {py_member.value}"
        )


class _JSONPathOnlyBackend(FFIBackend):
    """Real FFI backend that refuses the binary extraction fast path.

    Forces ``extract_signals`` down the JSON fallback (the Client catches
    :class:`BinaryPathUnsupportedError`) so both wire paths can be
    compared end-to-end against the same kernel.
    """

    def extract_signals_bin(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Raise unconditionally so the Client takes the JSON path."""
        del state, can_id, extended, dlc, data
        msg = "binary extraction path disabled for JSON/binary parity comparison"
        raise BinaryPathUnsupportedError(msg)


def test_out_of_bounds_reason_identical_on_binary_and_json_paths() -> None:
    """The same frame yields the exact same detailed reason on both wires.

    Real-FFI reason-parity pin: the frame's raw value scales past the
    signal's maximum, so both paths must partition the signal into
    ``errors`` with the kernel-minted out-of-bounds reason (which names
    the offending value) — asserting exact dict equality pins the binary
    wire's reason strings to the JSON path's.
    """
    bounds_dbc = dbc(
        [
            message(
                256,
                "M",
                [signal("Speed", factor=Fraction(1, 4), maximum=Fraction(8000))],
            )
        ]
    )
    frame = bytearray([0xFF, 0xFF, 0, 0, 0, 0, 0, 0])
    with AletheiaClient() as client:
        assert client.parse_dbc(bounds_dbc)["status"] == "success"
        bin_result = client.extract_signals(can_id=256, dlc=DLCCode(8), data=frame)
    with AletheiaClient(backend=_JSONPathOnlyBackend()) as client:
        assert client.parse_dbc(bounds_dbc)["status"] == "success"
        json_result = client.extract_signals(can_id=256, dlc=DLCCode(8), data=frame)
    assert list(bin_result.errors) == ["Speed"], dict(bin_result.errors)
    # Detailed kernel-minted reason (names the offending value), not a
    # generic per-code label.
    assert "not in [" in bin_result.errors["Speed"]
    assert bin_result.errors == json_result.errors
    assert bin_result.values == json_result.values == {}
    assert bin_result.absent == json_result.absent == ()
