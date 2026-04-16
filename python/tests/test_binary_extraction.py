"""Tests for binary extraction buffer parsing (_client_bin.py)."""

import struct

import pytest

from aletheia.client._client_bin import (
    EXTRACTION_ERROR_MESSAGES,
    EXTRACTION_ERROR_MESSAGES_BY_CODE,
    ExtractionErrorCode,
    parse_extraction_buffer,
)
from aletheia.client._types import ProcessError


NAMES = ("Speed", "RPM", "Temp")


class TestParseExtractionBuffer:
    """Test parse_extraction_buffer on the packed binary format."""

    def test_single_value(self) -> None:
        """One value, no errors, no absent."""
        header = struct.pack("<HHH", 1, 0, 0)
        # idx=0, numerator=100, denominator=1
        values = struct.pack("<Hqq", 0, 100, 1)
        result = parse_extraction_buffer(header + values, NAMES)
        assert result.values == {"Speed": 100.0}
        assert result.errors == {}
        assert result.absent == ()

    def test_multiple_values(self) -> None:
        """Three values extracted."""
        header = struct.pack("<HHH", 3, 0, 0)
        vals = b""
        vals += struct.pack("<Hqq", 0, 220, 1)
        vals += struct.pack("<Hqq", 1, 3500, 1)
        vals += struct.pack("<Hqq", 2, 85, 2)
        result = parse_extraction_buffer(header + vals, NAMES)
        assert result.values == {"Speed": 220.0, "RPM": 3500.0, "Temp": 42.5}

    def test_denominator_zero_raises(self) -> None:
        """Denominator zero raises ProcessError (not silent coercion)."""
        header = struct.pack("<HHH", 1, 0, 0)
        values = struct.pack("<Hqq", 0, 999, 0)
        with pytest.raises(ProcessError, match="Zero denominator"):
            parse_extraction_buffer(header + values, NAMES)

    def test_signal_index_out_of_range(self) -> None:
        """Index beyond names list uses fallback name."""
        header = struct.pack("<HHH", 1, 0, 0)
        values = struct.pack("<Hqq", 99, 42, 1)
        result = parse_extraction_buffer(header + values, NAMES)
        assert result.values == {"signal_99": 42.0}

    def test_errors_segment(self) -> None:
        """Error entries decoded with known error codes."""
        header = struct.pack("<HHH", 0, 2, 0)
        errs = struct.pack("<HB", 0, 0) + struct.pack("<HB", 1, 1)
        result = parse_extraction_buffer(header + errs, NAMES)
        assert result.errors == {
            "Speed": EXTRACTION_ERROR_MESSAGES[0],
            "RPM": EXTRACTION_ERROR_MESSAGES[1],
        }

    def test_unknown_error_code(self) -> None:
        """Error code beyond the table uses fallback."""
        header = struct.pack("<HHH", 0, 1, 0)
        errs = struct.pack("<HB", 0, 255)
        result = parse_extraction_buffer(header + errs, NAMES)
        assert result.errors == {"Speed": "Unknown error code 255"}

    def test_absent_segment(self) -> None:
        """Absent entries decoded."""
        header = struct.pack("<HHH", 0, 0, 2)
        absent = struct.pack("<HH", 1, 2)
        result = parse_extraction_buffer(header + absent, NAMES)
        assert result.absent == ("RPM", "Temp")

    def test_all_three_segments(self) -> None:
        """Mixed values, errors, and absent."""
        header = struct.pack("<HHH", 1, 1, 1)
        vals = struct.pack("<Hqq", 0, 50, 1)
        errs = struct.pack("<HB", 1, 2)
        absent = struct.pack("<H", 2)
        result = parse_extraction_buffer(header + vals + errs + absent, NAMES)
        assert result.values == {"Speed": 50.0}
        assert result.errors == {"RPM": EXTRACTION_ERROR_MESSAGES[2]}
        assert result.absent == ("Temp",)

    def test_empty_buffer_too_short(self) -> None:
        """Buffer shorter than 6 bytes raises ProcessError."""
        with pytest.raises(ProcessError, match="too short"):
            parse_extraction_buffer(b"", NAMES)

    def test_five_byte_buffer_too_short(self) -> None:
        """5-byte buffer is still too short for the header."""
        with pytest.raises(ProcessError, match="too short"):
            parse_extraction_buffer(b"\x00" * 5, NAMES)

    def test_empty_result(self) -> None:
        """Zero counts in all segments."""
        header = struct.pack("<HHH", 0, 0, 0)
        result = parse_extraction_buffer(header, NAMES)
        assert result.values == {}
        assert result.errors == {}
        assert result.absent == ()

    def test_fraction_exact_roundtrip(self) -> None:
        """Extraction preserves exact rationals (no float quantization)."""
        from fractions import Fraction

        header = struct.pack("<HHH", 1, 0, 0)
        # 1/3 is not representable as IEEE 754 double
        values = struct.pack("<Hqq", 0, 1, 3)
        result = parse_extraction_buffer(header + values, NAMES)
        assert result.values["Speed"] == Fraction(1, 3)
        # Verify it's an exact Fraction, not a float approximation
        assert isinstance(result.values["Speed"], Fraction)
        assert result.values["Speed"].numerator == 1
        assert result.values["Speed"].denominator == 3


class TestExtractionErrorCodeSync:
    """Guard the Python enum against Agda drift.

    ``ExtractionErrorCode`` mirrors ``Aletheia.CAN.BatchExtraction.
    ExtractionErrorCode``.  The Agda source is the authoritative
    manifest; this test reads the constructor order directly from
    ``src/Aletheia/CAN/BatchExtraction.agda`` so that adding, removing,
    or reordering an Agda constructor breaks this test instead of
    silently shifting a wire code to a stale message in production.
    """

    def _agda_constructors(self) -> list[str]:
        """Parse the Agda source for ``ExtractionErrorCode`` constructors."""
        from pathlib import Path
        agda = (
            Path(__file__).resolve().parents[2]
            / "src" / "Aletheia" / "CAN" / "BatchExtraction.agda"
        )
        if not agda.exists():
            pytest.fail(
                f"Agda source required for enum drift test but not at {agda}"
            )
        lines = agda.read_text(encoding="utf-8").splitlines()
        # Find the data block; constructors follow with 2-space indent until
        # a non-indented line or blank line is reached.
        try:
            start = next(
                i for i, line in enumerate(lines)
                if line.startswith("data ExtractionErrorCode")
            )
        except StopIteration:
            pytest.fail("``data ExtractionErrorCode`` block not found in Agda source")
        ctors: list[str] = []
        for line in lines[start + 1:]:
            stripped = line.strip()
            if not stripped or not line.startswith(" "):
                break
            # Constructor lines look like ``Name : ExtractionErrorCode ...``
            head = stripped.split(":", 1)[0].strip()
            if head:
                ctors.append(head)
        return ctors

    def test_enum_matches_agda_constructor_order(self) -> None:
        """Enum values match ``extractionErrorCodeToℕ`` in Agda."""
        # Agda → Python name mapping: both are stable by design; adding a
        # new Agda constructor forces a parallel addition here AND in the
        # Go/C++ bindings (see AGENTS.md cross-binding parity rule).
        expected_name_for_code = {
            "NotInDBC": "NOT_IN_DBC",
            "OutOfBounds": "OUT_OF_BOUNDS",
            "ExtractionFailed": "EXTRACTION_FAILED",
        }
        agda_ctors = self._agda_constructors()
        assert agda_ctors, "no constructors parsed from Agda source"
        assert len(agda_ctors) == len(ExtractionErrorCode), (
            f"Agda has {len(agda_ctors)} constructors, Python enum has "
            f"{len(ExtractionErrorCode)} — update Python to match"
        )
        for i, agda_name in enumerate(agda_ctors):
            py_name = expected_name_for_code.get(agda_name)
            assert py_name is not None, (
                f"Agda constructor {agda_name!r} has no Python mirror; "
                f"add it to ExtractionErrorCode"
            )
            py_member = ExtractionErrorCode[py_name]
            assert py_member.value == i, (
                f"{agda_name} is Agda constructor #{i} but Python "
                f"{py_name} = {py_member.value}"
            )

    def test_messages_cover_every_code(self) -> None:
        """Every enum member has a message — no ``KeyError`` at runtime."""
        for code in ExtractionErrorCode:
            assert code in EXTRACTION_ERROR_MESSAGES_BY_CODE
            assert EXTRACTION_ERROR_MESSAGES_BY_CODE[code]
        # Legacy positional tuple is derived from the dict — guard it too.
        assert len(EXTRACTION_ERROR_MESSAGES) == len(ExtractionErrorCode)
