"""Tests for binary extraction buffer parsing (_client_bin.py)."""

from __future__ import annotations

import struct

import pytest

from aletheia.client._client_bin import (
    EXTRACTION_ERROR_MESSAGES,
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

    def test_denominator_zero(self) -> None:
        """Denominator zero yields 0.0 (no crash)."""
        header = struct.pack("<HHH", 1, 0, 0)
        values = struct.pack("<Hqq", 0, 999, 0)
        result = parse_extraction_buffer(header + values, NAMES)
        assert result.values == {"Speed": 0.0}

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
