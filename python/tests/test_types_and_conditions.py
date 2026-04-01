"""Tests for utility types, DLC conversion, rational parsing, and condition sets."""

import pytest

from aletheia.client._client import AletheiaClient
from aletheia.client._types import ProtocolError, bytes_to_dlc, dlc_to_bytes
from aletheia._check_conditions import (
    ALL_SIMPLE_CONDITIONS,
    SIMPLE_VALUE_CONDITIONS,
    SIMPLE_RANGE_CONDITIONS,
    SIMPLE_SETTLES_CONDITIONS,
    SIMPLE_EQUALS_CONDITIONS,
)


# ============================================================================
# T-1: bytes_to_dlc tests
# ============================================================================

class TestBytesToDlc:
    """Tests for bytes_to_dlc reverse mapping."""

    @pytest.mark.parametrize("byte_count", range(9))
    def test_can20_direct_mapping(self, byte_count: int) -> None:
        """CAN 2.0 DLC codes 0-8 map directly from byte counts 0-8."""
        assert bytes_to_dlc(byte_count) == byte_count

    @pytest.mark.parametrize(
        ("byte_count", "expected_dlc"),
        [(12, 9), (16, 10), (20, 11), (24, 12), (32, 13), (48, 14), (64, 15)],
    )
    def test_canfd_byte_counts(self, byte_count: int, expected_dlc: int) -> None:
        """CAN-FD byte counts map to DLC codes 9-15."""
        assert bytes_to_dlc(byte_count) == expected_dlc

    @pytest.mark.parametrize("invalid", [9, 10, 11, 13, 15, 33, 65, 100, 256])
    def test_invalid_byte_count_raises(self, invalid: int) -> None:
        """Invalid byte counts (not in the CAN-FD table) raise ValueError."""
        with pytest.raises(ValueError, match="Invalid byte count"):
            bytes_to_dlc(invalid)

    @pytest.mark.parametrize("dlc_code", range(16))
    def test_roundtrip(self, dlc_code: int) -> None:
        """bytes_to_dlc(dlc_to_bytes(code)) == code for all valid DLC codes."""
        assert bytes_to_dlc(dlc_to_bytes(dlc_code)) == dlc_code


# ============================================================================
# T-6: Condition set identity
# ============================================================================

class TestConditionSets:
    """Verify ALL_SIMPLE_CONDITIONS is the union of component sets."""

    def test_all_simple_is_union(self) -> None:
        """ALL_SIMPLE_CONDITIONS == VALUE | RANGE | SETTLES | EQUALS."""
        expected = (
            SIMPLE_VALUE_CONDITIONS
            | SIMPLE_RANGE_CONDITIONS
            | SIMPLE_SETTLES_CONDITIONS
            | SIMPLE_EQUALS_CONDITIONS
        )
        assert ALL_SIMPLE_CONDITIONS == expected

    def test_component_sets_disjoint(self) -> None:
        """The four component sets are pairwise disjoint."""
        sets = [
            SIMPLE_VALUE_CONDITIONS,
            SIMPLE_RANGE_CONDITIONS,
            SIMPLE_SETTLES_CONDITIONS,
            SIMPLE_EQUALS_CONDITIONS,
        ]
        for i, s1 in enumerate(sets):
            for s2 in sets[i + 1:]:
                assert s1.isdisjoint(s2), f"Overlap: {s1 & s2}"


# ============================================================================
# T-5: _parse_rational string path
# ============================================================================

class TestParseRational:
    """Tests for AletheiaClient._parse_rational static method."""

    def test_int_value(self) -> None:
        assert AletheiaClient._parse_rational(42) == 42.0

    def test_float_value(self) -> None:
        assert AletheiaClient._parse_rational(3.14) == pytest.approx(3.14)

    def test_rational_string(self) -> None:
        assert AletheiaClient._parse_rational("3/4") == pytest.approx(0.75)

    def test_rational_string_negative(self) -> None:
        assert AletheiaClient._parse_rational("-1/2") == pytest.approx(-0.5)

    def test_numeric_string(self) -> None:
        assert AletheiaClient._parse_rational("2.5") == pytest.approx(2.5)

    def test_rational_dict(self) -> None:
        assert AletheiaClient._parse_rational(
            {"numerator": 1, "denominator": 3}
        ) == pytest.approx(1 / 3)

    def test_division_by_zero_string_raises(self) -> None:
        with pytest.raises(ProtocolError, match="Division by zero"):
            AletheiaClient._parse_rational("1/0")

    def test_invalid_type_raises(self) -> None:
        with pytest.raises(ProtocolError, match="Expected signal value"):
            AletheiaClient._parse_rational([1, 2])
