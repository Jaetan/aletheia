"""Tests for utility types, DLC conversion, rational parsing, and condition sets."""

import pytest

from aletheia.client._helpers import float_to_rational, parse_rational
from aletheia.client._types import (
    ProcessError, ProtocolError, bytes_to_dlc, dlc_to_bytes, validate_can_id,
)
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
    """Tests for parse_rational helper function."""

    def test_int_value(self) -> None:
        assert parse_rational(42) == 42.0

    def test_float_value(self) -> None:
        assert parse_rational(3.14) == pytest.approx(3.14)

    def test_rational_string(self) -> None:
        assert parse_rational("3/4") == pytest.approx(0.75)

    def test_rational_string_negative(self) -> None:
        assert parse_rational("-1/2") == pytest.approx(-0.5)

    def test_numeric_string(self) -> None:
        assert parse_rational("2.5") == pytest.approx(2.5)

    def test_rational_dict(self) -> None:
        assert parse_rational(
            {"numerator": 1, "denominator": 3}
        ) == pytest.approx(1 / 3)

    def test_division_by_zero_string_raises(self) -> None:
        with pytest.raises(ProtocolError, match="Division by zero"):
            parse_rational("1/0")

    def test_invalid_type_raises(self) -> None:
        with pytest.raises(ProtocolError, match="Expected signal value"):
            parse_rational([1, 2])


# ============================================================================
# T-7: float_to_rational binary FFI conversion
# ============================================================================

class TestFloatToRational:
    """Tests for float_to_rational 10^9 scaling."""

    def test_integer_value(self) -> None:
        n, d = float_to_rational(42.0)
        assert n == 42_000_000_000
        assert d == 1_000_000_000

    def test_fractional_value(self) -> None:
        n, d = float_to_rational(3.14)
        assert n == 3_140_000_000
        assert d == 1_000_000_000
        assert n / d == pytest.approx(3.14)

    def test_zero(self) -> None:
        n, d = float_to_rational(0.0)
        assert n == 0
        assert d == 1_000_000_000

    def test_negative(self) -> None:
        n, d = float_to_rational(-1.5)
        assert n == -1_500_000_000
        assert d == 1_000_000_000

    def test_small_value(self) -> None:
        n, d = float_to_rational(0.001)
        assert n == 1_000_000
        assert d == 1_000_000_000
        assert n / d == pytest.approx(0.001)

    def test_roundtrip_precision(self) -> None:
        """Values round-trip through float_to_rational with 9 decimal places."""
        for value in [0.0, 1.0, -1.0, 0.123456789, 220.0, 0.01, 65535.0]:
            n, d = float_to_rational(value)
            assert n / d == pytest.approx(value, abs=1e-9)


# ============================================================================
# T-8: Signal index cache integration
# ============================================================================

class TestSignalIndexCache:
    """Tests for signal index cache populated by parse_dbc."""

    def test_cache_populated_on_parse_dbc(self) -> None:
        """parse_dbc populates the signal index cache."""
        from aletheia import AletheiaClient
        with AletheiaClient() as client:
            dbc = {
                "version": "1.0",
                "messages": [{
                    "id": 256, "name": "Msg", "dlc": 8, "sender": "ECU",
                    "signals": [
                        {"name": "Sig0", "startBit": 0, "length": 8,
                         "byteOrder": "little_endian", "signed": False,
                         "factor": 1.0, "offset": 0.0,
                         "minimum": 0.0, "maximum": 255.0,
                         "unit": "", "presence": "always"},
                        {"name": "Sig1", "startBit": 8, "length": 8,
                         "byteOrder": "little_endian", "signed": False,
                         "factor": 1.0, "offset": 0.0,
                         "minimum": 0.0, "maximum": 255.0,
                         "unit": "", "presence": "always"},
                    ],
                }],
            }
            client.parse_dbc(dbc)
            # Cache keyed by (can_id, extended)
            assert (256, False) in client._signal_lookup
            idx_map = client._signal_lookup[(256, False)].indices
            assert idx_map["Sig0"] == 0
            assert idx_map["Sig1"] == 1

    def test_cache_cleared_on_new_dbc(self) -> None:
        """parse_dbc clears previous cache entries."""
        from aletheia import AletheiaClient
        with AletheiaClient() as client:
            dbc1 = {
                "version": "1.0",
                "messages": [{
                    "id": 256, "name": "Msg1", "dlc": 8, "sender": "ECU",
                    "signals": [
                        {"name": "OldSig", "startBit": 0, "length": 8,
                         "byteOrder": "little_endian", "signed": False,
                         "factor": 1.0, "offset": 0.0,
                         "minimum": 0.0, "maximum": 255.0,
                         "unit": "", "presence": "always"},
                    ],
                }],
            }
            client.parse_dbc(dbc1)
            assert "OldSig" in client._signal_lookup[(256, False)].indices

            dbc2 = {
                "version": "1.0",
                "messages": [{
                    "id": 512, "name": "Msg2", "dlc": 8, "sender": "ECU",
                    "signals": [
                        {"name": "NewSig", "startBit": 0, "length": 8,
                         "byteOrder": "little_endian", "signed": False,
                         "factor": 1.0, "offset": 0.0,
                         "minimum": 0.0, "maximum": 255.0,
                         "unit": "", "presence": "always"},
                    ],
                }],
            }
            client.parse_dbc(dbc2)
            assert (256, False) not in client._signal_lookup
            assert (512, False) in client._signal_lookup

    def test_build_frame_without_dbc_raises(self) -> None:
        """build_frame before parse_dbc raises with 'DBC not loaded'."""
        from aletheia import AletheiaClient
        with AletheiaClient() as client:
            with pytest.raises(ProcessError, match="DBC not loaded"):
                client.build_frame(can_id=256, dlc=8, signals={"Sig": 1.0})

    def test_build_frame_unknown_signal_raises(self) -> None:
        """build_frame with unknown signal name raises."""
        from aletheia import AletheiaClient
        with AletheiaClient() as client:
            dbc = {
                "version": "1.0",
                "messages": [{
                    "id": 256, "name": "Msg", "dlc": 8, "sender": "ECU",
                    "signals": [
                        {"name": "RealSig", "startBit": 0, "length": 8,
                         "byteOrder": "little_endian", "signed": False,
                         "factor": 1.0, "offset": 0.0,
                         "minimum": 0.0, "maximum": 255.0,
                         "unit": "", "presence": "always"},
                    ],
                }],
            }
            client.parse_dbc(dbc)
            with pytest.raises(ProcessError, match="unknown signal"):
                client.build_frame(can_id=256, dlc=8, signals={"NoSuchSig": 1.0})

    def test_dlc_payload_mismatch_extract(self) -> None:
        """extract_signals rejects payload/DLC size mismatch."""
        from aletheia import AletheiaClient
        with AletheiaClient() as client:
            dbc = {
                "version": "1.0",
                "messages": [{
                    "id": 256, "name": "Msg", "dlc": 8, "sender": "ECU",
                    "signals": [
                        {"name": "Sig", "startBit": 0, "length": 8,
                         "byteOrder": "little_endian", "signed": False,
                         "factor": 1.0, "offset": 0.0,
                         "minimum": 0.0, "maximum": 255.0,
                         "unit": "", "presence": "always"},
                    ],
                }],
            }
            client.parse_dbc(dbc)
            with pytest.raises(ProcessError, match="payload length .* does not match DLC"):
                client.extract_signals(can_id=256, dlc=8, data=bytearray(7))


# ============================================================================
# T-9: validate_can_id boundary conditions
# ============================================================================

class TestValidateCanId:
    """Boundary tests for validate_can_id."""

    def test_standard_zero(self) -> None:
        validate_can_id(0, extended=False)

    def test_standard_max(self) -> None:
        validate_can_id(0x7FF, extended=False)

    def test_standard_over_max_raises(self) -> None:
        with pytest.raises(ValueError, match="standard CAN ID"):
            validate_can_id(0x800, extended=False)

    def test_standard_negative_raises(self) -> None:
        with pytest.raises(ValueError, match="standard CAN ID"):
            validate_can_id(-1, extended=False)

    def test_extended_zero(self) -> None:
        validate_can_id(0, extended=True)

    def test_extended_max(self) -> None:
        validate_can_id(0x1FFFFFFF, extended=True)

    def test_extended_over_max_raises(self) -> None:
        with pytest.raises(ValueError, match="extended CAN ID"):
            validate_can_id(0x20000000, extended=True)

    def test_extended_negative_raises(self) -> None:
        with pytest.raises(ValueError, match="extended CAN ID"):
            validate_can_id(-1, extended=True)
