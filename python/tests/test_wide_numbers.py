# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Real-FFI tests for the numbers the kernel carries past 64 bits.

Each number kind has its own bound, decided by the kernel when it reads the
number: a rational's numerator magnitude and denominator at most 2^128-1, a
multiplex value at most 2^128-1, a value-description key signed with magnitude
at most 2^128-1, and a time bound at most 2^64-1 microseconds.  A refusal past
a bound whose measured value passes the reported ceiling names no number.
"""

from fractions import Fraction
from typing import NewType

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, Signal
from aletheia.client._types import InputBoundExceededError
from aletheia.types import DLCCode

# The statements of a DBC text after its message header, or a whole DBC text.
DBCText = NewType("DBCText", str)

_LIMIT = 2**128 - 1
_U64_MAX = 2**64 - 1
_WIRE_RANGE_MESSAGE = f"extracted value's numerator or denominator magnitude exceeds {_LIMIT}"

# The factor opendbc's vw_mlb.dbc gives OBD_Abs_Load_Val: 100/255 printed to
# 17 places, so a value's reduced numerator passes 64 bits on most raw values.
_VW_MLB_FACTOR = Fraction(39215686274509803, 10**17)


def _dbc_text(body: DBCText) -> DBCText:
    """Return a one-message, 8-byte DBC text carrying the given SG_ and VAL_ lines."""
    return DBCText('VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n' + body)


class TestRationalReach:
    """A rational's components reach 2^128-1 on every route."""

    def test_a_64_bit_raw_value_extracts_exactly(self) -> None:
        """A 64-bit signal declaring its full range reads its largest raw value exactly."""
        big = signal("Big", length=64, maximum=_U64_MAX)
        with AletheiaClient() as client:
            assert client.parse_dbc(dbc([message(0x100, "Msg", [big])]))["status"] == "success"
            result = client.extract_signals(
                can_id=0x100, dlc=DLCCode(8), data=bytearray(b"\xff" * 8)
            )
        assert dict(result.values) == {"Big": Fraction(_U64_MAX)}, dict(result.values)
        assert not result.errors

    def test_a_frame_is_built_from_a_64_bit_value(self) -> None:
        """Building a frame from the largest value a 64-bit signal carries sets every bit."""
        big = signal("Big", length=64, maximum=_U64_MAX)
        with AletheiaClient() as client:
            assert client.parse_dbc(dbc([message(0x100, "Msg", [big])]))["status"] == "success"
            frame = client.build_frame(0x100, DLCCode(8), {"Big": _U64_MAX})
        assert bytes(frame) == b"\xff" * 8

    def test_a_17_place_factor_extracts_exactly(self) -> None:
        """vw_mlb's factor on 16 bits loads and reads its raw values exactly."""
        maximum = _VW_MLB_FACTOR * 0xFFFF
        load = signal("Load", length=16, factor=_VW_MLB_FACTOR, maximum=maximum)
        raws = [0, 1, 255, 470, 471, 4097, 0xFFFE, 0xFFFF]
        with AletheiaClient() as client:
            assert client.parse_dbc(dbc([message(0x100, "Msg", [load])]))["status"] == "success"
            for raw in raws:
                data = bytearray(raw.to_bytes(2, "little") + bytes(6))
                result = client.extract_signals(can_id=0x100, dlc=DLCCode(8), data=data)
                assert dict(result.values) == {"Load": _VW_MLB_FACTOR * raw}, raw
                assert not result.errors, raw

    def test_a_value_past_the_bound_is_refused_with_the_bound_named(self) -> None:
        """A 132-bit CAN-FD value within its declared range whose numerator passes the bound."""
        raw = _LIMIT * 10 - 1
        assert Fraction(raw, 10).numerator > _LIMIT
        wide = signal("Wide", length=132, factor=Fraction(1, 10), maximum=_LIMIT)
        with AletheiaClient() as client:
            parsed = client.parse_dbc(dbc([message(0x300, "Fd", [wide], dlc=64)]))
            assert parsed["status"] == "success", parsed
            result = client.extract_signals(
                can_id=0x300, dlc=DLCCode(15), data=bytearray(raw.to_bytes(64, "little"))
            )
        assert dict(result.errors) == {"Wide": _WIRE_RANGE_MESSAGE}, dict(result.errors)
        assert not result.values

    def test_a_number_past_the_bound_is_refused_naming_no_number(self) -> None:
        """2^128 as a signal maximum: the saturated refusal names only the limit."""
        text = _dbc_text(DBCText(f' SG_ S : 0|8@1+ (1,0) [0|{2**128}] "" ECU\n'))
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as refused:
            client.parse_dbc_text(text)
        assert str(refused.value) == (
            f"ParseDBCText: signal maximum: rational component magnitude exceeds limit {_LIMIT}"
        )
        assert refused.value.observed == _LIMIT
        assert refused.value.limit == _LIMIT

    def test_a_fraction_of_65_significant_digits_that_fits_loads(self) -> None:
        """0.<the 65 digits of 5^92> is 5^27 / 2^65, within the bound, and reads exactly."""
        factor = "0." + str(5**92)
        text = _dbc_text(DBCText(f' SG_ S : 0|8@1+ ({factor},0) [0|1] "" ECU\n'))
        with AletheiaClient() as client:
            parsed = client.parse_dbc_text(text)
        assert parsed["status"] == "success", parsed
        assert parsed["dbc"]["messages"][0]["signals"][0]["factor"] == Fraction(5**27, 2**65)


class TestIntegerFieldReach:
    """Multiplex values and value-description keys reach their own bounds."""

    def test_a_multiplex_value_past_32_bits_loads_and_reads_back(self) -> None:
        """m4294967296 on a 40-bit multiplexor loads, and the client reads the DBC back."""
        text = _dbc_text(
            DBCText(
                f' SG_ Mx M : 0|40@1+ (1,0) [0|{2**40 - 1}] "" ECU\n'
                + ' SG_ A m4294967296 : 40|8@1+ (1,0) [0|255] "" ECU\n'
            )
        )
        with AletheiaClient() as client:
            parsed = client.parse_dbc_text(text)
        assert parsed["status"] == "success", parsed
        selected = parsed["dbc"]["messages"][0]["signals"][1]
        assert "multiplex_values" in selected, selected
        assert selected["multiplex_values"] == [2**32], selected

    def test_a_negative_value_description_key_loads(self) -> None:
        """Tesla's "SNA" at a signed signal's most negative raw value loads."""
        text = _dbc_text(
            DBCText(
                ' SG_ Rpm : 0|16@1- (1,0) [-32768|32767] "" ECU\n\n'
                + 'VAL_ 256 Rpm -32768 "SNA" 0 "Stopped" ;\n'
            )
        )
        with AletheiaClient() as client:
            parsed = client.parse_dbc_text(text)
        assert parsed["status"] == "success", parsed
        rpm = parsed["dbc"]["messages"][0]["signals"][0]
        assert "valueDescriptions" in rpm, rpm
        entries = rpm["valueDescriptions"]
        assert {"value": -32768, "description": "SNA"} in entries, entries


class TestTimeBound:
    """A time bound is microseconds, decided by the kernel against 2^64-1."""

    def test_a_time_window_is_written_in_microseconds(self) -> None:
        """Within takes microseconds: the timebound sent is the argument itself."""
        formula = Signal("S").less_than(10).within(1500).to_dict()
        assert formula["operator"] == "metricEventually", formula
        assert formula["timebound"] == 1500, formula

    def test_a_negative_time_bound_is_refused_by_the_kernel(self) -> None:
        """The client builds the property; the kernel refuses it, saying why."""
        text = _dbc_text(DBCText(' SG_ S : 0|8@1+ (1,0) [0|255] "" ECU\n'))
        prop = Signal("S").less_than(10).within(-1).to_dict()
        with AletheiaClient() as client:
            assert client.parse_dbc_text(text)["status"] == "success"
            reply = client.set_properties([prop])
        assert reply["status"] == "error", reply
        assert reply["code"] == "handler_property_parse_failed", reply
        assert reply["message"] == "SetProperties: property 0: timebound -1 is negative", reply

    def test_a_time_bound_past_the_timestamp_range_is_refused(self) -> None:
        """2^64 microseconds is past every timestamp: refused with the time bound's own limit."""
        text = _dbc_text(DBCText(' SG_ S : 0|8@1+ (1,0) [0|255] "" ECU\n'))
        prop = Signal("S").less_than(10).within(2**64).to_dict()
        with AletheiaClient() as client:
            assert client.parse_dbc_text(text)["status"] == "success"
            reply = client.set_properties([prop])
        assert reply["status"] == "error", reply
        assert reply["code"] == "input_bound_exceeded", reply
        assert reply.get("limit") == _U64_MAX, reply
        assert reply.get("observed") == 2**64, reply
        assert "time bound" in reply["message"], reply
