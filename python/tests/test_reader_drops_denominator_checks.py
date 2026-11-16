# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The readers of a kernel rational check its kinds, never its denominator's range.

The kernel proves every denominator it writes positive, in a JSON reply, in the
decimal entry's out-parameter and in the binary extraction buffer, so each reader
takes the parts as written and hands them to ``Fraction``, whose own error a zero
denominator raises.
"""

from __future__ import annotations

import struct
from fractions import Fraction

import pytest

from aletheia.client._client_bin import parse_extraction_buffer
from aletheia.client._ffi import AletheiaDecimal, AletheiaRational, AletheiaUint128
from aletheia.client._helpers.rational import decimal_value
from aletheia.client._helpers.reply_shape import ReplyPath, read_rational

# A rational place of a reply.
_PLACE = ReplyPath("values/value")


def test_read_rational_hands_the_parts_to_fraction() -> None:
    """A rational object's parts reach ``Fraction`` unchecked: a negative denominator signs it."""
    assert read_rational({"numerator": 3, "denominator": -4}, _PLACE) == Fraction(-3, 4)
    with pytest.raises(ZeroDivisionError, match=r"^Fraction\(3, 0\)$"):
        _ = read_rational({"numerator": 3, "denominator": 0}, _PLACE)


def test_decimal_value_hands_the_parts_to_fraction() -> None:
    """The decimal entry's parts reach ``Fraction`` unchecked: a zero denominator is its error."""
    zero = AletheiaRational(
        numerator=AletheiaUint128(lo=1, hi=0), denominator=AletheiaUint128(lo=0, hi=0)
    )
    with pytest.raises(ZeroDivisionError, match=r"^Fraction\(1, 0\)$"):
        _ = decimal_value(AletheiaDecimal(value=zero))


def test_extraction_value_hands_the_parts_to_fraction() -> None:
    """An extraction value's parts reach ``Fraction`` unchecked: a zero denominator is its error."""
    # One value entry (index 0, sign 0, numerator 999, denominator 0), no
    # error, no absent signal, and the offsets table's single 0.
    buf = b"".join(
        (
            struct.pack("<HHHI", 1, 0, 0, 0),
            struct.pack("<HBQQQQ", 0, 0, 999, 0, 0, 0),
            struct.pack("<I", 0),
        )
    )
    with pytest.raises(ZeroDivisionError, match=r"^Fraction\(999, 0\)$"):
        _ = parse_extraction_buffer(buf, ("Speed",))
