# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The readers of a kernel rational check its kinds, never its denominator's range.

The kernel proves every denominator it writes positive, in a JSON reply, in the
decimal entry's out-parameter and in the binary extraction buffer, so each reader
takes the parts as written: a dict's denominator is returned as it is, and a zero
one reaching ``Fraction`` raises ``Fraction``'s own error.
"""

from __future__ import annotations

import struct
from typing import NewType

import pytest

from aletheia.client._client_bin import parse_extraction_buffer
from aletheia.client._ffi import AletheiaDecimal, AletheiaRational, Magnitude, wire_uint128
from aletheia.client._helpers.rational import decimal_value, extract_rational_from_dict

# A denominator as a reply's rational dict spells it, in or out of the range
# the kernel writes.
WireDenominator = NewType("WireDenominator", int)


@pytest.mark.parametrize(
    "denominator", [WireDenominator(0), WireDenominator(-4)], ids=["zero", "negative"]
)
def test_extract_rational_from_dict_returns_the_denominator_as_written(
    denominator: WireDenominator,
) -> None:
    """A rational dict's denominator is returned as the kernel wrote it, its range unchecked."""
    rational = {"numerator": 3, "denominator": denominator}
    assert extract_rational_from_dict(rational, "rational") == (3, denominator)


def test_decimal_value_hands_the_parts_to_fraction() -> None:
    """The decimal entry's parts reach ``Fraction`` unchecked: a zero denominator is its error."""
    zero = AletheiaRational(
        numerator=wire_uint128(Magnitude(1)), denominator=wire_uint128(Magnitude(0))
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
