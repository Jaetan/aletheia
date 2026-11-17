# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The rationals the binding sends are laid out as ``struct aletheia_rational``'s fields.

``wire_rational`` and ``wire_rationals`` pack each rational as bytes; these
tests read the packed structures back through their ctypes fields, so a row
written in another order, width or sign reads as a different number here.
"""

import struct
from fractions import Fraction
from typing import NamedTuple, NewType

import pytest

from aletheia.client._ffi import AletheiaRational, Word, wire_rational, wire_rationals

# A rational's sign byte: 1 when it is negative, 0 otherwise.
SignByte = NewType("SignByte", int)

_WORD = 2**64

# Zero, both 128-bit bounds, values on either side of a word, and a negative
# value whose denominator fills its low word.
_EDGES = (
    Fraction(0),
    Fraction(2**128 - 1),
    Fraction(-(2**128 - 1), 2**128 - 1),
    Fraction(2**64, 3),
    Fraction(-(2**64 - 1)),
    Fraction(-1, 2**64 - 1),
    Fraction(7, 2**64 + 1),
)


class _Row(NamedTuple):
    """Every field of one ``struct aletheia_rational``, words low first."""

    numerator_lo: Word
    numerator_hi: Word
    denominator_lo: Word
    denominator_hi: Word
    negative: SignByte


def _fields(row: AletheiaRational) -> _Row:
    return _Row(
        row.numerator.lo, row.numerator.hi, row.denominator.lo, row.denominator.hi, row.negative
    )


def _expected(value: Fraction) -> _Row:
    num_hi, num_lo = divmod(abs(value.numerator), _WORD)
    den_hi, den_lo = divmod(value.denominator, _WORD)
    return _Row(
        Word(num_lo), Word(num_hi), Word(den_lo), Word(den_hi), SignByte(1 if value < 0 else 0)
    )


@pytest.mark.parametrize("value", _EDGES)
def test_one_rational_reads_back_as_its_magnitudes_and_sign(value: Fraction) -> None:
    """One packed rational holds its numerator's magnitude, its denominator and its sign byte."""
    assert _fields(wire_rational(value)) == _expected(value)


def test_an_array_holds_each_rational_at_its_place() -> None:
    """Every rational of an array reads back at its own index, in the order given."""
    rows = wire_rationals(_EDGES)
    assert len(rows) == len(_EDGES)
    assert [_fields(row) for row in rows] == [_expected(value) for value in _EDGES]


def test_an_empty_array_holds_no_rational() -> None:
    """No values make an array of no rationals."""
    assert len(wire_rationals(())) == 0


@pytest.mark.parametrize("value", [Fraction(2**128), Fraction(-(2**128)), Fraction(1, 2**128)])
def test_a_component_past_128_bits_is_refused(value: Fraction) -> None:
    """A component of ``2**128`` or more is refused, never truncated to its low words."""
    with pytest.raises(struct.error):
        _ = wire_rational(value)
