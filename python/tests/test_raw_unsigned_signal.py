# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``aletheia._dbc_types.raw_unsigned_signal``, the signal hand-written DBCs share.

The canonical test fixture and the load-scaling benchmark both build their
signals from it, so every field is pinned: a change to one is a change to
what the tests check and what the benchmark measures.  The range spans the
whole raw width, the narrowest and the widest included, and every call
returns its own dict.
"""

from __future__ import annotations

from fractions import Fraction

from aletheia._dbc_types import BitLength, SignalName, raw_unsigned_signal


def test_every_field_is_the_identity_signal_of_its_width() -> None:
    """An unsigned little-endian byte at bit 0, factor 1 and offset 0, from 0 to 255."""
    signal = raw_unsigned_signal(SignalName("S0"), BitLength(8))
    assert set(signal) == {
        "name",
        "startBit",
        "length",
        "byteOrder",
        "signed",
        "factor",
        "offset",
        "minimum",
        "maximum",
        "unit",
        "presence",
    }
    assert (signal["name"], signal["startBit"], signal["length"]) == ("S0", 0, 8)
    assert (signal["byteOrder"], signal["signed"]) == ("little_endian", False)
    assert (signal["factor"], signal["offset"]) == (Fraction(1), Fraction(0))
    assert (signal["minimum"], signal["maximum"]) == (Fraction(0), Fraction(255))
    assert (signal["unit"], signal["presence"]) == ("", "always")


def test_the_range_is_the_whole_raw_width() -> None:
    """One bit reaches 1, sixty-four bits reach 2**64 - 1."""
    assert raw_unsigned_signal(SignalName("Bit"), BitLength(1))["maximum"] == 1
    assert raw_unsigned_signal(SignalName("Wide"), BitLength(64))["maximum"] == 2**64 - 1


def test_each_call_returns_its_own_dict() -> None:
    """A caller that edits its signal leaves the next caller's untouched."""
    first = raw_unsigned_signal(SignalName("S"), BitLength(8))
    first["unit"] = "km/h"
    assert raw_unsigned_signal(SignalName("S"), BitLength(8))["unit"] == ""
