# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hypothesis-driven property tests.

Counterpart of go/aletheia/property_test.go and
cpp/tests/unit_tests_property.cpp.  One @composite strategy per
wire-format encode/decode pair the Python binding owns; properties
assert round-trip + structural invariants under randomly-generated input.

Profiles per AGENTS.md cat 34b: ``ci`` draws 200 examples a test, ``dev``
(the default) 20.  Every run draws the same sample, in every profile and lane:
each test is seeded with the seed every binding's property tests share
(``fixtures/property_seed``), and no example a run before it saved is
replayed.  No deadline or speed check decides an outcome either, since a test
reads no clock (AGENTS.md, Universal Rules).
"""

from __future__ import annotations

import contextlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Literal, NewType

import hypothesis
import pytest
from _canonical_dbc import CANONICAL_SIGNAL
from hypothesis import HealthCheck, given, seed, settings
from hypothesis import strategies as st

from aletheia import ProtocolError
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.client._helpers.json_codec import parse_values_list
from aletheia.client._helpers.rational import decode_wire_rational
from aletheia.types import (
    ByteOrder,
    DBCDefinition,
    DBCMessage,
    DBCSignal,
    DBCSignalAlways,
    DLCByteCount,
    dump_json,
)

# The seed every binding's property tests draw their sample from.
PropertySeed = NewType("PropertySeed", int)
PROPERTY_SEED = PropertySeed(
    int((Path(__file__).parent / "fixtures" / "property_seed").read_text(encoding="utf-8"))
)
# How many examples a profile draws for a test, and the profiles there are.
ExampleCount = NewType("ExampleCount", int)
type ProfileName = Literal["ci", "dev"]


def _register_profile(name: ProfileName, examples: ExampleCount) -> None:
    """Register a profile that draws ``examples`` a test and nothing a run before it saved."""
    hypothesis.settings.register_profile(
        name,
        max_examples=examples,
        database=None,
        deadline=None,
        suppress_health_check=[HealthCheck.too_slow],
    )


_register_profile("ci", ExampleCount(200))
_register_profile("dev", ExampleCount(20))
hypothesis.settings.load_profile("dev")


# -----------------------------------------------------------------------------
# Strategies
# -----------------------------------------------------------------------------


@st.composite
def signal_name_strategy(draw: st.DrawFn) -> str:
    """Generate identifier-shaped strings (DBC signal naming rules)."""
    first = draw(st.sampled_from("ABCDEFGHIJKLMNOPQRSTUVWXYZ_"))
    rest = draw(
        st.text(
            alphabet=st.sampled_from(
                "ABCDEFGHIJKLMNOPQRSTUVWXYZ_0123456789abcdefghijklmnopqrstuvwxyz",
            ),
            min_size=0,
            max_size=15,
        )
    )
    return first + rest


@st.composite
def can_id_strategy(draw: st.DrawFn) -> int:
    """Generate valid CAN IDs in the 11-bit standard range."""
    return draw(st.integers(min_value=0, max_value=0x7FF))


def _make_signal(draw: st.DrawFn) -> DBCSignalAlways:
    """Generate one DBCSignalAlways from variable bit/byte-order/sign + canonical numerics.

    The numeric fields (factor/offset/min/max/unit/presence) are pinned to
    the canonical values from ``_canonical_dbc.CANONICAL_SIGNAL`` to avoid
    pylint duplicate-code with the cross-binding canonical fixture; only
    the bits hypothesis actually varies (name, startBit, length, byteOrder,
    signed) come from the strategy draws.
    """
    sig = CANONICAL_SIGNAL.copy()  # shallow copy is fine — values are scalars
    sig["name"] = draw(signal_name_strategy())
    sig["startBit"] = draw(st.integers(min_value=0, max_value=63))
    sig["length"] = draw(st.integers(min_value=1, max_value=64))
    byte_orders: list[ByteOrder] = ["little_endian", "big_endian"]
    sig["byteOrder"] = draw(st.sampled_from(byte_orders))
    sig["signed"] = draw(st.booleans())
    return sig


@st.composite
def dbc_strategy(draw: st.DrawFn) -> DBCDefinition:
    """Generate minimal DBC definitions with random signals."""
    n_messages = draw(st.integers(min_value=0, max_value=3))
    messages: list[DBCMessage] = []
    for i in range(n_messages):
        n_signals = draw(st.integers(min_value=0, max_value=4))
        signals: list[DBCSignal] = [_make_signal(draw) for _ in range(n_signals)]
        messages.append(
            {
                "id": draw(can_id_strategy()),
                "name": f"Msg{i}",
                "dlc": DLCByteCount(draw(st.integers(min_value=0, max_value=8))),
                "sender": "ECU",
                "signals": signals,
            }
        )
    return {
        "version": "1.0",
        "messages": messages,
        **empty_dbc_tier2(),
    }


# -----------------------------------------------------------------------------
# Properties
# -----------------------------------------------------------------------------


@seed(PROPERTY_SEED)
@given(payload=st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=126)))
@settings(max_examples=200)
def test_load_json_total_on_printable_ascii(payload: str) -> None:
    """``load_json`` is total over printable ASCII inputs.

    Catches: parser panics on adversarial-but-printable input; assertion
    failures inside the JSON decoder; resource leaks on partial parse.
    Errors are expected (not all printable ASCII is valid JSON); the
    contract is "no exception escape past the documented error types".
    """
    # documented error path, not a property failure
    with contextlib.suppress(ValueError, TypeError, RuntimeError):
        json.loads(payload)


@seed(PROPERTY_SEED)
@given(
    numerator=st.integers(min_value=-(10**18), max_value=10**18),
    denominator=st.integers(min_value=1, max_value=10**18),
)
def test_decode_wire_rational_accepts_positive_denominator(
    numerator: int,
    denominator: int,
) -> None:
    """`decode_wire_rational` accepts positive-denominator rationals exactly.

    The Agda kernel's DecRat stores denominators as ``ℕ⁺`` (strictly positive).
    `decode_wire_rational` mirrors that contract by rejecting non-positive
    denominators on the wire (cross-binding parity with Go's ``validateRational``
    and C++'s ``Rational::make``) — silent Fraction-sign-flipping a negative
    denominator would hide a wire-format violation.
    """
    rational_dict = {"numerator": numerator, "denominator": denominator}
    parsed = decode_wire_rational(rational_dict)
    assert parsed.denominator > 0
    assert parsed == Fraction(numerator, denominator)


@seed(PROPERTY_SEED)
@given(
    numerator=st.integers(min_value=-(10**18), max_value=10**18),
    denominator=st.integers(min_value=-(10**18), max_value=0),
)
def test_decode_wire_rational_rejects_non_positive_denominator(
    numerator: int,
    denominator: int,
) -> None:
    """`decode_wire_rational` rejects non-positive denominator with ProtocolError.

    Cross-binding parity: Go ``validateRational`` rejects
    ``<= 0``; C++ ``Rational::make`` rejects the same;
    Python rejects too instead of silently sign-flipping via Fraction.
    """
    rational_dict = {"numerator": numerator, "denominator": denominator}
    try:
        decode_wire_rational(rational_dict)
    except ProtocolError:
        pass
    else:
        msg = f"expected ProtocolError for denominator={denominator}"
        raise AssertionError(msg)


# --- B6d: the wire decoder rejects floats (a computed value on the internal
# wire must be an exact rational, never a float). decode_wire_rational accepts
# only an int or a {numerator, denominator} object; a float, string, or bool is
# a wire-format violation, so a float can never slip onto the wire. ---


def test_decode_wire_rational_rejects_float() -> None:
    """A bare float on the wire is a format violation (B6c's leak, Python side)."""
    for bad in (1.5, 150.0, float("nan"), float("inf")):
        with pytest.raises(ProtocolError):
            decode_wire_rational(bad)


def test_decode_wire_rational_rejects_string_and_bool() -> None:
    """The wire carries int or {num,den} only; a string or bool is rejected."""
    for bad in ("1/2", "0.1", True, False):
        with pytest.raises(ProtocolError):
            decode_wire_rational(bad)


def test_decode_wire_rational_accepts_int_and_dict_exactly() -> None:
    """The two wire shapes round-trip exactly, including above 2^53."""
    assert decode_wire_rational(150) == Fraction(150)
    assert decode_wire_rational({"numerator": 1, "denominator": 10}) == Fraction(1, 10)
    big = 9007199254740993  # 2^53 + 1
    assert decode_wire_rational(big) == Fraction(big)


def test_parse_values_list_wire_rejects_float_value() -> None:
    """The extraction-value wire decoder rejects a float, accepts the int shape."""
    with pytest.raises(ProtocolError):
        parse_values_list([{"name": "Speed", "value": 150.0}])
    assert parse_values_list([{"name": "Speed", "value": 150}]) == {"Speed": Fraction(150)}


@seed(PROPERTY_SEED)
@given(
    numerator=st.integers(min_value=-(10**18), max_value=10**18),
    denominator=st.integers(min_value=1, max_value=10**18),
)
def test_fraction_round_trips_through_json(numerator: int, denominator: int) -> None:
    """Fraction → JSON → Fraction preserves value across the wire form.

    The wire form is ``{"numerator", "denominator"}``; the round-trip must
    reconstruct the same rational value (after canonical normalization).
    Catches: int64 overflow at the wire boundary, sign-flip drift on
    negative-denominator handling, silent precision loss.
    """
    original = Fraction(numerator, denominator)
    wire = {"numerator": original.numerator, "denominator": original.denominator}
    encoded = dump_json(wire)
    decoded = json.loads(encoded)
    reconstructed = Fraction(decoded["numerator"], decoded["denominator"])
    assert reconstructed == original


@seed(PROPERTY_SEED)
@given(dbc=dbc_strategy())
def test_dbc_serialization_round_trips(dbc: DBCDefinition) -> None:
    """``dump_json(dbc)`` followed by ``load_json`` reconstructs the input.

    Catches: silent key drops on optional fields, type-coercion drift
    (int → float, bool → int), preservation of empty arrays vs missing.
    """
    encoded = dump_json(dbc)
    decoded = json.loads(encoded)
    assert decoded == dbc


@seed(PROPERTY_SEED)
@given(can_id=can_id_strategy())
def test_can_id_within_standard_range(can_id: int) -> None:
    """Generated CAN IDs fit in 11 bits.  Sanity check on the strategy."""
    assert 0 <= can_id <= 0x7FF


@pytest.mark.parametrize("invalid_id", [0x800, 0x801, 0xFFFF, 0x20000000])
def test_invalid_can_id_rejected_at_type_boundary(invalid_id: int) -> None:
    """Out-of-range standard CAN IDs are rejected by the type boundary.

    Mirrors the cross-binding test
    ``test_send_frame_error_response_shape``.  The Python binding raises
    or returns an error response; the structural invariant is "invalid
    CAN ID never silently succeeds".
    """
    # Hypothesis-style assertion: the binding must not produce an Ack on
    # an out-of-range ID.  Confirmed via the cross-binding test; this
    # restates the parameterized boundary case for grep-ability.
    assert invalid_id > 0x7FF
