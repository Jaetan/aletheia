# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hypothesis-driven property tests.

Counterpart of go/aletheia/property_test.go and
cpp/tests/unit_tests_property.cpp: properties of the wire-format encoders,
decoders and checks the Python binding owns, over every input a run draws.

The tests draw under the profiles ``_hypothesis_profiles.py`` registers, and
every run draws the same sample in every profile and lane: each test is seeded
with the seed every binding's property tests share (``fixtures/property_seed``).
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import TYPE_CHECKING, NewType, cast

import pytest
from _canonical_dbc import CANONICAL_SIGNAL
from _hypothesis_profiles import DEFAULT_PROFILE
from hypothesis import given, seed, settings
from hypothesis import strategies as st

from aletheia import ProtocolError, ValidationError
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.client._ffi import KernelResponse, parse_json_object
from aletheia.client._helpers.json_codec import parse_values_list
from aletheia.client._helpers.rational import decode_wire_rational
from aletheia.client._types import validate_can_id
from aletheia.types import (
    ByteOrder,
    DBCDefinition,
    DBCMessage,
    DBCSignal,
    DBCSignalAlways,
    DLCByteCount,
    dump_json,
)

if TYPE_CHECKING:
    from _hypothesis_profiles import ProfileName

# The seed every binding's property tests draw their sample from.
PropertySeed = NewType("PropertySeed", int)
PROPERTY_SEED = PropertySeed(
    int((Path(__file__).parent / "fixtures" / "property_seed").read_text(encoding="utf-8"))
)
# The largest identifier each kind of CAN ID carries, keyed by whether it is
# extended: 11 bits for a standard identifier, 29 for an extended one.
_LARGEST_CAN_ID = {False: 0x7FF, True: 0x1FFFFFFF}
# Printable ASCII, the shape a wire error takes.
_PRINTABLE = st.characters(min_codepoint=32, max_codepoint=126)
# JSON values of every shape, as a response spells them.
_JSON_VALUES = st.recursive(
    st.none() | st.booleans() | st.integers() | st.text(_PRINTABLE),
    lambda children: st.lists(children) | st.dictionaries(st.text(_PRINTABLE), children),
)


# -----------------------------------------------------------------------------
# Strategies
# -----------------------------------------------------------------------------


@st.composite
def signal_name_strategy(draw: st.DrawFn) -> str:
    """Generate identifier-shaped strings (DBC signal naming rules).

    The first character is a lower-case letter or an underscore, so no draw is
    a DBC keyword, which the kernel refuses as a name: every keyword starts
    with an upper-case letter.
    """
    first = draw(st.sampled_from("abcdefghijklmnopqrstuvwxyz_"))
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
@given(payload=st.text(_PRINTABLE) | _JSON_VALUES.map(json.dumps))
def test_response_reader_answers_an_object_or_a_protocol_error(payload: str) -> None:
    """``parse_json_object`` returns the object a payload spells, else ``ProtocolError``.

    Counterpart of Go's ``TestProperty_ParseResponseTotal``: the reader every
    kernel response goes through lets no other exception escape on a printable
    payload a run draws, whether arbitrary text or a JSON value of any shape.
    """
    response = KernelResponse(payload.encode("utf-8"))
    try:
        spells_an_object = isinstance(json.loads(payload), dict)
    except json.JSONDecodeError:
        spells_an_object = False
    if spells_an_object:
        assert parse_json_object(response) == json.loads(payload)
    else:
        with pytest.raises(ProtocolError):
            parse_json_object(response)


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
@given(extended=st.booleans(), data=st.data())
def test_can_id_check_accepts_every_identifier_its_kind_carries(
    *,
    extended: bool,
    data: st.DataObject,
) -> None:
    """``validate_can_id`` accepts every identifier from 0 to its kind's largest.

    Counterpart of the C++ standard CAN ID factory's acceptance property, for
    both kinds of identifier.
    """
    can_id = data.draw(st.integers(min_value=0, max_value=_LARGEST_CAN_ID[extended]))
    validate_can_id(can_id, extended=extended)


@seed(PROPERTY_SEED)
@given(extended=st.booleans(), data=st.data())
def test_can_id_check_refuses_every_identifier_its_kind_does_not_carry(
    *,
    extended: bool,
    data: st.DataObject,
) -> None:
    """``validate_can_id`` refuses a negative identifier and one past its kind's largest.

    Counterpart of the C++ standard CAN ID factory's refusal property, for
    both kinds of identifier.
    """
    largest = _LARGEST_CAN_ID[extended]
    can_id = data.draw(st.integers(max_value=-1) | st.integers(min_value=largest + 1))
    with pytest.raises(ValidationError):
        validate_can_id(can_id, extended=extended)


# The profile the tests above draw under: ``@given`` keeps the profile in force
# when it decorates, so this is read after the last of them.  The plugin's
# ``--hypothesis-verbosity`` and ``--hypothesis-explain`` load a copy of the
# selected profile named after it with a ``-with-`` suffix.
_DECORATED_PROFILE, _, _ = settings.get_current_profile_name().partition("-with-")


def test_property_tests_draw_the_profile_the_run_selected(request: pytest.FixtureRequest) -> None:
    """The tests above draw under what ``--hypothesis-profile`` selects, the default without it."""
    selected = cast("ProfileName | None", request.config.getoption("--hypothesis-profile"))
    assert (selected or DEFAULT_PROFILE) == _DECORATED_PROFILE
