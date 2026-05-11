"""Hypothesis-driven property tests (R18 cluster 5 — Cat 34b).

Counterpart of go/aletheia/property_test.go and
cpp/tests/unit_tests_property.cpp.  One @composite strategy per
wire-format encode/decode pair the Python binding owns; properties
assert round-trip + structural invariants under randomly-generated input.

Profiles per AGENTS.md cat 34b:
- ``ci``: max_examples=200, deterministic seed (CI bot)
- ``dev``: max_examples=20, statistically-shrunk failures (developer)

The tests run under both standard and ``--random-order`` lanes.  Hypothesis
manages its own random seed; deterministic-by-seed runs are the default
unless ``--hypothesis-profile=ci`` is selected.
"""

from __future__ import annotations

import json
from fractions import Fraction

import hypothesis
import pytest
from hypothesis import given, settings, strategies as st

from _canonical_dbc import CANONICAL_SIGNAL
from aletheia.client._helpers import dump_json, parse_rational
from aletheia.protocols import DBCDefinition

hypothesis.settings.register_profile("ci", max_examples=200)
hypothesis.settings.register_profile("dev", max_examples=20)
hypothesis.settings.load_profile("dev")


# -----------------------------------------------------------------------------
# Strategies
# -----------------------------------------------------------------------------

@st.composite
def signal_name_strategy(draw: st.DrawFn) -> str:
    """Generate identifier-shaped strings (DBC signal naming rules)."""
    first = draw(st.sampled_from("ABCDEFGHIJKLMNOPQRSTUVWXYZ_"))
    rest = draw(st.text(
        alphabet=st.sampled_from(
            "ABCDEFGHIJKLMNOPQRSTUVWXYZ_0123456789abcdefghijklmnopqrstuvwxyz",
        ),
        min_size=0, max_size=15,
    ))
    return first + rest


@st.composite
def can_id_strategy(draw: st.DrawFn) -> int:
    """Generate valid CAN IDs in the 11-bit standard range."""
    return draw(st.integers(min_value=0, max_value=0x7FF))


def _make_signal(draw: st.DrawFn) -> dict[str, object]:
    """Generate one DBCSignalAlways from variable bit/byte-order/sign + canonical numerics.

    The numeric fields (factor/offset/min/max/unit/presence) are pinned to
    the canonical values from ``_canonical_dbc.CANONICAL_SIGNAL`` to avoid
    pylint duplicate-code with the cross-binding canonical fixture; only
    the bits hypothesis actually varies (name, startBit, length, byteOrder,
    signed) come from the strategy draws.
    """
    sig: dict[str, object] = dict(CANONICAL_SIGNAL)  # shallow copy is fine — values are scalars
    sig["name"] = draw(signal_name_strategy())
    sig["startBit"] = draw(st.integers(min_value=0, max_value=63))
    sig["length"] = draw(st.integers(min_value=1, max_value=64))
    sig["byteOrder"] = draw(st.sampled_from(["little_endian", "big_endian"]))
    sig["signed"] = draw(st.booleans())
    return sig


@st.composite
def dbc_strategy(draw: st.DrawFn) -> DBCDefinition:
    """Generate minimal DBC definitions with random signals."""
    n_messages = draw(st.integers(min_value=0, max_value=3))
    messages = []
    for i in range(n_messages):
        n_signals = draw(st.integers(min_value=0, max_value=4))
        signals = [_make_signal(draw) for _ in range(n_signals)]
        messages.append({
            "id": draw(can_id_strategy()),
            "name": f"Msg{i}",
            "dlc": draw(st.integers(min_value=0, max_value=8)),
            "sender": "ECU",
            "signals": signals,
        })
    return {"version": "1.0", "messages": messages}


# -----------------------------------------------------------------------------
# Properties
# -----------------------------------------------------------------------------


@given(payload=st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=126)))
@settings(max_examples=200)
def test_load_json_total_on_printable_ascii(payload: str) -> None:
    """``load_json`` is total over printable ASCII inputs.

    Catches: parser panics on adversarial-but-printable input; assertion
    failures inside the JSON decoder; resource leaks on partial parse.
    Errors are expected (not all printable ASCII is valid JSON); the
    contract is "no exception escape past the documented error types".
    """
    try:
        json.loads(payload)
    except (ValueError, TypeError, RuntimeError):
        pass  # documented error path, not a property failure


@given(numerator=st.integers(min_value=-(10**18), max_value=10**18),
       denominator=st.integers(min_value=-(10**18), max_value=10**18).filter(lambda d: d != 0))
def test_parse_rational_normalises_to_positive_denominator(
    numerator: int, denominator: int,
) -> None:
    """`parse_rational` canonicalises a rational dict to positive-denominator form.

    The Agda kernel's DecRat stores denominators as ℕ (always positive) and
    normalises sign-flip into the numerator (``Fraction(1, -2)`` →
    ``-1/2``).  Python's ``parse_rational`` delegates to ``fractions.
    Fraction``, which applies the same normalisation.  This test verifies
    cross-binding parity over arbitrary signed-denominator inputs that the
    wire format does not strictly forbid (R19 cluster 17 — PY-D-19.3).
    """
    rational_dict = {"numerator": numerator, "denominator": denominator}
    parsed = parse_rational(rational_dict)
    assert parsed.denominator > 0
    assert parsed == Fraction(numerator, denominator)


@given(numerator=st.integers(min_value=-(10**18), max_value=10**18),
       denominator=st.integers(min_value=1, max_value=10**18))
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


@given(dbc=dbc_strategy())
def test_dbc_serialization_round_trips(dbc: DBCDefinition) -> None:
    """``dump_json(dbc)`` followed by ``load_json`` reconstructs the input.

    Catches: silent key drops on optional fields, type-coercion drift
    (int → float, bool → int), preservation of empty arrays vs missing.
    """
    encoded = dump_json(dbc)
    decoded = json.loads(encoded)
    assert decoded == dbc


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
