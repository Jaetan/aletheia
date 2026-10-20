# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Real-FFI regression tests for the Int64 bound on an extracted value.

The kernel computes exact unbounded rationals, and reduction alone can
push a component past the Int64 range even when every DBC field and frame
byte is in range.  The kernel's batch categoriser
(``Aletheia.CAN.BatchExtraction.wireFits``) refuses an extracted value
whose reduced ``|numerator|`` or denominator is above
``MAX_RATIONAL_COMPONENT_MAGNITUDE`` (a symmetric magnitude bound) on both
extraction paths, the JSON-answering entry and the binary buffer, as a
per-signal error entry carrying the ``ValueExceedsWireRange`` code and
one message.  The binary wire's int64 slots therefore only ever carry a
value the kernel kept.

Regression pinned here: without the bound, an over-range component was
narrowed with a silently wrapping conversion, so ``extract_signals``
returned a *wrong* value (observed as a sign-flipped garbage number) with
an empty error list.
"""

import json
from fractions import Fraction
from typing import TYPE_CHECKING, NewType

from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, FFIBackend
from aletheia.limits import MAX_RATIONAL_COMPONENT_MAGNITUDE
from aletheia.types import DLCCode, ParseDBCCommand, dump_json

if TYPE_CHECKING:
    from aletheia.types import DBCDefinition

# The signed 64-bit wire range shared by the binary FFI's rational slots
# and the JSON ingestion bound (one Int64 bound on every wire).
_INT64_MAX = MAX_RATIONAL_COMPONENT_MAGNITUDE

_FRAME = bytearray([0xFF, 0xFF, 0, 0, 0, 0, 0, 0])

# The message the kernel puts on every over-range refusal, on both paths.
_WIRE_RANGE_MESSAGE = "extracted value's numerator or denominator exceeds the Int64 wire range"

# The data bytes of one CAN 2.0B frame, DLC 8.
FramePayload = NewType("FramePayload", bytes)


def _json_entry_refuses_big(big_dbc: DBCDefinition, data: FramePayload) -> None:
    """Assert the JSON-answering extraction entry refuses ``Big`` with the kernel's message.

    Drives the backend directly: the Client takes the binary buffer once the
    DBC's signal names are cached, so the JSON entry is reached by loading
    the DBC through the raw command and calling the entry itself.
    """
    command: ParseDBCCommand = {"type": "command", "command": "parseDBC", "dbc": big_dbc}
    backend = FFIBackend()
    state = backend.init()
    try:
        loaded = json.loads(backend.process(state, dump_json(command).encode()))
        assert loaded["status"] == "success", loaded
        reply = json.loads(
            backend.extract_signals_binary(
                state, can_id=0x100, extended=False, dlc=DLCCode(8), data=data
            )
        )
    finally:
        backend.close(state)
    assert reply == {
        "status": "success",
        "values": [],
        "errors": [{"name": "Big", "error": _WIRE_RANGE_MESSAGE}],
        "absent": [],
    }, reply


def _assert_refused_on_both_paths(
    data: FramePayload,
    *,
    factor: Fraction,
    offset: Fraction,
    minimum: Fraction,
    maximum: Fraction,
) -> None:
    """Assert one 64-bit unsigned signal ``Big`` at ``data`` is refused alike on both paths."""
    big = signal("Big", length=64, factor=factor, offset=offset, minimum=minimum, maximum=maximum)
    big_dbc = dbc([message(0x100, "Msg", [big])])
    _json_entry_refuses_big(big_dbc, data)
    with AletheiaClient() as client:
        assert client.parse_dbc(big_dbc)["status"] == "success"
        binary = client.extract_signals(can_id=0x100, dlc=DLCCode(8), data=data)
    assert binary.errors == {"Big": _WIRE_RANGE_MESSAGE}, dict(binary.errors)
    assert binary.values == {}, dict(binary.values)
    assert binary.absent == ()


class TestExtractionValueExceedsWireRange:
    """Over-range exact values become typed per-signal error entries."""

    def test_numerator_overflow_refused_as_error_entry(self) -> None:
        """17-significant-digit factor × 16-bit all-ones raw: no silent wrap.

        The exact value passes the signal's own ``[minimum, maximum]``
        bounds, but its reduced numerator exceeds the Int64 wire slot.
        The signal must be ABSENT from ``values`` and carry exactly one
        error entry naming the Int64 wire range.  The signal is 17 bits
        wide so that its declared maximum lies within what its bits carry;
        the frame sets only the low 16.

        This test also pins the cost of the JSON ingestion measurement:
        the ``parse_dbc`` call submits the large-component rationals the
        bound exists to measure, and the kernel measures them with the
        builtin maximum, whose cost does not grow with the component's
        value.  Completing in normal test time (under the client's default
        RTS heap cap) IS the regression pin.
        """
        factor = Fraction(12345678901234567, 10**17)
        exact = factor * 0xFFFF
        # Fixture self-check: the scenario is adversarial only while the
        # reduced numerator actually exceeds the wire range.
        assert exact.numerator > _INT64_MAX
        assert exact.denominator <= _INT64_MAX

        wrap_dbc = dbc(
            [
                message(
                    256,
                    "M",
                    [signal("Speed", length=17, factor=factor, maximum=Fraction(10000))],
                )
            ]
        )
        with AletheiaClient() as client:
            parsed = client.parse_dbc(wrap_dbc)
            assert parsed["status"] == "success", parsed
            result = client.extract_signals(can_id=256, dlc=DLCCode(8), data=_FRAME)

        assert "Speed" not in result.values, dict(result.values)
        assert list(result.errors) == ["Speed"], dict(result.errors)
        assert "Int64 wire range" in result.errors["Speed"]
        assert result.absent == ()

    def test_denominator_overflow_refused_as_error_entry(self) -> None:
        """Reduced denominator past Int64 (numerator in range): same refusal.

        ``factor + offset`` denominators are each in range and terminating
        (2/5-smooth, so ``parse_dbc`` accepts them), but their lcm — the
        exact value's reduced denominator — exceeds the wire slot while
        the numerator still fits.  Pins the bound's denominator arm
        independently of the numerator arm.
        """
        factor = Fraction(1, 2**62)
        offset = Fraction(1, 5**26)
        exact = factor * 1 + offset
        # Fixture self-check: denominator-only overflow.
        assert abs(exact.numerator) <= _INT64_MAX
        assert exact.denominator > _INT64_MAX

        den_dbc = dbc(
            [
                message(
                    256,
                    "M",
                    [
                        signal(
                            "S",
                            factor=factor,
                            offset=offset,
                            # The bits carry [offset, offset + factor × 0xFFFF];
                            # the maximum leaves the offset out, whose sum with it
                            # has a denominator past Int64, and stays inside them.
                            minimum=offset,
                            maximum=factor * 0xFFFF,
                        )
                    ],
                )
            ]
        )
        with AletheiaClient() as client:
            parsed = client.parse_dbc(den_dbc)
            assert parsed["status"] == "success", parsed
            # Raw value 1 keeps the numerator small; the denominator is
            # fixed by the factor/offset lcm.
            result = client.extract_signals(
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([0x01, 0x00, 0, 0, 0, 0, 0, 0]),
            )

        assert "S" not in result.values, dict(result.values)
        assert list(result.errors) == ["S"], dict(result.errors)
        assert "Int64 wire range" in result.errors["S"]

    def test_error_message_is_the_exact_wire_range_message(self) -> None:
        """The error entry carries the kernel's reason verbatim.

        End-to-end pin of the message the kernel's batch categoriser puts
        on a ``ValueExceedsWireRange`` refusal (``Aletheia.CAN.BatchExtraction``,
        the string twin of the code): callers switch on this message to
        tell the bound's refusal apart from another extraction failure, so
        its exact public text is part of the contract.
        """
        factor = Fraction(12345678901234567, 10**17)
        wrap_dbc = dbc(
            [
                message(
                    256,
                    "M",
                    [signal("Speed", length=17, factor=factor, maximum=Fraction(10000))],
                )
            ]
        )
        with AletheiaClient() as client:
            assert client.parse_dbc(wrap_dbc)["status"] == "success"
            result = client.extract_signals(can_id=256, dlc=DLCCode(8), data=_FRAME)
        assert result.errors["Speed"] == _WIRE_RANGE_MESSAGE

    def test_both_components_past_the_bound_refused_on_both_paths(self) -> None:
        """A 64-bit signal whose value has both components past Int64 is refused alike.

        The factor and offset denominators (a power of two and a power of
        five) are each in range, but at raw ``2**63 + 1`` the exact value's
        reduced numerator and denominator both land past the bound.  The
        JSON-answering entry refuses it exactly as the binary buffer does:
        one error entry named ``Big`` with the kernel's message, no value,
        nothing absent.
        """
        factor = Fraction(1, 2**62)
        offset = Fraction(1, 5**27)
        raw = 2**63 + 1
        exact = factor * raw + offset
        # Fixture self-check: both components are past the bound.
        assert exact.numerator > _INT64_MAX
        assert exact.denominator > _INT64_MAX

        _assert_refused_on_both_paths(
            FramePayload(raw.to_bytes(8, "little")),
            factor=factor,
            offset=offset,
            minimum=offset,
            maximum=Fraction(3),
        )

    def test_numerator_exactly_minus_two_to_the_63_refused_on_both_paths(self) -> None:
        """A numerator of exactly ``-(2**63)`` is refused: the bound is symmetric.

        ``-(2**63)`` fits an int64 slot, but the kernel holds a component's
        magnitude to ``MAX_RATIONAL_COMPONENT_MAGNITUDE`` on both sides of
        zero.  Raw ``2**63`` scaled by ``-1/5`` lands the reduced numerator
        exactly there with the denominator in range; the signal's minimum
        is what its bits carry, so the range check accepts the value and
        the magnitude bound is what refuses it, on both paths alike.
        """
        factor = Fraction(-1, 5)
        raw = 2**63
        exact = factor * raw
        # Fixture self-check: the numerator sits one past the negative bound.
        assert exact.numerator == -(2**63)
        assert -exact.numerator == _INT64_MAX + 1
        assert exact.denominator <= _INT64_MAX

        _assert_refused_on_both_paths(
            FramePayload(raw.to_bytes(8, "little")),
            factor=factor,
            offset=Fraction(0),
            minimum=Fraction(-(2**64 - 1), 5),
            maximum=Fraction(0),
        )


class TestWireRangeBoundaryAccepted:
    """Components exactly at Int64 max travel the wire exactly (tightness)."""

    def test_value_with_numerator_at_int64_max_travels_exactly(self) -> None:
        """A 1-bit signal scaled to exactly Int64 max round-trips exactly.

        The guard must not over-refuse: components AT the wire range are
        representable and must come back as the exact ``Fraction``, not an
        error entry.  Together with the overflow tests this pins the
        boundary from both sides.
        """
        edge = Fraction(_INT64_MAX)
        edge_dbc = dbc(
            [
                message(
                    256,
                    "M",
                    [signal("S", length=1, factor=edge, maximum=edge)],
                )
            ]
        )
        with AletheiaClient() as client:
            parsed = client.parse_dbc(edge_dbc)
            assert parsed["status"] == "success", parsed
            result = client.extract_signals(
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([0x01, 0x00, 0, 0, 0, 0, 0, 0]),
            )
        assert result.errors == {}, dict(result.errors)
        value = result.values["S"]
        assert value == edge
        assert value.numerator == _INT64_MAX
        assert value.denominator == 1

    def test_value_with_negative_numerator_at_int64_max_travels_exactly(self) -> None:
        """The negative side of the signed wire slot round-trips exactly too.

        An offset of exactly −(Int64 max) with raw value 0 lands the
        exact value on the slot's negative boundary (the magnitude limit
        is symmetric); it must come back as the exact negative
        ``Fraction``, not an error entry.
        """
        edge = Fraction(_INT64_MAX)
        edge_dbc = dbc(
            [
                message(
                    256,
                    "M",
                    [
                        signal(
                            "S",
                            length=1,
                            offset=-edge,
                            # The one bit carries −edge and 1 − edge.
                            minimum=-edge,
                            maximum=1 - edge,
                        )
                    ],
                )
            ]
        )
        with AletheiaClient() as client:
            parsed = client.parse_dbc(edge_dbc)
            assert parsed["status"] == "success", parsed
            result = client.extract_signals(
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray(8),
            )
        assert result.errors == {}, dict(result.errors)
        value = result.values["S"]
        assert value == -edge
        assert value.numerator == -_INT64_MAX
        assert value.denominator == 1
