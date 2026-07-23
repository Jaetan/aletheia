# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Real-FFI regression tests for the binary wire's Int64 rational slots.

The binary extraction wire carries each signal value as a signed 64-bit
numerator/denominator pair, but the kernel computes exact unbounded
rationals — reduction alone can push a component past the wire range
even when every DBC field and frame byte is in range.  The FFI shim's
binary encoder (``AletheiaFFI/BinaryOutput.hs``) checks both components
before the poke and reroutes any unrepresentable value to the per-signal
error stream with the kernel-minted ``ValueExceedsWireRange`` code.

Regression pinned here: before the guard, the over-range components were
narrowed with a silently wrapping conversion, so ``extract_signals``
returned a *wrong* value (observed as a sign-flipped garbage number) with
an empty error list.
"""

from fractions import Fraction

from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient
from aletheia.limits import MAX_RATIONAL_COMPONENT_MAGNITUDE
from aletheia.types import DLCCode

# The signed 64-bit wire range shared by the binary FFI's rational slots
# and the JSON ingestion bound (one Int64 bound on every wire).
_INT64_MAX = MAX_RATIONAL_COMPONENT_MAGNITUDE

_FRAME = bytearray([0xFF, 0xFF, 0, 0, 0, 0, 0, 0])


class TestExtractionValueExceedsWireRange:
    """Over-range exact values become typed per-signal error entries."""

    def test_numerator_overflow_reroutes_to_error_entry(self) -> None:
        """17-significant-digit factor × 16-bit all-ones raw: no silent wrap.

        The exact value passes the signal's own ``[minimum, maximum]``
        bounds, but its reduced numerator exceeds the Int64 wire slot.
        The signal must be ABSENT from ``values`` and carry exactly one
        error entry naming the Int64 wire range.

        This test also pins the host-crash fix in the JSON ingestion
        measurement: the ``parse_dbc`` call submits the same
        large-component rationals the bound exists to measure, and an
        earlier implementation measured them with the unary
        value-recursive natural-number max, whose cost grows with the
        component's VALUE — the call would hang and exhaust host memory
        instead of returning.  Completing in normal test time (under the
        client's default RTS heap cap) IS the regression pin.
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
                    [signal("Speed", factor=factor, maximum=Fraction(10000))],
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

    def test_denominator_overflow_reroutes_to_error_entry(self) -> None:
        """Reduced denominator past Int64 (numerator in range): same reroute.

        ``factor + offset`` denominators are each in range and terminating
        (2/5-smooth, so ``parse_dbc`` accepts them), but their lcm — the
        exact value's reduced denominator — exceeds the wire slot while
        the numerator still fits.  Pins the guard's denominator arm
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
                            maximum=Fraction(10000),
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
        """The rerouted entry surfaces the kernel-minted reason verbatim.

        End-to-end pin of the reason string the shim puts on the wire
        (``wireRangeReason`` in ``Aletheia.CAN.BatchExtraction``): callers
        switch on this message to tell the reroute apart from a
        kernel-side extraction failure, so its exact public text is part
        of the contract.
        """
        factor = Fraction(12345678901234567, 10**17)
        wrap_dbc = dbc(
            [
                message(
                    256,
                    "M",
                    [signal("Speed", factor=factor, maximum=Fraction(10000))],
                )
            ]
        )
        with AletheiaClient() as client:
            assert client.parse_dbc(wrap_dbc)["status"] == "success"
            result = client.extract_signals(can_id=256, dlc=DLCCode(8), data=_FRAME)
        assert (
            result.errors["Speed"]
            == "extracted value's numerator or denominator exceeds the Int64 wire range"
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
                            minimum=-edge,
                            maximum=0,
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
