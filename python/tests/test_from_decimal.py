# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""High-level parity tests for the public :func:`aletheia.from_decimal`.

``from_decimal`` is the cross-binding single source of truth for decimal-string
→ exact rational (the float principle: a decimal is an exact ``Fraction``, never
a float).  It wraps the kernel ``aletheia_parse_decimal`` FFI export and decodes
a refusal with the decoder every kernel refusal goes through.

Distinct from ``test_parse_decimal_ffi.py`` (which exercises the raw ctypes
marshaling path): this test covers the *binding* wrapper — success returns the
exact :class:`~fractions.Fraction`; a refused literal surfaces as
:class:`aletheia.ValidationError` carrying the kernel's code and message (the
literal is the caller's own text), and a component past the magnitude bound as
:class:`aletheia.InputBoundExceededError` carrying the bound's fields,
mirroring Go / C++ / Rust.

Decimal parsing is RTS-gated (it runs the kernel's parser and bound), so the
module brings the GHC RTS up via the shared ``rts_up`` fixture.
"""

from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import pytest
from _decimal_cases import (
    OVERFLOW_CASES,
    OVERFLOW_IDS,
    PARSE_FAIL_CASES,
    PARSE_FAIL_IDS,
    SUCCESS_CASES,
    DecimalText,
    OverflowCase,
    ParseFailCase,
)
from _stand_in import StandInName, stand_in_kernel

from aletheia import FFIError, InputBoundExceededError, ProtocolError, ValidationError, from_decimal
from aletheia.client._ffi import AletheiaDecimal, AletheiaRational
from aletheia.client._helpers.rational import decimal_value
from aletheia.codes import ErrorCode
from aletheia.limits import (
    BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
    MAX_RATIONAL_COMPONENT_MAGNITUDE,
)

if TYPE_CHECKING:
    import ctypes

pytestmark = pytest.mark.usefixtures("rts_up")


@pytest.mark.parametrize(("text", "numerator", "denominator"), SUCCESS_CASES)
def test_from_decimal_success(text: str, numerator: int, denominator: int) -> None:
    """A valid decimal yields the exact, canonical :class:`Fraction`."""
    result = from_decimal(text)
    assert isinstance(result, Fraction)
    assert result == Fraction(numerator, denominator)
    # Python's own exact decimal parse agrees (and the FFI pair is lowest-terms).
    assert result == Fraction(text)
    assert (result.numerator, result.denominator) == (
        Fraction(numerator, denominator).numerator,
        Fraction(numerator, denominator).denominator,
    )


@pytest.mark.parametrize("case", PARSE_FAIL_CASES, ids=PARSE_FAIL_IDS)
def test_from_decimal_rejects_malformed(case: ParseFailCase) -> None:
    """A malformed literal raises ValidationError with the kernel's code and message."""
    with pytest.raises(ValidationError) as exc_info:
        from_decimal(case.text)
    assert exc_info.value.code == case.code
    assert str(exc_info.value) == case.envelope()["message"]


@pytest.mark.parametrize("case", OVERFLOW_CASES, ids=OVERFLOW_IDS)
def test_from_decimal_rejects_overflow(case: OverflowCase) -> None:
    """A component past the magnitude bound raises the typed bound error, field ``decimal``."""
    with pytest.raises(InputBoundExceededError) as exc_info:
        from_decimal(case.text)
    err = exc_info.value
    assert err.code == "input_bound_exceeded"
    assert err.kind == BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE
    assert err.observed == case.observed
    assert err.limit == MAX_RATIONAL_COMPONENT_MAGNITUDE
    assert err.field == "decimal"
    assert str(err) == case.envelope()["message"]


def test_from_decimal_rejects_non_ascii() -> None:
    """A non-ASCII literal is a grammar refusal, not a UTF-8 one.

    The text is valid UTF-8, so the kernel reads it, parses ``1.5`` and stops in
    front of the character it cannot read.
    """
    with pytest.raises(ValidationError) as exc_info:
        from_decimal("1.5€")
    assert exc_info.value.code == "text_trailing_input"
    assert str(exc_info.value) == (
        "parse failed at line 1, column 4 (first unparseable statement starts at line 1, column 4)"
    )


def test_from_decimal_rejects_interior_nul() -> None:
    """An interior NUL is refused by the shim, not read as the end of the literal."""
    with pytest.raises(ValidationError) as exc_info:
        _ = from_decimal("1\x00xyz")
    assert exc_info.value.code == ErrorCode.FFI_VALIDATION_ERROR
    assert str(exc_info.value) == "input contains a NUL byte"


def test_from_decimal_vocal_when_rts_down(monkeypatch: pytest.MonkeyPatch) -> None:
    """Vocal contract: with the RTS down, raise FFIError before the FFI call.

    ``from_decimal`` never self-initialises the GHC RTS (an ``FFIBackend`` is the
    sole initialiser, owning the bus-count ``-N``).  The ``rts_up`` fixture has
    the RTS genuinely up, so stub ``hs_initialized`` to report it down and assert
    the guard fires rather than invoking the MAlonzo export (which would be UB).
    """
    monkeypatch.setattr(
        "aletheia.client._helpers.rational.hs_initialized",
        lambda: False,
    )
    with pytest.raises(FFIError, match="not initialized"):
        from_decimal("1")


# Lone surrogates, the one text a ``str`` holds that is not UTF-8: each reaches
# the shim as the bytes ``surrogatepass`` writes, which it refuses as it refuses
# the bytes Go and C++ hand it that are not UTF-8.
_LONE_SURROGATES = (DecimalText("1.5\ud800"), DecimalText("1.5\udcff"), DecimalText("\udfff1"))


@pytest.mark.parametrize("text", _LONE_SURROGATES)
def test_from_decimal_refuses_a_lone_surrogate(text: DecimalText) -> None:
    """A lone surrogate is the shim's refusal of text that is not UTF-8, as in every binding."""
    with pytest.raises(ValidationError) as exc_info:
        _ = from_decimal(text)
    assert exc_info.value.code == ErrorCode.FFI_VALIDATION_ERROR
    assert str(exc_info.value) == "input is not valid UTF-8"


def test_from_decimal_failure_without_an_envelope_is_a_protocol_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A failure the library answers without an error envelope is a wire fault.

    The null stand-in kernel answers the decimal entry with failure and no
    envelope; the renderer loads it in place of the library, as Go's loader
    test does, and the fault is a ``ProtocolError`` as in Go, C++ and Rust.
    """
    cell: list[ctypes.CDLL | None] = [None]
    monkeypatch.setattr("aletheia.client._enrichment._RENDERER_LIB", cell)
    monkeypatch.setenv("ALETHEIA_LIB", str(stand_in_kernel(StandInName("null_kernel"))))
    with pytest.raises(ProtocolError) as exc_info:
        _ = from_decimal("1")
    assert str(exc_info.value) == "aletheia_parse_decimal failed without an error"
    assert exc_info.value.code is None


@pytest.mark.parametrize(
    "rational",
    [AletheiaRational(numerator=1, denominator=0), AletheiaRational(numerator=1, denominator=-1)],
    ids=["zero", "negative"],
)
def test_decimal_value_refuses_a_non_positive_denominator(rational: AletheiaRational) -> None:
    """A rational the kernel never answers is a wire fault, worded as Go, C++ and Rust word it."""
    with pytest.raises(ProtocolError) as exc_info:
        _ = decimal_value(AletheiaDecimal(value=rational))
    assert str(exc_info.value) == (
        f"aletheia_parse_decimal answered a non-positive denominator {rational.denominator}"
    )


def test_decimal_value_reads_the_answered_rational() -> None:
    """A positive denominator is the kernel's answer, read as the exact fraction."""
    out = AletheiaDecimal(value=AletheiaRational(numerator=-157, denominator=50))
    assert decimal_value(out) == Fraction(-157, 50)
