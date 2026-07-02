# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""High-level parity tests for the public :func:`aletheia.from_decimal`.

``from_decimal`` is the cross-binding single source of truth for decimal-string
→ exact rational (the float principle: a decimal is an exact ``Fraction``, never
a float).  It wraps the kernel ``aletheia_parse_decimal`` FFI export, branching
on the error envelope before reusing the shared wire decoder.

Distinct from ``test_parse_decimal_ffi.py`` (which exercises the raw ctypes
marshaling path): this test covers the *binding* wrapper — success returns the
exact :class:`~fractions.Fraction`; a parse failure or Int64 overflow surfaces
as :class:`aletheia.ValidationError` (user input, not a protocol/core fault),
mirroring Go / C++ / Rust.

Decimal parsing is RTS-gated (it runs the kernel ``toℚ`` + Int64 bound check),
so the module brings the GHC RTS up via the shared ``rts_up`` fixture.
"""

from __future__ import annotations

from fractions import Fraction

import pytest
from _decimal_cases import OVERFLOW_CASES, PARSE_FAIL_CASES, SUCCESS_CASES

from aletheia import FFIError, ValidationError, from_decimal

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


@pytest.mark.parametrize("text", PARSE_FAIL_CASES)
def test_from_decimal_rejects_malformed(text: str) -> None:
    """Malformed input raises ValidationError (user input, not a wire fault)."""
    with pytest.raises(ValidationError):
        from_decimal(text)


@pytest.mark.parametrize("text", OVERFLOW_CASES)
def test_from_decimal_rejects_overflow(text: str) -> None:
    """An Int64-overflowing numerator/denominator raises ValidationError."""
    with pytest.raises(ValidationError):
        from_decimal(text)


def test_from_decimal_rejects_non_ascii() -> None:
    r"""A non-ASCII literal raises ValidationError, not a Protocol/wire fault.

    Regression guard for the shim's JSON encoding of the echoed ``input`` field:
    before ``Marshal.hs`` used ``jsonString``, ``show`` emitted an invalid-JSON
    ``\NNN`` escape for the non-ASCII byte, so the error envelope failed to parse
    and surfaced a confusing Protocol error instead of this ValidationError.
    """
    with pytest.raises(ValidationError):
        from_decimal("1.5€")  # 1.5€


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
