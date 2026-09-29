# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Raw-FFI smoke test for ``aletheia_parse_decimal``.

``aletheia_parse_decimal`` is the kernel-side single source of truth for
decimal-string → exact rational (the float principle: a decimal is an exact
``DecRat``, never a float).  The public ``from_decimal`` wraps it
(``test_from_decimal``); this module calls the export directly via ``ctypes``,
which is how it reaches bytes no binding sends, and checks the envelope itself:

    peek → Agda ``parseDecimal`` → ``toℚ`` → Int64 bound check → wire JSON

Success returns the bare
``{"numerator","denominator"}`` shape the bindings' ``decode_wire_rational``
consumes; failure returns a ``{"status":"error",...}`` envelope keyed by
``message`` (the cross-binding convention) with a precise ``code`` and the
offending ``input`` echoed.
"""

from __future__ import annotations

import ctypes
import json
from fractions import Fraction
from typing import Final, cast

import pytest
from _decimal_cases import OVERFLOW_CASES, PARSE_FAIL_CASES, SUCCESS_CASES

from aletheia.client._ffi import (
    AletheiaDecimal,
    AletheiaText,
    configure_ffi_signatures,
    find_ffi_library,
)

# The parser MAlonzo code needs a live GHC RTS; the module-scoped fixture brings
# it up (idempotent, refcounted) for every test here.  Loading the .so below
# only dlopens it (no RTS needed); calling parse_decimal — which does — happens
# in the test bodies, where the fixture has run.
pytestmark = pytest.mark.usefixtures("rts_up")

# dlopen the built .so once and pin the signatures.  A failure's error is an
# owned char* freed via aletheia_free_str.
_LIB = ctypes.CDLL(str(find_ffi_library()))
configure_ffi_signatures(_LIB)


def _parse_decimal(text: str) -> dict[str, object]:
    r"""Call the FFI on *text*: the rational as a dict, or the error envelope, freed.

    *text* is encoded as UTF-8 with ``surrogateescape``, so a lone surrogate
    ``\udcXX`` in it reaches the kernel as the raw byte ``XX``.
    """
    out = AletheiaDecimal()
    raw = text.encode(errors="surrogateescape")
    text_arg = ctypes.byref(AletheiaText(raw, len(raw)))
    if _LIB.aletheia_parse_decimal(text_arg, ctypes.byref(out)) == 0:
        return {"numerator": out.value.numerator, "denominator": out.value.denominator}
    err: int | None = out.err
    assert err is not None
    try:
        parsed = json.loads(ctypes.string_at(err).decode())
        assert isinstance(parsed, dict)
        return cast("dict[str, object]", parsed)
    finally:
        _LIB.aletheia_free_str(err)


@pytest.mark.parametrize(("text", "numerator", "denominator"), SUCCESS_CASES)
def test_parse_decimal_success(text: str, numerator: int, denominator: int) -> None:
    """A valid decimal yields the exact, canonical wire rational."""
    result = _parse_decimal(text)
    assert result == {"numerator": numerator, "denominator": denominator}
    # Cross-check against Python's own exact decimal parse (Fraction of a
    # decimal string is itself exact); the FFI pair is in lowest terms.
    assert Fraction(text) == Fraction(numerator, denominator)


@pytest.mark.parametrize("text", PARSE_FAIL_CASES)
def test_parse_decimal_rejects_malformed(text: str) -> None:
    """Malformed input yields a parse-failure envelope echoing the input."""
    result = _parse_decimal(text)
    assert result["status"] == "error"
    assert result["code"] == "decimal_parse_failed"
    assert result["input"] == text
    assert isinstance(result["message"], str)
    assert result["message"]  # non-empty reason


@pytest.mark.parametrize("text", OVERFLOW_CASES)
def test_parse_decimal_rejects_overflow(text: str) -> None:
    """A numerator or denominator beyond the Int64 wire range is rejected."""
    result = _parse_decimal(text)
    assert result["status"] == "error"
    assert result["code"] == "decimal_overflow"
    assert result["input"] == text


# Bytes that are not UTF-8 around digits that are a literal without them: a
# stray byte, a truncated sequence, an encoded surrogate and an overlong NUL.
# Each is written as the lone surrogate ``surrogateescape`` turns into the byte.
_NOT_UTF8: Final = ("1.5\udcff", "1\udce2\udc82.5", "1\udced\udca0\udc805", "\udcc0\udc801")


def test_parse_decimal_refuses_input_that_is_not_utf8() -> None:
    """Bytes that are not UTF-8 are refused, never dropped to leave a literal."""
    for text in _NOT_UTF8:
        result = _parse_decimal(text)
        assert result == {
            "status": "error",
            "code": "decimal_parse_failed",
            "message": "input is not valid UTF-8",
            "input": "",
        }, text.encode(errors="surrogateescape")
