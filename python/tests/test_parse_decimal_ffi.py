# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Raw-FFI smoke test for ``aletheia_parse_decimal``.

``aletheia_parse_decimal`` is the kernel-side single source of truth for
decimal-string → exact rational (the float principle: a decimal is an exact
``DecRat``, never a float).  Phase 0 ships only the Agda function + shim export;
no high-level binding wrapper exists yet (that is Phase 1).  So this exercises
the new shim marshaling path directly via ``ctypes``:

    peek → Agda ``parseDecimal`` → ``toℚ`` → Int64 bound check → wire JSON

This is the *only* gate that covers that path — ``check-fidelity`` covers the
binary path, ``check-ffi-exports`` only checks names.  Success returns the bare
``{"numerator","denominator"}`` shape the bindings' ``decode_wire_rational``
consumes; failure returns a ``{"status":"error",...}`` envelope keyed by
``message`` (the cross-binding convention) with a precise ``code`` and the
offending ``input`` echoed.
"""

from __future__ import annotations

import ctypes
import json
from fractions import Fraction
from typing import cast

import pytest
from _decimal_cases import OVERFLOW_CASES, PARSE_FAIL_CASES, SUCCESS_CASES

from aletheia.client._ffi import find_ffi_library

# The parser MAlonzo code needs a live GHC RTS; the module-scoped fixture brings
# it up (idempotent, refcounted) for every test here.  Loading the .so below
# only dlopens it (no RTS needed); calling parse_decimal — which does — happens
# in the test bodies, where the fixture has run.
pytestmark = pytest.mark.usefixtures("rts_up")

# dlopen the built .so once and pin the signatures.  The result is an owned
# char* freed via aletheia_free_str.
_LIB = ctypes.CDLL(str(find_ffi_library()))
_LIB.aletheia_parse_decimal.restype = ctypes.c_void_p
_LIB.aletheia_parse_decimal.argtypes = [ctypes.c_char_p]
_LIB.aletheia_free_str.restype = None
_LIB.aletheia_free_str.argtypes = [ctypes.c_void_p]


def _parse_decimal(text: str) -> dict[str, object]:
    """Call the FFI on *text*, free the returned string, return the parsed JSON."""
    ptr = _LIB.aletheia_parse_decimal(text.encode())
    try:
        raw = ctypes.cast(ptr, ctypes.c_char_p).value
        assert raw is not None
        parsed = json.loads(raw.decode())
        assert isinstance(parsed, dict)
        return cast("dict[str, object]", parsed)
    finally:
        _LIB.aletheia_free_str(ptr)


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
