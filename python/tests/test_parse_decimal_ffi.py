# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Raw-FFI smoke test for ``aletheia_parse_decimal``.

``aletheia_parse_decimal`` is the kernel-side single source of truth for
decimal-string → exact rational (the float principle: a decimal is an exact
``DecRat``, never a float).  The public ``from_decimal`` wraps it
(``test_from_decimal``); this module calls the export directly via ``ctypes``,
which is how it reaches bytes no binding sends, and checks the envelope itself:

    peek → Agda ``parseDecimal`` → the rational component magnitude bound → wire JSON

Every refusal past the peek is the kernel's decision.  Success returns the bare
``{"numerator","denominator"}`` shape the bindings' ``decode_wire_rational``
consumes; a refusal returns the ``{"status":"error",...}`` envelope every
kernel refusal is rendered as (``code``, ``message`` and the code's own fields,
``_decimal_cases`` spells them), and a text the shim refuses before the kernel
reads it (a NUL byte, bytes that are not UTF-8) the three-key
``ffi_validation_error`` envelope.
"""

from __future__ import annotations

import ctypes
import json
from fractions import Fraction
from typing import Final, NewType, cast

import pytest
from _decimal_cases import (
    OVERFLOW_CASES,
    OVERFLOW_IDS,
    PARSE_FAIL_CASES,
    PARSE_FAIL_IDS,
    SUCCESS_CASES,
    OverflowCase,
    ParseFailCase,
)

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


@pytest.mark.parametrize("case", PARSE_FAIL_CASES, ids=PARSE_FAIL_IDS)
def test_parse_decimal_rejects_malformed(case: ParseFailCase) -> None:
    """A malformed literal yields the kernel's parse refusal, position included."""
    assert _parse_decimal(case.text) == case.envelope()


@pytest.mark.parametrize("case", OVERFLOW_CASES, ids=OVERFLOW_IDS)
def test_parse_decimal_rejects_overflow(case: OverflowCase) -> None:
    """A component past the magnitude bound yields the kernel's bound refusal."""
    assert _parse_decimal(case.text) == case.envelope()


# Bytes that are not UTF-8 around digits that are a literal without them: a
# stray byte, a truncated sequence, an encoded surrogate and an overlong NUL.
# Each is written as the lone surrogate ``surrogateescape`` turns into the byte.
_NOT_UTF8: Final = ("1.5\udcff", "1\udce2\udc82.5", "1\udced\udca0\udc805", "\udcc0\udc801")


def test_parse_decimal_refuses_input_that_is_not_utf8() -> None:
    """Bytes that are not UTF-8 are refused by the shim, never dropped to leave a literal."""
    for text in _NOT_UTF8:
        result = _parse_decimal(text)
        assert result == {
            "status": "error",
            "code": "ffi_validation_error",
            "message": "input is not valid UTF-8",
        }, text.encode(errors="surrogateescape")


# Byte strings set between the digits ``1`` and ``5``, so dropping one would
# leave a literal: valid sequences of every length up to the last code point,
# then overlong encodings, encoded surrogates, code points past U+10FFFF,
# truncated sequences and stray continuation and lead bytes.  Each is spelled as
# its bytes in hex, a space between two, as ``bytes.fromhex`` reads them.
HexBytes = NewType("HexBytes", str)
_UTF8_CORPUS: Final = tuple(HexBytes(spelled) for spelled in (
    "", "41", "7f", "c2 80", "df bf", "e0 a0 80", "ef bf bf", "f0 90 80 80", "f4 8f bf bf",
    "c3 a9 e2 82 ac f0 9f 98 80",
    "c0 80", "c1 bf", "e0 80 80", "e0 9f bf", "f0 80 80 80", "f0 8f bf bf",
    "ed a0 80", "ed bf bf", "ed 9f bf", "ee 80 80", "f4 90 80 80", "f5 80 80 80",
    "f8 88 80 80 80", "80", "bf", "c2", "e0 a0", "f0 90 80", "c2 41", "e2 82", "ff", "fe",
))  # fmt: skip


@pytest.mark.parametrize("hex_bytes", _UTF8_CORPUS, ids=lambda hex_bytes: hex_bytes or "empty")
def test_parse_decimal_refuses_as_not_utf8_exactly_what_utf8_refuses(hex_bytes: HexBytes) -> None:
    """The shim refuses as not UTF-8 exactly the bytes Python's strict decoder refuses.

    A sequence the decoder reads is never refused as not UTF-8 and, being no
    digit, never accepted as part of a literal either.
    """
    middle = bytes.fromhex(hex_bytes)
    raw = b"1" + middle + b"5"
    result = _parse_decimal(raw.decode(errors="surrogateescape"))
    not_utf8 = {
        "status": "error",
        "code": "ffi_validation_error",
        "message": "input is not valid UTF-8",
    }
    try:
        _ = middle.decode()
    except UnicodeDecodeError:
        assert result == not_utf8, raw
    else:
        assert result != not_utf8, raw
        assert not middle or result.get("status") == "error", raw
