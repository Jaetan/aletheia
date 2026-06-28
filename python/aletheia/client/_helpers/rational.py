# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""ℚ arithmetic + parsing + validation for the JSON / binary FFI wire."""

from __future__ import annotations

import ctypes
from fractions import Fraction
from typing import TYPE_CHECKING, TypeGuard

from aletheia.client._enrichment import get_renderer_lib
from aletheia.client._ffi import hs_initialized, parse_json_object
from aletheia.client._types import FFIError, ProtocolError, ValidationError
from aletheia.types import is_str_dict

if TYPE_CHECKING:
    from collections.abc import Mapping

    from aletheia.types import JSONValue

# int64 bounds match the Haskell ``Int64`` numerator/denominator that the
# Agda core consumes; the binary FFI wire packs each component as ``<q``
# little-endian, so a value outside this range cannot cross the boundary.
_INT64_MAX = (1 << 63) - 1
_INT64_MIN = -(1 << 63)


def is_pure_int(v: object) -> TypeGuard[int]:
    """Type guard: value is an ``int`` and not a ``bool`` subclass.

    Python's ``bool`` is a subclass of ``int`` (``isinstance(True, int)``
    returns ``True``), so plain ``isinstance(v, int)`` is insufficient
    for "is this a numeric integer?" checks.  This guard rejects bools
    while accepting all other ``int`` values.  Lives here (next to the wire
    rational decoders that use it) rather than in ``_loader_utils`` so the
    loader helpers can delegate decimal parsing to :func:`from_decimal`
    without a circular import.
    """
    return isinstance(v, int) and not isinstance(v, bool)


def from_decimal(s: str) -> Fraction:
    """Parse a decimal string into an exact :class:`~fractions.Fraction`.

    The cross-binding single source of truth for decimal → rational: delegates
    to the verified Agda kernel's ``aletheia_parse_decimal`` FFI export (the
    float principle — a decimal is an exact rational, never a float).  The
    accepted grammar is the kernel's: ``-?digits`` or ``-?digits.digits+`` —
    no ``+`` sign, no leading/trailing ``.``, no exponent (so ``"1e3"``,
    ``".5"``, ``"1."``, ``"+2"`` are rejected, and the whole string must be
    consumed).  Mirrors Go ``ParseDecimal`` / C++ ``Rational::from_decimal`` /
    Rust ``Rational::from_decimal`` exactly.

    Like rational *display* (:func:`~aletheia.client._enrichment.format_rational`),
    decimal parsing is RTS-gated and **vocal**: it never initialises the GHC
    RTS (an :class:`FFIBackend` is the sole initialiser, owning the bus-count
    ``-N``), so it raises before the FFI call when the RTS is down rather than
    self-initialising.

    Raises:
        FFIError: the GHC runtime is not initialised (no client/backend
            created), or the FFI returned a null pointer.
        ValidationError: *s* is not a valid decimal literal, or its exact
            rational overflows the Int64 wire range (the kernel's
            ``decimal_parse_failed`` / ``decimal_overflow`` — user input, not
            a wire fault).
        ProtocolError: the FFI returned a malformed response envelope (an
            ABI / kernel malfunction).

    """
    if not hs_initialized():
        msg = (
            "GHC runtime not initialized: create an AletheiaClient (or FFIBackend) "
            "before parsing decimals — from_decimal does not self-initialise the RTS"
        )
        raise FFIError(msg)
    lib = get_renderer_lib()
    raw = lib.aletheia_parse_decimal(s.encode())  # str.encode defaults to utf-8
    if not raw:
        msg = "aletheia_parse_decimal returned a null pointer"
        raise FFIError(msg)
    try:
        decoded = ctypes.cast(raw, ctypes.c_char_p).value
    finally:
        lib.aletheia_free_str(raw)
    if decoded is None:
        msg = "aletheia_parse_decimal returned a null pointer"
        raise FFIError(msg)
    response = parse_json_object(decoded.decode())
    # Branch on the error envelope BEFORE handing the value to the wire
    # decoder: otherwise ``decode_wire_rational`` reports an opaque "missing
    # numerator" and masks the precise decimal_parse_failed / decimal_overflow
    # reason.  A failure is user-input (ValidationError), not a wire fault.
    if response.get("status") == "error":
        message = response.get("message", "invalid decimal literal")
        raise ValidationError(str(message))
    # Success envelope is the bare {"numerator", "denominator"} wire shape that
    # the shared wire decoder consumes — no reimplemented denom > 0 check.
    return decode_wire_rational(response)


def to_exact_fraction(value: int | Fraction) -> Fraction:
    """Coerce an exact numeric API input to a :class:`~fractions.Fraction`.

    The float principle at the runtime API boundary: a predicate threshold or a
    signal value must be an exact ``int`` or ``Fraction``.

    - A ``float`` is **rejected** — ``Fraction(0.1)`` captures the IEEE-754
      rounding error (``3602879701896397/36028797018963968``), not ``1/10``;
      pass a ``Fraction`` or :func:`from_decimal` for an exact decimal.
    - A ``bool`` is **rejected** — ``bool`` is an ``int`` subclass, so
      ``Fraction(True)`` would silently become ``1`` and turn a mistaken
      boolean into a numeric threshold.

    This enforces at runtime the rejection the Go / C++ / Rust signatures get
    for free at the type level, so neither a ``float`` nor a ``bool`` can enter
    via an untyped caller; both accepted arms are exact, so the value and its
    kernel-rendered description agree byte-for-byte across bindings. The single
    source of truth shared by the DSL predicate path
    (:func:`~aletheia.dsl.to_predicate_fraction`) and the client's signal-value
    path (``Client._resolve_signal_indices``).

    Raises:
        TypeError: *value* is a ``bool`` or a ``float``.

    """
    if isinstance(value, bool):
        msg = (
            "a boolean is not an exact numeric value; pass an int, a Fraction, or "
            "from_decimal('...') for an exact decimal (the float principle)"
        )
        raise TypeError(msg)
    if isinstance(value, float):
        msg = (
            "a float is not exact; pass an int, a Fraction, or from_decimal('...') "
            "for an exact decimal (the float principle)"
        )
        raise TypeError(msg)
    return Fraction(value)


def fraction_to_wire_pair(value: Fraction) -> tuple[int, int]:
    """Convert a Fraction to (numerator, denominator) for the binary frame FFI.

    Exact int64 numerator/denominator extraction required by the binary-frame
    endpoints (``aletheia_build_frame_bin`` / ``aletheia_update_frame_bin``,
    which take ``POINTER(c_int64)`` arrays): the Agda core works in ℚ and the
    wire carries int64 numerator/denominator pairs, so a Fraction flows through
    losslessly.

    Raises:
        ValidationError: If either component overflows the Int64 wire range.

    """
    n, d = value.numerator, value.denominator
    if not _INT64_MIN <= n <= _INT64_MAX or not _INT64_MIN <= d <= _INT64_MAX:
        msg = f"Fraction {value!r} components exceed int64 range"
        raise ValidationError(msg)
    return (n, d)


def extract_rational_from_dict(
    d: Mapping[str, JSONValue],
    context: str,
) -> tuple[int, int]:
    """Extract (numerator, denominator) from a rational dict.

    Raises ProtocolError if the dict is malformed or denominator is non-positive.
    Mirrors Go ``validateRational`` (rejects ``<= 0``) and the Agda kernel
    invariant that the denominator is a ``ℕ⁺``.  A negative denominator on
    the wire would otherwise be silently sign-flipped by ``Fraction(n, d)``,
    hiding the wire-format violation.
    """
    numerator = d.get("numerator")
    denominator = d.get("denominator")
    # is_pure_int rejects bool subclass so a malicious response
    # {"numerator": true, "denominator": false} cannot coerce to
    # Fraction(1, 0).  Mirrors the Go encoding/json + C++
    # nlohmann/json bool→int rejection contract.
    if not is_pure_int(numerator):
        msg = f"Expected {context}.numerator to be int"
        raise ProtocolError(msg)
    if not is_pure_int(denominator):
        msg = f"Expected {context}.denominator to be int"
        raise ProtocolError(msg)
    if denominator <= 0:
        msg = f"Expected {context}.denominator to be positive, got {denominator}"
        raise ProtocolError(msg)
    return numerator, denominator


def validate_integer_field(field_name: str, raw_value: object) -> int:
    """Validate + extract an integer-valued response field as ``int``.

    The field's Agda-side type is ``ℕ`` / ``ℤ`` (timestamps in microseconds,
    property indices); it arrives on the wire either as a plain int or as
    ``{"numerator": N, "denominator": 1}``, never with a fractional
    component.  Returns ``N``.  A non-unit denominator indicates a
    wire-format violation by the kernel and is rejected.
    """
    # is_pure_int over isinstance(raw_value, int) so a `true` on the wire
    # (json deserialised as Python bool) is rejected rather than silently
    # treated as numerator=1.
    if is_pure_int(raw_value):
        return raw_value
    if not is_str_dict(raw_value):
        msg = f"Expected {field_name} to be int or dict, got {type(raw_value).__name__}"
        raise ProtocolError(msg)
    numerator, denominator = extract_rational_from_dict(raw_value, field_name)
    if denominator != 1:
        msg = (
            f"Expected {field_name} to be an integer (denominator == 1), "
            f"got {numerator}/{denominator}"
        )
        raise ProtocolError(msg)
    return numerator


def decode_wire_rational(value_raw: object) -> Fraction:
    """Decode an exact rational from a core *response* (the internal wire).

    Computed values cross the FFI boundary as exact rationals only — a bare
    integer or a ``{"numerator": n, "denominator": d}`` object — never a float:
    a float on the wire would mean a computed value escaped the rational kernel.
    A float, string, or bool is therefore a wire-format violation, rejected here:
    nothing internal to the program is ever a float (a decimal is an exact
    rational, carried as an int or a {numerator, denominator} object).
    """
    if isinstance(value_raw, bool):
        # bool is an int subclass; reject so True/False can't slip through.
        msg = "Expected a wire rational (int or {numerator, denominator}), got bool"
        raise ProtocolError(msg)
    if isinstance(value_raw, int):
        return Fraction(value_raw)
    if is_str_dict(value_raw):
        n, d = extract_rational_from_dict(value_raw, "rational")
        return Fraction(n, d)
    msg = (
        "Expected a wire rational (int or {numerator, denominator}), "
        f"got {type(value_raw).__name__}"
    )
    raise ProtocolError(msg)
