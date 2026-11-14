# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""ℚ arithmetic + parsing + validation for the JSON / binary FFI wire."""

from __future__ import annotations

import ctypes
from fractions import Fraction
from typing import NewType, TypeGuard

from aletheia.client._ffi import (
    AletheiaDecimal,
    AletheiaText,
    AletheiaTimeBound,
    started_library,
    take_error_envelope,
    uint128_value,
)
from aletheia.client._refusal import raise_entry_refusal
from aletheia.client._types import (
    InputBoundExceededError,
    KernelRefusal,
    ValidationError,
)
from aletheia.codes import ErrorCode
from aletheia.common_types import Microseconds, Prose
from aletheia.limits import (
    BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
    MAX_RATIONAL_COMPONENT_MAGNITUDE,
    BoundField,
)

# A time window's text, whole microseconds as a loader's document spells them.
TimeBoundText = NewType("TimeBoundText", str)

# The part of a build a value wider than its wire slot names, as the kernel
# names the part of a JSON number past the bound.
_SIGNAL_VALUE_FIELD = BoundField("signal value")


def is_pure_int(v: object) -> TypeGuard[int]:
    """Type guard: value is an ``int`` and not a ``bool`` subclass.

    Python's ``bool`` is a subclass of ``int`` (``isinstance(True, int)``
    returns ``True``), so plain ``isinstance(v, int)`` is insufficient
    for "is this a numeric integer?" checks.  This guard rejects bools
    while accepting all other ``int`` values.  The whole-number reply checks
    of ``dbc_normalize`` and ``_response_parsers`` use it.
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
    consumed).  Mirrors Go ``FromDecimal`` / C++ ``Rational::from_decimal`` /
    Rust ``Rational::from_decimal`` exactly.

    Like rational *display* (:func:`~aletheia.client._enrichment.format_rational`),
    decimal parsing needs the GHC runtime up and is **vocal**: it never starts
    the runtime, since a start fixes the core count for the process, so it
    raises before the FFI call while the runtime is down.  A program that reads
    a decimal before opening a client calls :func:`~aletheia.start_runtime`
    first.

    A refusal is the kernel's error, decoded by the decoder the binary-output
    entries use (:func:`raise_entry_refusal`): a refused literal is the
    caller's own text, so it is a :class:`ValidationError` carrying the
    kernel's ``code``, and a component past the bound the typed bound error.

    Raises:
        FFIError: the GHC runtime is not started (no
            :func:`~aletheia.start_runtime` and no client).
        InputBoundExceededError: a component of the exact rational is past
            the kernel's rational component magnitude bound (the kernel's
            ``input_bound_exceeded`` refusal, ``field`` ``"decimal"``).
        ValidationError: the literal was refused, its ``code`` saying how:
            ``text_parse_failure`` when the grammar matched nothing and
            ``text_trailing_input`` when input remains after a literal, each
            carrying the kernel's position in its message, or
            ``ffi_validation_error`` when the shim refused the text before the
            kernel read it (a NUL byte, or a lone surrogate, the one text a
            ``str`` holds that is not UTF-8).
        ProtocolError: the FFI answered a failure without an envelope or with
            a malformed one (an ABI / kernel malfunction).

    """
    lib = started_library(Prose("parsing decimals"))
    out = AletheiaDecimal()
    # A lone surrogate reaches the shim as the bytes ``surrogatepass`` writes,
    # which are not UTF-8, so the shim refuses it as it refuses such bytes from
    # every binding; every other ``str`` encodes as plain UTF-8.
    raw = s.encode(errors="surrogatepass")
    text = AletheiaText(raw, len(raw))
    if lib.aletheia_parse_decimal(ctypes.byref(text), ctypes.byref(out)) != 0:
        missing = Prose("aletheia_parse_decimal failed without an error")
        raise_entry_refusal(take_error_envelope(lib, out, missing), error=ValidationError)
    return decimal_value(out)


def parse_time_bound(s: TimeBoundText) -> Microseconds:
    """Read a time window's text as the whole microseconds the kernel reads it as.

    The kernel reads *s* as :func:`from_decimal` reads a decimal, then as it
    reads a property's time bound: a whole, non-negative number of
    microseconds at most 2^64-1.  Vocal, as :func:`from_decimal` is: it never
    starts the runtime.

    Raises:
        FFIError: the GHC runtime is not started (no
            :func:`~aletheia.start_runtime` and no client).
        InputBoundExceededError: the number is past 2^64-1 (``field``
            ``"time bound"``), or a component of the decimal is past the
            rational bound (``field`` ``"decimal"``).
        ValidationError: the text was refused, its ``code`` saying how: a text
            that is no decimal as :func:`from_decimal` refuses it, or
            ``handler_property_refused`` for a negative or fractional
            number (``timebound -1500 is negative``, ``timebound 1.5 is not a
            whole number``).

    """
    lib = started_library(Prose("reading a time bound"))
    out = AletheiaTimeBound()
    raw = s.encode(errors="surrogatepass")
    text = AletheiaText(raw, len(raw))
    if lib.aletheia_parse_time_bound(ctypes.byref(text), ctypes.byref(out)) != 0:
        missing = Prose("aletheia_parse_time_bound failed without an error")
        raise_entry_refusal(take_error_envelope(lib, out, missing), error=ValidationError)
    microseconds: Microseconds = out.microseconds
    return microseconds


def decimal_value(out: AletheiaDecimal) -> Fraction:
    """Read the rational the decimal entry answered into *out*.

    The kernel proves its answer lowest terms over a positive denominator, so
    the parts are read as written.  Any sign byte but 0 is negative, as the
    header reads one.
    """
    value = Fraction(uint128_value(out.value.numerator), uint128_value(out.value.denominator))
    negative: int = out.value.negative
    return -value if negative else value


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


def reject_inexact(value: object, ctx: str) -> None:
    """Reject a non-exact value (a ``float`` or ``bool``) at an outbound *rational* wire field.

    The outbound twin of
    :func:`~aletheia.client._helpers.reply_shape.read_rational`, applied at exactly the
    fields the Agda kernel parses as ℚ — signal ``factor``/``offset``/``minimum``/
    ``maximum``, env-var ``initial``/``minimum``/``maximum``, *float-kind*
    attribute ``min``/``max``/``value``, and predicate
    ``value``/``min``/``max``/``delta``/``tolerance``.  A ``float`` there is
    silently absorbed by the kernel's decimal parser as an exact-but-*wrong*
    rational (``0.1 + 0.2`` → ``0.30000000000000004``, which ``json.dumps`` emits
    verbatim and the kernel reads as ``30000000000000004 / 10**17``); a ``bool``
    is not a numeric value.

    Applied *only* at rational fields — integer wire fields (``multiplex_values``,
    ``startBit``, ``dlc``, ``id``, value-table values, int/hex attribute bounds…)
    are left to the kernel's own typed validation, which rejects a non-integer
    there loudly (e.g. ``parse_non_integer_multiplex_value``) rather than
    silently.  The reply readers likewise read only the rational fields as
    rationals.

    Args:
        value: The single field value to check.
        ctx: A short label for *value*'s location, used in the error message.

    Raises:
        ValidationError: *value* is a ``float`` or a ``bool``.

    """
    if isinstance(value, bool):
        msg = (
            f"{ctx}: a bool is not an exact numeric value; pass an int, a Fraction, "
            "or from_decimal('...') for an exact decimal (the float principle)"
        )
        raise ValidationError(msg)
    if isinstance(value, float):
        msg = (
            f"{ctx}: a float ({value!r}) is not exact and must not reach the wire; "
            "pass an int, a Fraction, or from_decimal('...') for an exact decimal "
            "(the float principle)"
        )
        raise ValidationError(msg)


def check_wire_bound(value: Fraction) -> None:
    """Refuse a signal value the binary frame FFI's slots cannot hold.

    The binary-frame endpoints (``aletheia_build_frame_bin`` /
    ``aletheia_update_frame_bin``) take each value as a sign and two unsigned
    128-bit magnitudes, so a Fraction whose components fit flows through
    losslessly.  A wider one would be truncated by ctypes, so it is refused
    before packing, as the kernel refuses a JSON number past the bound: the
    magnitude it measured is past the reported ceiling, so the refusal names
    only the limit.

    Raises:
        InputBoundExceededError: the numerator's magnitude or the denominator
            exceeds :data:`~aletheia.limits.MAX_RATIONAL_COMPONENT_MAGNITUDE`
            (``field`` ``"signal value"``).

    """
    n, d = value.numerator, value.denominator
    if max(abs(n), d) > MAX_RATIONAL_COMPONENT_MAGNITUDE:
        message = Prose(
            f"{_SIGNAL_VALUE_FIELD}: rational component magnitude exceeds limit "
            + f"{MAX_RATIONAL_COMPONENT_MAGNITUDE}"
        )
        raise InputBoundExceededError(
            BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
            MAX_RATIONAL_COMPONENT_MAGNITUDE,
            MAX_RATIONAL_COMPONENT_MAGNITUDE,
            code=ErrorCode.INPUT_BOUND_EXCEEDED,
            refusal=KernelRefusal(message, _SIGNAL_VALUE_FIELD),
        )
