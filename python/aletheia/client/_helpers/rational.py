# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""ℚ arithmetic + parsing + validation for the JSON / binary FFI wire."""

from __future__ import annotations

import math
from fractions import Fraction
from typing import TYPE_CHECKING

from aletheia._loader_utils import is_pure_int
from aletheia.client._types import ProtocolError, ValidationError
from aletheia.types import is_str_dict

if TYPE_CHECKING:
    from collections.abc import Mapping

    from aletheia.types import JSONValue

# Shared bounds and scaling factors for the binary FFI rational encoding.
# int64 bounds match the Haskell ``Int64`` numerator/denominator that the
# Agda core consumes; the decimal precision denominator mirrors the 10^9
# scaling that Agda's ``formatRational`` emits on the JSON path so the two
# wire formats stay bit-identical on round-trip.
_INT64_MAX = (1 << 63) - 1
_INT64_MIN = -(1 << 63)
_DECIMAL_PRECISION_DEN = 1_000_000_000
_RATIONAL_STR_PARTS = 2


def float_to_rational(value: float) -> tuple[int, int]:
    """Convert a float to (numerator, denominator) for binary FFI.

    Uses 10^9 scaling to match JSON decimal precision.
    The Haskell side normalizes to coprime form via GCD.

    Raises:
        ValidationError: If *value* is NaN, infinite, or too large for int64.

    """
    if math.isnan(value) or math.isinf(value):
        msg = f"Cannot convert {value!r} to rational"
        raise ValidationError(msg)
    numerator = round(value * _DECIMAL_PRECISION_DEN)
    # Guard against values that would overflow int64 in the binary FFI.
    # Use the full int64 range, not the 53-bit float mantissa bound — the
    # denominator is a compile-time constant ≤ int64 so any numerator that
    # fits int64 is safe to pack as ``<q`` little-endian.
    if not _INT64_MIN <= numerator <= _INT64_MAX:
        msg = f"signal value {value!r} too large for rational representation"
        raise ValidationError(msg)
    return (numerator, _DECIMAL_PRECISION_DEN)


def fraction_to_rational(value: Fraction) -> tuple[int, int]:
    """Convert a Fraction to (numerator, denominator) for binary FFI, lossless.

    Unlike float_to_rational this preserves exact precision — the Agda core
    works in ℚ and the wire format carries int64 numerator/denominator pairs,
    so Fractions flow through without the 10^9 quantization step.

    Raises:
        ValidationError: If either component overflows int64.

    """
    n, d = value.numerator, value.denominator
    if not _INT64_MIN <= n <= _INT64_MAX or not _INT64_MIN <= d <= _INT64_MAX:
        msg = f"Fraction {value!r} components exceed int64 range"
        raise ValidationError(msg)
    return (n, d)


def coerce_to_rational(value: float | Fraction) -> tuple[int, int]:
    """Convert a numeric signal input to (numerator, denominator).

    Uses Fraction's exact representation when the caller already has one;
    falls back to float_to_rational's 10^9 scaling for float inputs.
    """
    if isinstance(value, Fraction):
        return fraction_to_rational(value)
    return float_to_rational(value)


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


def _parse_rational_str(value_raw: str) -> Fraction | None:
    """Parse a rational from string form (``'n/d'`` or a plain numeric string).

    Returns the ``Fraction``, or ``None`` when the string is not parseable
    (the caller then raises the generic type error).  Raises
    :class:`ProtocolError` on a non-positive denominator in explicit
    ``'n/d'`` form.
    """
    if "/" in value_raw:
        parts = value_raw.split("/")
        if len(parts) == _RATIONAL_STR_PARTS:
            try:
                numerator_s = int(parts[0])
                denominator_s = int(parts[1])
            except ValueError:
                pass
            else:
                if denominator_s <= 0:
                    msg = f"Expected positive denominator in rational string, got {value_raw!r}"
                    raise ProtocolError(msg)
                return Fraction(numerator_s, denominator_s)
    try:
        return Fraction(value_raw)
    except ValueError, ZeroDivisionError:
        return None


def parse_rational(value_raw: object) -> Fraction:
    """Parse a value that may be a number, rational dict, or rational string.

    Returns a Fraction to preserve the Agda core's exact rational precision
    end-to-end — JSON rational dicts {"numerator": n, "denominator": d}
    become Fraction(n, d) with no float quantization.

    For legacy float inputs (rare — Agda's formatRational emits integers as
    ints and non-integers as rational dicts) we still go through Fraction,
    using its float-from-string heuristic to avoid binary float artifacts.
    """
    if isinstance(value_raw, bool):
        # bool is a subclass of int; reject explicitly to avoid True → Fraction(1)
        msg = "Expected signal value to be number, rational dict, or rational string, got bool"
        raise ProtocolError(msg)
    if isinstance(value_raw, int):
        return Fraction(value_raw)
    if isinstance(value_raw, float):
        if math.isnan(value_raw) or math.isinf(value_raw):
            msg = f"Cannot convert {value_raw!r} to rational"
            raise ProtocolError(msg)
        return Fraction(value_raw).limit_denominator(_DECIMAL_PRECISION_DEN)
    if is_str_dict(value_raw):
        n, d = extract_rational_from_dict(value_raw, "rational")
        return Fraction(n, d)
    if isinstance(value_raw, str):
        parsed = _parse_rational_str(value_raw)
        if parsed is not None:
            return parsed
    msg = (
        "Expected signal value to be number, rational dict, "
        f"or rational string, got {type(value_raw).__name__}"
    )
    raise ProtocolError(msg)
