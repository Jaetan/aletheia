"""ℚ arithmetic + parsing + validation for the JSON / binary FFI wire."""

import math
from fractions import Fraction

from ..._loader_utils import is_pure_int
from ...protocols import RationalNumber, is_str_dict
from .._types import ProtocolError, ValidationError

# Shared bounds and scaling factors for the binary FFI rational encoding.
# int64 bounds match the Haskell ``Int64`` numerator/denominator that the
# Agda core consumes; the decimal precision denominator mirrors the 10^9
# scaling that Agda's ``formatRational`` emits on the JSON path so the two
# wire formats stay bit-identical on round-trip.
_INT64_MAX = (1 << 63) - 1
_INT64_MIN = -(1 << 63)
_DECIMAL_PRECISION_DEN = 1_000_000_000


def float_to_rational(value: float) -> tuple[int, int]:
    """Convert a float to (numerator, denominator) for binary FFI.

    Uses 10^9 scaling to match JSON decimal precision.
    The Haskell side normalizes to coprime form via GCD.

    Raises:
        ValidationError: If *value* is NaN, infinite, or too large for int64.
    """
    if math.isnan(value) or math.isinf(value):
        raise ValidationError(f"Cannot convert {value!r} to rational")
    numerator = round(value * _DECIMAL_PRECISION_DEN)
    # Guard against values that would overflow int64 in the binary FFI.
    # Use the full int64 range, not the 53-bit float mantissa bound — the
    # denominator is a compile-time constant ≤ int64 so any numerator that
    # fits int64 is safe to pack as ``<q`` little-endian.
    if not _INT64_MIN <= numerator <= _INT64_MAX:
        raise ValidationError(
            f"signal value {value!r} too large for rational representation"
        )
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
        raise ValidationError(
            f"Fraction {value!r} components exceed int64 range"
        )
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
    d: dict[str, object], context: str,
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
    # PY-B-8.1 (R21): is_pure_int rejects bool subclass so a malicious
    # response {"numerator": true, "denominator": false} cannot coerce
    # to Fraction(1, 0).  Mirrors the Go encoding/json + C++
    # nlohmann/json bool→int rejection contract.
    if not is_pure_int(numerator):
        raise ProtocolError(f"Expected {context}.numerator to be int")
    if not is_pure_int(denominator):
        raise ProtocolError(f"Expected {context}.denominator to be int")
    if denominator <= 0:
        raise ProtocolError(
            f"Expected {context}.denominator to be positive, got {denominator}"
        )
    return numerator, denominator


def validate_rational(field_name: str, raw_value: object) -> RationalNumber:
    """Validate and extract RationalNumber from response field."""
    # PY-B-8.1 (R21): is_pure_int over isinstance(raw_value, int) so a
    # `true` on the wire (json deserialised as Python bool) is rejected
    # rather than silently treated as numerator=1.
    if is_pure_int(raw_value):
        return {"numerator": raw_value, "denominator": 1}
    if not is_str_dict(raw_value):
        raise ProtocolError(
            f"Expected {field_name} to be int or dict, got {type(raw_value).__name__}"
        )
    n, d = extract_rational_from_dict(raw_value, field_name)
    return {"numerator": n, "denominator": d}


def validate_integer_rational(field_name: str, raw_value: object) -> RationalNumber:
    """Validate a RationalNumber response field that must be integer-valued.

    Same as :func:`validate_rational` plus a post-parse assertion that the
    denominator is exactly ``1``.  Used for fields whose Agda-side type is
    ``ℕ`` or ``ℤ`` (timestamps in microseconds, property indices) — they
    arrive on the wire as a plain int or as ``{"numerator": N,
    "denominator": 1}``, never with a fractional component.  A non-unit
    denominator indicates a wire-format violation by the kernel.
    """
    rational = validate_rational(field_name, raw_value)
    if rational["denominator"] != 1:
        raise ProtocolError(
            f"Expected {field_name} to be an integer (denominator == 1), "
            + f"got {rational['numerator']}/{rational['denominator']}"
        )
    return rational


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
        raise ProtocolError(
            "Expected signal value to be number, rational dict, "
            + "or rational string, got bool"
        )
    if isinstance(value_raw, int):
        return Fraction(value_raw)
    if isinstance(value_raw, float):
        if math.isnan(value_raw) or math.isinf(value_raw):
            raise ProtocolError(f"Cannot convert {value_raw!r} to rational")
        return Fraction(value_raw).limit_denominator(_DECIMAL_PRECISION_DEN)
    if is_str_dict(value_raw):
        n, d = extract_rational_from_dict(value_raw, "rational")
        return Fraction(n, d)
    if isinstance(value_raw, str):
        if "/" in value_raw:
            parts = value_raw.split("/")
            if len(parts) == 2:
                try:
                    numerator_s = int(parts[0])
                    denominator_s = int(parts[1])
                except ValueError:
                    pass
                else:
                    if denominator_s <= 0:
                        raise ProtocolError(
                            f"Expected positive denominator in rational string, got {value_raw!r}"
                        )
                    return Fraction(numerator_s, denominator_s)
        try:
            return Fraction(value_raw)
        except (ValueError, ZeroDivisionError):
            pass
    raise ProtocolError(
        "Expected signal value to be number, rational dict, "
        + f"or rational string, got {type(value_raw).__name__}"
    )
