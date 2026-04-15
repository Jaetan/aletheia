"""Pure helper functions for response parsing and type conversion."""

import json
import math
from collections.abc import Sequence
from fractions import Fraction
from typing import cast, override

from ..protocols import (
    DBCDefinition,
    DBCSignal,
    DBCMessage,
    RationalNumber,
    is_str_dict,
    is_object_list,
)
from ._types import ProtocolError

# Fields in a DBCSignal that Agda serializes as JNumber (may be rational dict)
_NUMERIC_SIGNAL_FIELDS = ("factor", "offset", "minimum", "maximum")


class FractionJSONEncoder(json.JSONEncoder):
    """JSONEncoder that serializes Fraction as {"numerator": n, "denominator": d}.

    Matches Agda's rational wire format — parseRational accepts integer
    literals, rational dicts, and decimal floats, so this preserves exact
    precision on any DBCDefinition round-trip path.
    """

    @override
    def default(self, o: object) -> object:
        if isinstance(o, Fraction):
            return {"numerator": o.numerator, "denominator": o.denominator}
        return super().default(o)


def dump_json(value: object, *, indent: int | None = None) -> str:
    """Serialize *value* to JSON, handling Fraction via FractionJSONEncoder."""
    return json.dumps(value, cls=FractionJSONEncoder, indent=indent)


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
        ValueError: If *value* is NaN, infinite, or too large for int64.
    """
    if math.isnan(value) or math.isinf(value):
        raise ValueError(f"Cannot convert {value!r} to rational")
    numerator = round(value * _DECIMAL_PRECISION_DEN)
    # Guard against values that would overflow int64 in the binary FFI.
    # Use the full int64 range, not the 53-bit float mantissa bound — the
    # denominator is a compile-time constant ≤ int64 so any numerator that
    # fits int64 is safe to pack as ``<q`` little-endian.
    if not _INT64_MIN <= numerator <= _INT64_MAX:
        raise ValueError(
            f"signal value {value!r} too large for rational representation"
        )
    return (numerator, _DECIMAL_PRECISION_DEN)


def fraction_to_rational(value: Fraction) -> tuple[int, int]:
    """Convert a Fraction to (numerator, denominator) for binary FFI, lossless.

    Unlike float_to_rational this preserves exact precision — the Agda core
    works in ℚ and the wire format carries int64 numerator/denominator pairs,
    so Fractions flow through without the 10^9 quantization step.

    Raises:
        ValueError: If either component overflows int64.
    """
    n, d = value.numerator, value.denominator
    if not _INT64_MIN <= n <= _INT64_MAX or not _INT64_MIN <= d <= _INT64_MAX:
        raise ValueError(
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


def to_signal_fraction(value: float | int | Fraction) -> Fraction:
    """Convert a decimal-intent numeric input to a Fraction for DBCSignal fields.

    Floats are bounded via ``limit_denominator(1_000_000_000)`` so that
    decimal inputs like ``0.1`` become ``1/10`` exactly rather than the
    IEEE-754 approximation's monstrous denominator.  Int and existing
    Fraction inputs flow through unchanged.
    """
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        return Fraction(value)
    return Fraction(value).limit_denominator(_DECIMAL_PRECISION_DEN)


def extract_rational_from_dict(
    d: dict[str, object], context: str,
) -> tuple[int, int]:
    """Extract (numerator, denominator) from a rational dict.

    Raises ProtocolError if the dict is malformed or denominator is zero.
    """
    numerator = d.get("numerator")
    denominator = d.get("denominator")
    if not isinstance(numerator, int):
        raise ProtocolError(f"Expected {context}.numerator to be int")
    if not isinstance(denominator, int):
        raise ProtocolError(f"Expected {context}.denominator to be int")
    if denominator == 0:
        raise ProtocolError(f"Expected {context}.denominator to be nonzero")
    return numerator, denominator


def validate_rational(field_name: str, raw_value: object) -> RationalNumber:
    """Validate and extract RationalNumber from response field."""
    if isinstance(raw_value, int):
        return {"numerator": raw_value, "denominator": 1}
    if not is_str_dict(raw_value):
        raise ProtocolError(
            f"Expected {field_name} to be int or dict, got {type(raw_value).__name__}"
        )
    n, d = extract_rational_from_dict(raw_value, field_name)
    return {"numerator": n, "denominator": d}


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
                    if denominator_s == 0:
                        raise ProtocolError(
                            f"Division by zero in rational string: {value_raw!r}"
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


def normalize_signal(raw_sig: dict[str, object]) -> DBCSignal:
    """Normalize a single Agda signal dict into a DBCSignal."""
    sig: dict[str, object] = dict(raw_sig)
    for field in _NUMERIC_SIGNAL_FIELDS:
        if field in sig:
            sig[field] = parse_rational(sig[field])
    return cast(DBCSignal, sig)


def normalize_dbc(raw: dict[str, object]) -> DBCDefinition:
    """Normalize Agda's formatDBC JSON into a proper DBCDefinition.

    Agda's ``formatRational`` encodes non-integer rationals as
    ``{"numerator": n, "denominator": d}`` dicts. This method
    converts those to ``Fraction`` so the result matches the
    ``DBCDefinition`` TypedDict and preserves the core's exact
    rational precision end-to-end.
    """
    raw_messages = raw.get("messages")
    if not is_object_list(raw_messages):
        raise ProtocolError("Expected 'messages' to be a list")
    messages: list[DBCMessage] = []
    for m in raw_messages:
        if not is_str_dict(m):
            raise ProtocolError("Expected each message to be a dict")
        raw_signals = m.get("signals")
        if not is_object_list(raw_signals):
            raise ProtocolError("Expected 'signals' to be a list")
        signals: list[DBCSignal] = []
        for s in raw_signals:
            if not is_str_dict(s):
                raise ProtocolError("Expected each signal to be a dict")
            signals.append(normalize_signal(s))
        msg: dict[str, object] = dict(m)
        msg["signals"] = signals
        messages.append(cast(DBCMessage, msg))
    return {
        "version": str(raw.get("version", "")),
        "messages": messages,
    }


def parse_values_list(values_data: Sequence[object]) -> dict[str, Fraction]:
    """Parse signal values list from response."""
    values: dict[str, Fraction] = {}
    for item in values_data:
        if not is_str_dict(item):
            raise ProtocolError(f"Expected signal value to be dict, got {type(item)}")
        name_raw = item.get("name")
        if not isinstance(name_raw, str):
            raise ProtocolError(f"Expected signal name to be str, got {type(name_raw)}")
        value_raw = item.get("value")
        values[name_raw] = parse_rational(value_raw)
    return values


def parse_errors_list(errors_data: Sequence[object]) -> dict[str, str]:
    """Parse signal errors list from response."""
    errors: dict[str, str] = {}
    for item in errors_data:
        if not is_str_dict(item):
            raise ProtocolError(f"Expected error item to be dict, got {type(item)}")
        name_raw = item.get("name")
        if not isinstance(name_raw, str):
            raise ProtocolError(f"Expected error signal name to be str, got {type(name_raw)}")
        error_raw = item.get("error")
        if not isinstance(error_raw, str):
            raise ProtocolError(f"Expected error message to be str, got {type(error_raw)}")
        errors[name_raw] = error_raw
    return errors


def parse_absent_list(absent_data: Sequence[object]) -> list[str]:
    """Parse absent signals list from response."""
    absent: list[str] = []
    for item in absent_data:
        if not isinstance(item, str):
            raise ProtocolError(f"Expected absent signal name to be str, got {type(item)}")
        absent.append(item)
    return absent
