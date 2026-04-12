"""Pure helper functions for response parsing and type conversion."""

from __future__ import annotations

from collections.abc import Sequence
from typing import cast

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


def float_to_rational(value: float) -> tuple[int, int]:
    """Convert a float to (numerator, denominator) for binary FFI.

    Uses 10^9 scaling to match JSON decimal precision.
    The Haskell side normalizes to coprime form via GCD.
    """
    numerator = round(value * 1_000_000_000)
    return (numerator, 1_000_000_000)


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


def parse_rational(value_raw: object) -> float:
    """Parse a value that may be a number, rational dict, or rational string."""
    if isinstance(value_raw, (int, float)):
        return float(value_raw)
    if is_str_dict(value_raw):
        n, d = extract_rational_from_dict(value_raw, "rational")
        return n / d
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
                    return numerator_s / denominator_s
        try:
            return float(value_raw)
        except ValueError:
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
    converts those to ``float`` so the result matches the
    ``DBCDefinition`` TypedDict (where numeric fields are ``float``).
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


def parse_values_list(values_data: Sequence[object]) -> dict[str, float]:
    """Parse signal values list from response."""
    values: dict[str, float] = {}
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
