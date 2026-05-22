"""Protocol-level list parsers for the streaming response shape."""

from collections.abc import Sequence
from fractions import Fraction

from ...protocols import is_str_dict
from .._types import ProtocolError
from .rational import parse_rational


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
