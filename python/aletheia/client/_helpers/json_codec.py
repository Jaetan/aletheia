"""Protocol-level list parsers for the streaming response shape."""

from collections.abc import Sequence
from fractions import Fraction

from aletheia.client._helpers.rational import parse_rational
from aletheia.client._types import ProtocolError
from aletheia.protocols import is_str_dict


def parse_values_list(values_data: Sequence[object]) -> dict[str, Fraction]:
    """Parse signal values list from response."""
    values: dict[str, Fraction] = {}
    for item in values_data:
        if not is_str_dict(item):
            msg = f"Expected signal value to be dict, got {type(item)}"
            raise ProtocolError(msg)
        name_raw = item.get("name")
        if not isinstance(name_raw, str):
            msg = f"Expected signal name to be str, got {type(name_raw)}"
            raise ProtocolError(msg)
        value_raw = item.get("value")
        values[name_raw] = parse_rational(value_raw)
    return values


def parse_errors_list(errors_data: Sequence[object]) -> dict[str, str]:
    """Parse signal errors list from response."""
    errors: dict[str, str] = {}
    for item in errors_data:
        if not is_str_dict(item):
            msg = f"Expected error item to be dict, got {type(item)}"
            raise ProtocolError(msg)
        name_raw = item.get("name")
        if not isinstance(name_raw, str):
            msg = f"Expected error signal name to be str, got {type(name_raw)}"
            raise ProtocolError(msg)
        error_raw = item.get("error")
        if not isinstance(error_raw, str):
            msg = f"Expected error message to be str, got {type(error_raw)}"
            raise ProtocolError(msg)
        errors[name_raw] = error_raw
    return errors


def parse_absent_list(absent_data: Sequence[object]) -> list[str]:
    """Parse absent signals list from response."""
    absent: list[str] = []
    for item in absent_data:
        if not isinstance(item, str):
            msg = f"Expected absent signal name to be str, got {type(item)}"
            raise ProtocolError(msg)
        absent.append(item)
    return absent
