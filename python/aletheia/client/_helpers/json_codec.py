# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Readers of the three arrays an extraction reply writes at its root."""

from typing import TYPE_CHECKING, Final

from aletheia.client._helpers.reply_shape import (
    A_RATIONAL,
    OBJECT,
    STRING,
    ReplyPath,
    at,
    came,
    came_as,
    read_rational,
    reply_refusal,
)
from aletheia.types import is_str_dict

if TYPE_CHECKING:
    from collections.abc import Sequence
    from fractions import Fraction

    from aletheia.types import JSONValue

_VALUES: Final = ReplyPath("values")
_ERRORS: Final = ReplyPath("errors")
_ABSENT: Final = ReplyPath("absent")


def parse_values_list(values_data: Sequence[JSONValue]) -> dict[str, Fraction]:
    """Read the ``values`` array: objects with a string ``name`` and a rational ``value``.

    Raises:
        ProtocolError: If an entry, its ``name`` or its ``value`` is not what
            the kernel writes there.

    """
    values: dict[str, Fraction] = {}
    for item in values_data:
        if not is_str_dict(item):
            raise reply_refusal(_VALUES, OBJECT, came_as(item))
        name_raw = item.get("name")
        if not isinstance(name_raw, str):
            raise reply_refusal(at(_VALUES, "name"), STRING, came(item, "name"))
        if "value" not in item:
            raise reply_refusal(at(_VALUES, "value"), A_RATIONAL, came(item, "value"))
        values[name_raw] = read_rational(item["value"], at(_VALUES, "value"))
    return values


def parse_errors_list(errors_data: Sequence[JSONValue]) -> dict[str, str]:
    """Read the ``errors`` array: each entry an object with a string ``name`` and ``error``.

    Raises:
        ProtocolError: If an entry, its ``name`` or its ``error`` is not what
            the kernel writes there.

    """
    errors: dict[str, str] = {}
    for item in errors_data:
        if not is_str_dict(item):
            raise reply_refusal(_ERRORS, OBJECT, came_as(item))
        name_raw = item.get("name")
        if not isinstance(name_raw, str):
            raise reply_refusal(at(_ERRORS, "name"), STRING, came(item, "name"))
        error_raw = item.get("error")
        if not isinstance(error_raw, str):
            raise reply_refusal(at(_ERRORS, "error"), STRING, came(item, "error"))
        errors[name_raw] = error_raw
    return errors


def parse_absent_list(absent_data: Sequence[JSONValue]) -> list[str]:
    """Read the ``absent`` array: each entry a signal's name, a string.

    Raises:
        ProtocolError: If an entry is not a string.

    """
    absent: list[str] = []
    for item in absent_data:
        if not isinstance(item, str):
            raise reply_refusal(_ABSENT, STRING, came_as(item))
        absent.append(item)
    return absent
