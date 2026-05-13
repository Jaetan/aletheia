"""Shared field accessors for YAML and Excel check loaders.

Both loaders need to extract typed fields from untyped dicts with
helpful error messages.  This module provides runtime-checked accessors
that raise :class:`aletheia.ValidationError` with a caller-supplied
context string.
"""

from typing import TypeGuard

# Direct sub-module import avoids re-entering ``client/__init__.py`` when
# this module is loaded transitively from ``client._helpers`` during package
# initialization (would deadlock on a partially-initialized ``aletheia.client``).
from .client._types import ValidationError
from .protocols import is_str_dict


def is_str(val: object) -> TypeGuard[str]:
    """Type guard: value is a str."""
    return isinstance(val, str)


def is_pure_int(v: object) -> TypeGuard[int]:
    """Type guard: value is an ``int`` and not a ``bool`` subclass.

    Python's ``bool`` is a subclass of ``int`` (``isinstance(True, int)``
    returns ``True``), so plain ``isinstance(v, int)`` is insufficient
    for "is this a numeric integer?" checks.  This guard rejects bools
    while accepting all other ``int`` values.
    """
    return isinstance(v, int) and not isinstance(v, bool)


def get_str(d: dict[str, object], key: str, ctx: str) -> str:
    """Extract a required string field from *d*.

    Raises :class:`ValidationError` with *ctx* prefix if the key is
    missing or not a string.
    """
    val = d.get(key)
    if not isinstance(val, str):
        raise ValidationError(f"{ctx}: missing or invalid '{key}' (expected string)")
    return val


def get_number(d: dict[str, object], key: str, ctx: str) -> float:
    """Extract a required numeric field from *d*.

    Booleans are rejected (``isinstance(True, int)`` is ``True`` in
    Python, but a boolean is not a number in check semantics).
    """
    val = d.get(key)
    if isinstance(val, (int, float)) and not isinstance(val, bool):
        return float(val)
    raise ValidationError(f"{ctx}: missing or invalid '{key}' (expected number)")


def get_int(d: dict[str, object], key: str, ctx: str) -> int:
    """Extract a required integer field from *d*."""
    val = d.get(key)
    if is_pure_int(val):
        return val
    raise ValidationError(f"{ctx}: missing or invalid '{key}' (expected integer)")


def get_bool(d: dict[str, object], key: str, ctx: str) -> bool:
    """Extract a required boolean field from *d*.

    Accepts Python bools, integers ``1``/``0`` (Excel data_only mode),
    and the strings ``"TRUE"``/``"FALSE"`` (Excel text export).
    """
    val = d.get(key)
    if isinstance(val, bool):
        return val
    if isinstance(val, int):
        if val == 1:
            return True
        if val == 0:
            return False
    if isinstance(val, str):
        upper = val.upper()
        if upper == "TRUE":
            return True
        if upper == "FALSE":
            return False
    raise ValidationError(f"{ctx}: missing or invalid '{key}' (expected TRUE/FALSE)")


def get_dict(d: dict[str, object], key: str, ctx: str) -> dict[str, object]:
    """Extract a required dict field from *d*."""
    val = d.get(key)
    if not is_str_dict(val):
        raise ValidationError(f"{ctx}: missing or invalid '{key}' (expected mapping)")
    return val
