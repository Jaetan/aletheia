"""Shared field accessors for YAML and Excel check loaders.

Both loaders need to extract typed fields from untyped dicts with
helpful error messages.  This module provides runtime-checked accessors
that raise ``ValueError`` with a caller-supplied context string.
"""

from typing import TypeGuard

from .protocols import is_str_dict


def is_str(val: object) -> TypeGuard[str]:
    """Type guard: value is a str."""
    return isinstance(val, str)


def get_str(d: dict[str, object], key: str, ctx: str) -> str:
    """Extract a required string field from *d*.

    Raises ``ValueError`` with *ctx* prefix if the key is missing or
    not a string.
    """
    val = d.get(key)
    if not isinstance(val, str):
        raise ValueError(f"{ctx}: missing or invalid '{key}' (expected string)")
    return val


def get_number(d: dict[str, object], key: str, ctx: str) -> float:
    """Extract a required numeric field from *d*.

    Booleans are rejected (``isinstance(True, int)`` is ``True`` in
    Python, but a boolean is not a number in check semantics).
    """
    val = d.get(key)
    if isinstance(val, (int, float)) and not isinstance(val, bool):
        return float(val)
    raise ValueError(f"{ctx}: missing or invalid '{key}' (expected number)")


def get_int(d: dict[str, object], key: str, ctx: str) -> int:
    """Extract a required integer field from *d*."""
    val = d.get(key)
    if isinstance(val, int) and not isinstance(val, bool):
        return val
    raise ValueError(f"{ctx}: missing or invalid '{key}' (expected integer)")


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
    raise ValueError(f"{ctx}: missing or invalid '{key}' (expected TRUE/FALSE)")


def get_dict(d: dict[str, object], key: str, ctx: str) -> dict[str, object]:
    """Extract a required dict field from *d*."""
    val = d.get(key)
    if not is_str_dict(val):
        raise ValueError(f"{ctx}: missing or invalid '{key}' (expected mapping)")
    return val
