# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared field accessors and path-hardening helpers for the YAML and Excel loaders.

Both loaders need to (a) extract typed fields from untyped dicts with
helpful error messages, and (b) reject adversarial loader inputs
(symlinks, oversize files) before yaml-cpp / openpyxl gets a chance to
explode or exhaust memory.  This module provides both surfaces.
"""

import os
import stat
from typing import TYPE_CHECKING, TypeGuard

# DEFERRED:
# Finding: `is_str_dict` (in protocols/_dbc_types.py) and `is_object_list`
#   (in this module, definition below) are internal TypeGuard helpers exposed
#   publicly via no-underscore naming.  Project-internal usage only.
# Why: Mechanical rename + import-site update across ~10 call sites;
#   gain is small (linter/dev-tooling clarity).
# Revisit when: First external user lands, OR a `python -m aletheia._loader_utils`
#   discovery surfaces the helpers as confusing public API.
# Direct sub-module import avoids re-entering ``client/__init__.py`` when
# this module is loaded transitively from ``client._helpers`` during package
# initialization (would deadlock on a partially-initialized ``aletheia.client``).
from aletheia.client._types import ValidationError
from aletheia.protocols import is_str_dict

if TYPE_CHECKING:
    from pathlib import Path


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
        msg = f"{ctx}: missing or invalid '{key}' (expected string)"
        raise ValidationError(msg)
    return val


def get_number(d: dict[str, object], key: str, ctx: str) -> float:
    """Extract a required numeric field from *d*.

    Booleans are rejected (``isinstance(True, int)`` is ``True`` in
    Python, but a boolean is not a number in check semantics).
    """
    val = d.get(key)
    if isinstance(val, (int, float)) and not isinstance(val, bool):
        return float(val)
    msg = f"{ctx}: missing or invalid '{key}' (expected number)"
    raise ValidationError(msg)


def get_int(d: dict[str, object], key: str, ctx: str) -> int:
    """Extract a required integer field from *d*."""
    val = d.get(key)
    if is_pure_int(val):
        return val
    msg = f"{ctx}: missing or invalid '{key}' (expected integer)"
    raise ValidationError(msg)


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
    msg = f"{ctx}: missing or invalid '{key}' (expected TRUE/FALSE)"
    raise ValidationError(msg)


def get_dict(d: dict[str, object], key: str, ctx: str) -> dict[str, object]:
    """Extract a required dict field from *d*."""
    val = d.get(key)
    if not is_str_dict(val):
        msg = f"{ctx}: missing or invalid '{key}' (expected mapping)"
        raise ValidationError(msg)
    return val


# ===========================================================================
# Path-hardening helper (cross-binding mirror)
# ===========================================================================


def reject_symlink_loader_path(p: Path, kind: str) -> None:
    """Reject *p* if it is a symbolic link.

    Mirrors the C++ ``aletheia::detail::validate_loader_path`` symlink
    rejection.  Cross-binding parity per
    ``feedback_cross_language_parity.md``: if the C++ binding refuses a
    symlinked .xlsx / .yaml, the Python binding does too.

    *kind* is interpolated into the error message ("Excel" / "YAML") so
    operators see which loader rejected the path.

    Canonicalisation would FOLLOW the link, defeating the check, so we
    use ``os.lstat`` and refuse outright.  Callers passing legitimate
    symlinks must resolve them first (``Path(link).resolve()``).

    Raises:
        ValidationError: *p* exists but is a symbolic link.

    """
    link_st = os.lstat(p)
    if stat.S_ISLNK(link_st.st_mode):
        raise ValidationError(
            f"{kind} file is a symbolic link; refusing to load: {p}."
            + "  Resolve the link and pass the real path explicitly."
        )
