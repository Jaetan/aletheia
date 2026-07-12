# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared field accessors and path-hardening helpers for the YAML and Excel loaders.

Both loaders need to (a) extract typed fields from untyped dicts with
helpful error messages, and (b) reject adversarial loader inputs
(symlinks, oversize files) before yaml-cpp / openpyxl gets a chance to
explode or exhaust memory.  This module provides both surfaces.
"""

from __future__ import annotations

import os
import stat
from fractions import Fraction
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
from aletheia.client._helpers.rational import from_decimal, is_pure_int
from aletheia.client._types import ValidationError

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

    from aletheia.types import JSONValue


def is_str(val: object) -> TypeGuard[str]:
    """Type guard: value is a str."""
    return isinstance(val, str)


def get_str(d: Mapping[str, JSONValue], key: str, ctx: str) -> str:
    """Extract a required string field from *d*.

    Raises :class:`ValidationError` with *ctx* prefix if the key is
    missing or not a string.
    """
    val = d.get(key)
    if not isinstance(val, str):
        msg = f"{ctx}: missing or invalid '{key}' (expected string)"
        raise ValidationError(msg)
    return val


def get_number(d: Mapping[str, JSONValue], key: str, ctx: str) -> Fraction:
    """Extract a required numeric field from *d* as an exact rational.

    The float principle: no float ever materialises.  An integer is
    read exactly (``Fraction(n)``); a decimal arrives as its original STRING
    (YAML's float resolver is disabled; Excel uses the all-text contract) and
    is parsed exactly via the kernel SSOT :func:`~aletheia.from_decimal`.  A
    ``float`` cell is **rejected** with a "format it as TEXT" message — a
    spreadsheet number cell stores a lossy IEEE-754 double.  Booleans are
    rejected (``isinstance(True, int)`` is ``True``, but a boolean is not a
    number).  Mirrors Rust ``get_rational`` / Go / C++.

    Decimal parsing is RTS-gated (see :func:`~aletheia.from_decimal`).
    """
    val = d.get(key)
    if is_pure_int(val):
        return Fraction(val)
    if isinstance(val, str):
        try:
            return from_decimal(val.strip())
        except ValidationError as exc:
            # Re-raise with the field context the loaders carry everywhere else,
            # preserving the kernel's precise decimal_parse_failed/overflow reason.
            msg = f"{ctx}: invalid '{key}': {exc}"
            raise ValidationError(msg) from exc
    if isinstance(val, float):
        msg = (
            f"{ctx}: '{key}' is a number cell; format it as TEXT so the exact value "
            "is preserved (a number cell stores a lossy float)"
        )
        raise ValidationError(msg)
    msg = f"{ctx}: missing or invalid '{key}' (expected number)"
    raise ValidationError(msg)


def get_int(d: Mapping[str, JSONValue], key: str, ctx: str) -> int:
    """Extract a required integer field from *d*.

    An integer cell is accepted directly.  A text cell (the Excel all-text
    contract) is parsed exactly via :func:`~aletheia.from_decimal` and must be
    whole (unit denominator).  A ``float`` cell is **rejected** with a "format
    it as TEXT" message (a number cell stores a lossy double).  Mirrors Rust
    ``get_int``.

    Parsing a text cell is RTS-gated (see :func:`~aletheia.from_decimal`).
    """
    val = d.get(key)
    if is_pure_int(val):
        return val
    if isinstance(val, str):
        try:
            frac = from_decimal(val.strip())
        except ValidationError as exc:
            msg = f"{ctx}: invalid '{key}': {exc}"
            raise ValidationError(msg) from exc
        if frac.denominator != 1:
            msg = f"{ctx}: '{key}' must be a whole number, got {frac}"
            raise ValidationError(msg)
        return frac.numerator
    if isinstance(val, float):
        msg = f"{ctx}: '{key}' is a number cell; format it as TEXT (a whole number)"
        raise ValidationError(msg)
    msg = f"{ctx}: missing or invalid '{key}' (expected integer)"
    raise ValidationError(msg)


def get_excel_number(d: Mapping[str, JSONValue], key: str, ctx: str) -> Fraction:
    """Extract a required Excel numeric field as an exact rational (all-text contract).

    Unlike :func:`get_number` (shared with YAML, where an integer literal is
    itself exact), an Excel **number cell** stores a lossy IEEE-754 double — so a
    numeric field MUST be a text-formatted cell. openpyxl returns ``str`` for a
    text cell and ``int``/``float`` for a number cell, so any non-``str`` numeric
    cell is **rejected** with a "format it as TEXT" message; the text is parsed
    exactly via the kernel SSOT :func:`~aletheia.from_decimal` (RTS-gated). This
    rejects an integer number cell too — matching Rust ``get_rational``, Go
    ``xlsxRational`` and C++ ``get_decimal``, so the four bindings agree on every
    spreadsheet (the float principle: no lossy number cell ever enters).
    """
    val = d.get(key)
    if isinstance(val, str):
        try:
            return from_decimal(val.strip())
        except ValidationError as exc:
            msg = f"{ctx}: invalid '{key}': {exc}"
            raise ValidationError(msg) from exc
    if isinstance(val, (int, float)) and not isinstance(val, bool):
        msg = (
            f"{ctx}: '{key}' is a number cell (got {val}); format it as TEXT so the "
            "exact value is preserved (a number cell stores a lossy float)"
        )
        raise ValidationError(msg)
    msg = f"{ctx}: missing or invalid '{key}' (expected a text-formatted number)"
    raise ValidationError(msg)


def get_excel_int(d: Mapping[str, JSONValue], key: str, ctx: str) -> int:
    """Extract a required Excel whole-number field (all-text contract).

    The text cell is parsed exactly via :func:`~aletheia.from_decimal` and must be
    whole (unit denominator). A number cell (``int`` or ``float``) is rejected with
    a "format it as TEXT" message — see :func:`get_excel_number`.
    """
    val = d.get(key)
    if isinstance(val, str):
        try:
            frac = from_decimal(val.strip())
        except ValidationError as exc:
            msg = f"{ctx}: invalid '{key}': {exc}"
            raise ValidationError(msg) from exc
        if frac.denominator != 1:
            msg = f"{ctx}: '{key}' must be a whole number, got {frac}"
            raise ValidationError(msg)
        return frac.numerator
    if isinstance(val, (int, float)) and not isinstance(val, bool):
        msg = (
            f"{ctx}: '{key}' is a number cell (got {val}); format it as TEXT so the "
            "exact value is preserved (a number cell stores a lossy float)"
        )
        raise ValidationError(msg)
    msg = f"{ctx}: missing or invalid '{key}' (expected a text-formatted whole number)"
    raise ValidationError(msg)


def get_bool(d: Mapping[str, JSONValue], key: str, ctx: str) -> bool:
    """Extract a required boolean field from *d*.

    Accepts Python bools, integers ``1``/``0`` (Excel data_only mode), and the
    strings ``"TRUE"``/``"FALSE"``/``"1"``/``"0"`` (case-insensitive) — the same
    multi-form set as Rust ``get_bool``, Go ``xlsxBool`` and C++ ``get_bool``
    (booleans are exempt from the all-text contract, which governs only numeric
    cells, so a ``Signed`` value may be a native bool, a number, or text).
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
        upper = val.strip().upper()
        if upper in ("TRUE", "1"):
            return True
        if upper in ("FALSE", "0"):
            return False
    msg = f"{ctx}: missing or invalid '{key}' (expected TRUE/FALSE or 1/0)"
    raise ValidationError(msg)


def get_dict(d: Mapping[str, JSONValue], key: str, ctx: str) -> Mapping[str, JSONValue]:
    """Extract a required nested mapping field from *d*."""
    val = d.get(key)
    if isinstance(val, dict):
        return val
    msg = f"{ctx}: missing or invalid '{key}' (expected mapping)"
    raise ValidationError(msg)


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


def require_present_file(p: Path, kind: str) -> None:
    """Raise a clear ``FileNotFoundError`` if *p* is absent; else pass through.

    A stat failure other than "absent" propagates with its real errno.
    ``Path.exists()`` is unusable for this since Python 3.12: it swallows every
    ``OSError`` (EACCES, ENAMETOOLONG, EMFILE/EIO under load, …) and returns
    ``False``, which would mislabel a stat *failure* as "file not found" and
    mask a resource/permission problem.  ``os.lstat`` instead raises the precise
    errno — ENOENT / ENOTDIR (a missing leaf or a non-directory parent
    component) mean genuinely absent and surface as ``FileNotFoundError``;
    anything else propagates unchanged.  Mirrors the cross-binding
    ec-vs-not-found split in C++ ``validate_loader_path`` and Go
    ``validateLoaderPath`` (which key on ``os.ErrNotExist``, covering both
    ENOENT and ENOTDIR).

    *kind* ("Excel" / "YAML") is interpolated into the not-found message so
    operators see which loader rejected the path.

    Raises:
        FileNotFoundError: *p* does not exist (ENOENT / ENOTDIR).
        OSError: any other stat failure (surfaced with its errno).

    """
    try:
        os.lstat(p)
    except (FileNotFoundError, NotADirectoryError) as e:
        msg = f"{kind} file not found: {p}"
        raise FileNotFoundError(msg) from e
