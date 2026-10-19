# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared field accessors and path-hardening helpers for the YAML and Excel loaders.

Both loaders need to (a) extract typed fields from untyped dicts with
helpful error messages, and (b) reject adversarial loader inputs
(symlinks, oversize files) before PyYAML / openpyxl gets a chance to
explode or exhaust memory.  This module provides both surfaces.
"""

from __future__ import annotations

import os
import stat
from typing import TYPE_CHECKING, NewType, TypeGuard

# DEFERRED:
# Finding: `is_str_dict` and `is_object_list` (both in `aletheia/types.py`)
#   are internal TypeGuard helpers exposed publicly via no-underscore naming.
#   Project-internal usage only.
# Why: Mechanical rename + import-site update across the package; gain is
#   small (linter/dev-tooling clarity).
# Revisit when: First external user lands, OR the helpers surface as
#   confusing public API.
# Direct sub-module import avoids re-entering ``client/__init__.py`` when
# this module is loaded transitively from ``client._helpers`` during package
# initialization (would deadlock on a partially-initialized ``aletheia.client``).
from aletheia.client._helpers.rational import from_decimal
from aletheia.client._types import AletheiaError, ValidationError
from aletheia.common_types import DocumentKey, Location

if TYPE_CHECKING:
    from collections.abc import Mapping
    from fractions import Fraction
    from pathlib import Path

    from aletheia.types import JSONValue

# A number's text: a YAML scalar as the document spells it, an Excel cell's trimmed.
NumberText = NewType("NumberText", str)


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


def _read_number(text: NumberText, location: Location, key: DocumentKey) -> Fraction:
    """Return the exact rational the kernel reads *text* as.

    The kernel decides what a number is.  Its refusal, or the shim's, carries a
    code and keeps its type, code and fields, gaining *location* and *key*, so
    its string form is ``<location>: invalid '<key>': <message>``.  An error
    without a code (the RTS down, a malformed envelope) is the run's fault and
    passes through unchanged.  RTS-gated, as :func:`~aletheia.from_decimal` is.
    """
    try:
        return from_decimal(text)
    except AletheiaError as exc:
        if exc.code is not None:
            exc.locate(location, key)
        raise


def get_number(d: Mapping[str, JSONValue], key: str, ctx: str) -> Fraction:
    """Extract a required numeric field of a YAML check as an exact rational.

    The YAML loader keeps every number as its text, so a number arrives as a
    string, which the kernel reads as the document spells it
    (:func:`_read_number`); any other value is refused as not a number.
    """
    val = d.get(key)
    if isinstance(val, str):
        return _read_number(NumberText(val), Location(ctx), DocumentKey(key))
    msg = f"{ctx}: missing or invalid '{key}' (expected number)"
    raise ValidationError(msg)


def get_int(d: Mapping[str, JSONValue], key: str, ctx: str) -> int:
    """Extract a required whole-number field of a YAML check.

    The text is read as :func:`get_number` reads it and must be whole (unit
    denominator).
    """
    val = d.get(key)
    if isinstance(val, str):
        frac = _read_number(NumberText(val), Location(ctx), DocumentKey(key))
        if frac.denominator != 1:
            msg = f"{ctx}: '{key}' must be a whole number, got {frac}"
            raise ValidationError(msg)
        return frac.numerator
    msg = f"{ctx}: missing or invalid '{key}' (expected integer)"
    raise ValidationError(msg)


def get_excel_number(d: Mapping[str, JSONValue], key: str, ctx: str) -> Fraction:
    """Extract a required Excel numeric field as an exact rational (all-text contract).

    An Excel **number cell** stores a lossy IEEE-754 double, so a numeric field
    MUST be a text-formatted cell. openpyxl returns ``str`` for a text cell and
    ``int``/``float`` for a number cell, so any non-``str`` numeric cell is
    **rejected** with a "format it as TEXT" message; the trimmed text is read by
    the kernel (:func:`_read_number`). This rejects an integer number cell too,
    matching Rust ``get_rational``, Go ``xlsxRational`` and C++ ``get_decimal``,
    so the four bindings agree on every spreadsheet (the float principle: no
    lossy number cell ever enters).
    """
    val = d.get(key)
    if isinstance(val, str):
        return _read_number(NumberText(val.strip()), Location(ctx), DocumentKey(key))
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

    The text cell is read as :func:`get_excel_number` reads it and must be whole
    (unit denominator). A number cell (``int`` or ``float``) is rejected with a
    "format it as TEXT" message, as :func:`get_excel_number` rejects it.
    """
    val = d.get(key)
    if isinstance(val, str):
        frac = _read_number(NumberText(val.strip()), Location(ctx), DocumentKey(key))
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
    rejection.  Cross-binding parity: if the C++ binding refuses a
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
