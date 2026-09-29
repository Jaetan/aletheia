# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The shim marshals strings only through its own UTF-8 helpers.

``Foreign.C.String``'s marshallers read and write through the process locale.
On the paths whose text is ASCII by construction a locale-dependent call is
invisible to every runtime test (``test_ffi_strings`` holds the others), so
the shim's imports are checked instead.  It reads ``haskell-shim/`` above
``python/``, which mutmut's copied tree does not hold, so the mutation lane
ignores this module.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Final

_SHIM_SOURCES: Final = Path(__file__).resolve().parents[2] / "haskell-shim" / "src"

# An import of the module whose marshallers use the process locale, or of the
# module that re-exports them, with whatever follows the module name.
_LOCALE_MARSHALLERS: Final = re.compile(
    r"^import\s+(?:qualified\s+)?Foreign\.C(?:\.String)?(?![\w.])(.*)$", re.MULTILINE
)
# The one form such an import may take: the string types, and nothing else.
_TYPES_ONLY: Final = re.compile(r"\s*\((?:\s*CString(?:Len)?\s*,?)+\)\s*")


def test_shim_marshals_strings_only_as_utf8() -> None:
    """The shim takes only the string types from ``Foreign.C.String``."""
    sources = sorted(p for p in _SHIM_SOURCES.rglob("*") if p.suffix in {".hs", ".hsc"})
    assert sources, f"no Haskell sources under {_SHIM_SOURCES}"
    offending = [
        f"{source.name}: {match.group(0)}"
        for source in sources
        for match in _LOCALE_MARSHALLERS.finditer(source.read_text(encoding="utf-8"))
        if "qualified" in match.group(0) or not _TYPES_ONLY.fullmatch(match.group(1))
    ]
    assert not offending, "\n".join(offending)
