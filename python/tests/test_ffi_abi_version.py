# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The backend refuses a library whose ABI version is not the binding's.

A library at another version would read the binding's structures at other
offsets, so the loader reads ``aletheia_abi_version`` before anything else and
refuses there. The stand-in exports that one symbol at a version no binding
was written against; a library without the export predates the versioned ABI
and is refused for that. The stand-ins are the ones ``cabal run shake --
build`` makes beside the library: in the directory ``ALETHEIA_LIB`` names, or
the repository's ``build/``.
"""

import os
import re
import subprocess
import sys
from pathlib import Path
from typing import NewType

import pytest

from aletheia import FFIBackend, FFIError
from aletheia.client._ffi import ABI_VERSION

# A stand-in kernel's name, the stem of its source under haskell-shim/test.
StandInName = NewType("StandInName", str)

_REPO = Path(__file__).resolve().parents[2]
_SHIM = _REPO / "haskell-shim"


def _stand_in(name: StandInName) -> Path:
    """Return the stand-in kernel the build makes beside the library the tests run against."""
    lib = os.environ.get("ALETHEIA_LIB")
    built = Path(lib).parent if lib else _REPO / "build"
    path = built / "stand-ins" / f"{name}.so"
    assert path.exists(), f"stand-in {path} not built; run 'cabal run shake -- build'"
    return path


def test_the_binding_version_is_the_header_s() -> None:
    """``ABI_VERSION`` is the ``ALETHEIA_ABI_VERSION`` the header defines."""
    header = (_SHIM / "include" / "aletheia.h").read_text(encoding="utf-8")
    match = re.search(r"enum \{ ALETHEIA_ABI_VERSION = (\d+) \};", header)
    assert match is not None
    assert int(match[1]) == ABI_VERSION


def test_a_library_at_another_version_is_refused() -> None:
    """The loader names both versions and loads nothing further."""
    with pytest.raises(
        FFIError, match=f"ABI version {ABI_VERSION + 1}, and this binding needs {ABI_VERSION}"
    ):
        FFIBackend(lib_path=_stand_in(StandInName("stale_abi_kernel")))


def test_a_library_without_the_version_export_is_refused() -> None:
    """A loadable library with no version export predates the versioned ABI."""
    with pytest.raises(FFIError, match="predates the versioned ABI"):
        FFIBackend(lib_path=_stand_in(StandInName("symbolless")))


def test_the_renderer_refuses_a_library_at_another_version() -> None:
    """The renderer's own load reads the version too, in a process that has no backend."""
    stale = _stand_in(StandInName("stale_abi_kernel"))
    probe = (
        "from aletheia.client._enrichment import get_renderer_lib\n"
        "try:\n"
        "    get_renderer_lib()\n"
        "except Exception as exc:\n"
        "    print(type(exc).__name__, exc)\n"
    )
    result = subprocess.run(
        [sys.executable, "-c", probe],
        env={**os.environ, "ALETHEIA_LIB": str(stale)},
        capture_output=True,
        text=True,
        check=True,
    )
    assert result.stdout.strip() == (
        f"FFIError the library implements ABI version {ABI_VERSION + 1}, "
        f"and this binding needs {ABI_VERSION}"
    )
