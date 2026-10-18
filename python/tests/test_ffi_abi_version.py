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

import re
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _stand_in import StandInName, stand_in_kernel

from aletheia import FFIBackend, FFIError
from aletheia.client._enrichment import get_renderer_lib
from aletheia.client._ffi import ABI_VERSION

if TYPE_CHECKING:
    import ctypes

_SHIM = Path(__file__).resolve().parents[2] / "haskell-shim"


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
        FFIBackend(lib_path=stand_in_kernel(StandInName("stale_abi_kernel")))


def test_a_library_without_the_version_export_is_refused() -> None:
    """A loadable library with no version export predates the versioned ABI."""
    with pytest.raises(FFIError, match="predates the versioned ABI"):
        FFIBackend(lib_path=stand_in_kernel(StandInName("symbolless")))


def test_the_renderer_refuses_a_library_at_another_version(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The renderer's own load reads the version too, with no backend's library registered.

    The refused library is never registered: the renderer's cell stays empty.
    """
    stale = stand_in_kernel(StandInName("stale_abi_kernel"))
    cell: list[ctypes.CDLL | None] = [None]
    monkeypatch.setattr("aletheia.client._enrichment._RENDERER_LIB", cell)
    monkeypatch.setenv("ALETHEIA_LIB", str(stale))
    with pytest.raises(FFIError) as refused:
        _ = get_renderer_lib()
    assert str(refused.value) == (
        f"the library implements ABI version {ABI_VERSION + 1}, "
        f"and this binding needs {ABI_VERSION}"
    )
    assert cell == [None]
