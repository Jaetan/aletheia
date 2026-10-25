# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The backend refuses a library whose ABI version is not the binding's.

A library at another version would read the binding's structures at other
offsets, so the loader a backend and ``start_runtime`` share reads
``aletheia_abi_version`` before anything else and refuses there. The stand-in
exports that one symbol at a version no binding was written against; a library
without the export predates the versioned ABI and is refused for that. The
stand-ins are the ones ``cabal run shake -- build`` makes beside the library: in
the directory ``ALETHEIA_LIB`` names, or the repository's ``build/``.
"""

import re
from pathlib import Path

import pytest
from _stand_in import StandInName, stand_in_kernel

from aletheia import FFIBackend, FFIError, RTSState, start_runtime
from aletheia.client._ffi import ABI_VERSION

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


@pytest.mark.usefixtures("unstarted")
def test_a_start_on_a_library_at_another_version_is_refused_and_starts_nothing() -> None:
    """``start_runtime`` reads the version as the backend does, and the runtime stays down."""
    with pytest.raises(FFIError) as refused:
        start_runtime(1, lib_path=stand_in_kernel(StandInName("stale_abi_kernel")))
    assert str(refused.value) == (
        f"the library implements ABI version {ABI_VERSION + 1}, "
        f"and this binding needs {ABI_VERSION}"
    )
    assert (RTSState.initialized, RTSState.lib) == (False, None)


def test_a_library_without_the_version_export_is_refused() -> None:
    """A loadable library with no version export predates the versioned ABI."""
    with pytest.raises(FFIError, match="predates the versioned ABI"):
        FFIBackend(lib_path=stand_in_kernel(StandInName("symbolless")))
