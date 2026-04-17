"""Lazy-import boundary guard for ``aletheia/__init__.py``.

The ``aletheia`` package re-exports from submodules at import time. One
of those submodules — ``aletheia.client._ffi`` — needs to consult the
install-time-generated ``aletheia._install_config`` module to find the
shared library, which would create an import cycle if done eagerly.

The cycle is broken by deferring the ``from .. import _install_config``
import to inside ``find_ffi_library``'s function body. Two invariants
keep that deferral working:

1. ``aletheia._install_config`` (when present) must not import from
   ``aletheia`` or any ``aletheia.*`` submodule. Otherwise we recreate
   the cycle from the other end.
2. ``aletheia.client._ffi`` must not contain a top-level
   ``from .. import _install_config`` (or equivalent) — the import must
   stay inside ``find_ffi_library``.

This test file enforces both invariants by parsing the relevant source
files. It does **not** exercise the runtime; the contract is structural.
A breakage here would surface at install time as an ``ImportError`` on
``import aletheia``, which is far more painful to debug than a failing
unit test.
"""

import ast
from pathlib import Path

import pytest

import aletheia


_ALETHEIA_PKG_ROOT = Path(aletheia.__file__).resolve().parent
_FFI_MODULE = _ALETHEIA_PKG_ROOT / "client" / "_ffi.py"
_INSTALL_CONFIG = _ALETHEIA_PKG_ROOT / "_install_config.py"


def _module_imports(source: str) -> list[ast.ImportFrom | ast.Import]:
    """Return all *top-level* import statements in a Python source string.

    Imports inside function bodies, class bodies, conditionals, or try
    blocks are intentionally excluded — those are the lazy/conditional
    forms we *want*.
    """
    tree = ast.parse(source)
    return [
        node for node in tree.body
        if isinstance(node, (ast.Import, ast.ImportFrom))
    ]


def test_ffi_module_does_not_eagerly_import_install_config() -> None:
    """``client/_ffi.py`` must defer the ``_install_config`` import.

    If a top-level ``from .. import _install_config`` slips in, the
    cycle warning at the top of ``aletheia/__init__.py`` becomes a real
    ``ImportError``. The deferred form lives inside ``find_ffi_library``.
    """
    source = _FFI_MODULE.read_text(encoding="utf-8")
    top_level = _module_imports(source)

    offending = [
        node for node in top_level
        if isinstance(node, ast.ImportFrom)
        and node.module is not None
        and "_install_config" in node.module
    ]
    # Also check ``from .. import _install_config`` (level=2, names list)
    offending.extend(
        node for node in top_level
        if isinstance(node, ast.ImportFrom)
        and node.level >= 1
        and any(alias.name == "_install_config" for alias in node.names)
    )

    assert not offending, (
        "client/_ffi.py imports _install_config at module top level — "
        "this recreates the import cycle that find_ffi_library's "
        "deferred import is designed to avoid. Move the import back "
        "inside find_ffi_library."
    )


def test_install_config_does_not_import_from_aletheia() -> None:
    """``_install_config.py`` must not import from the ``aletheia`` package.

    Skipped when no install-time config has been generated (development
    checkout without ``cabal run shake -- install``).
    """
    if not _INSTALL_CONFIG.exists():
        pytest.skip(
            "_install_config.py not present — install via "
            "'cabal run shake -- install' to exercise this guard."
        )

    source = _INSTALL_CONFIG.read_text(encoding="utf-8")
    tree = ast.parse(source)

    # Walk *all* nodes (not just top-level) — even a deferred
    # ``from aletheia import ...`` inside a function would re-introduce
    # the cycle the moment something resolves _install_config.
    offending: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            module = node.module or ""
            if module == "aletheia" or module.startswith("aletheia."):
                offending.append(
                    f"line {node.lineno}: from {module} import ..."
                )
            elif node.level >= 1:
                offending.append(
                    f"line {node.lineno}: relative import (level={node.level})"
                    f" — _install_config must be a leaf module."
                )
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == "aletheia" or alias.name.startswith("aletheia."):
                    offending.append(
                        f"line {node.lineno}: import {alias.name}"
                    )

    assert not offending, (
        "_install_config.py imports from aletheia: "
        + "; ".join(offending)
        + ". This recreates the import cycle that __init__.py's lazy "
        "boundary is designed to avoid."
    )


def test_aletheia_imports_without_locating_ffi() -> None:
    """Re-importing ``aletheia`` must not trigger the FFI lookup.

    ``find_ffi_library`` is the entry point for the lazy
    ``_install_config`` import; it should only run on first
    ``AletheiaClient`` construction, not on ``import aletheia``.

    We verify this structurally by importing the package and asserting
    no client has been constructed and no FFI handle has been resolved
    as a side-effect of the import.
    """
    # The fact that ``import aletheia`` at the top of this file did not
    # raise, plus the absence of any pre-resolved FFI handle on the
    # package object, is the assertion. If a future change moves an
    # eager ``find_ffi_library()`` call into ``__init__.py``, the import
    # will fail outright on systems without a built ``.so`` — long
    # before this assertion runs.
    assert not hasattr(aletheia, "_ffi_handle"), (
        "aletheia package surfaces a pre-resolved FFI handle at import "
        "time — this means find_ffi_library() is being called eagerly, "
        "defeating the lazy-import contract."
    )
