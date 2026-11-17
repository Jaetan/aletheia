# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every refusal of a reply place is built by the one helper that writes the one form.

A ``ProtocolError`` the package builds anywhere but in ``reply_refusal`` is one
the form leaves alone: the kernel's own message carried with its code, the
binary extraction reply's layout, a library that answered no reply at all, or
an argument of the package's own that no reply carries. Each such site is
listed with its count, so a refusal written by hand anywhere else is red, and
so is a listed site that no longer builds one.
"""

from __future__ import annotations

import ast
from collections import Counter
from pathlib import Path
from typing import NamedTuple, NewType

# A module of the package, as its path below the package directory.
ModulePath = NewType("ModulePath", str)

# A function of a module, by its own name.
FunctionName = NewType("FunctionName", str)

# How many ``ProtocolError`` calls a function writes.
CallCount = NewType("CallCount", int)


class Site(NamedTuple):
    """A function building ``ProtocolError`` itself."""

    module: ModulePath
    function: FunctionName


_PACKAGE = Path(__file__).resolve().parents[1] / "aletheia"

# What each function outside the helper builds by hand, and why the form leaves it alone.
_LEFT_ALONE: dict[Site, CallCount] = {
    # The kernel's own message, carried with its code.
    Site(ModulePath("client/_client.py"), FunctionName("validate_dbc")): CallCount(1),
    Site(ModulePath("client/_client.py"), FunctionName("format_dbc")): CallCount(1),
    Site(ModulePath("client/_client.py"), FunctionName("format_dbc_text")): CallCount(1),
    Site(ModulePath("client/_signal_ops.py"), FunctionName("extract_signals")): CallCount(1),
    Site(ModulePath("client/_types.py"), FunctionName("raise_on_error_response")): CallCount(1),
    # The kernel's own message, and an event kind of the package's own callers.
    Site(
        ModulePath("client/_response_parsers.py"), FunctionName("parse_event_response")
    ): CallCount(2),
    # The binary extraction reply's layout, which the reply proof does not reach.
    Site(ModulePath("client/_client_bin.py"), FunctionName("_parse_reasons")): CallCount(4),
    Site(ModulePath("client/_client_bin.py"), FunctionName("parse_extraction_buffer")): CallCount(
        3
    ),
    # A library that answered no reply: a refusal without its envelope.
    Site(ModulePath("client/_ffi.py"), FunctionName("take_error_envelope")): CallCount(1),
    # The one form itself.
    Site(ModulePath("client/_helpers/reply_shape.py"), FunctionName("reply_refusal")): CallCount(1),
}


def _built_by_hand() -> Counter[Site]:
    """Count each function's ``ProtocolError(...)`` calls across the package."""
    sites: Counter[Site] = Counter()
    for path in sorted(_PACKAGE.rglob("*.py")):
        module = ModulePath(path.relative_to(_PACKAGE).as_posix())
        tree = ast.parse(path.read_text(encoding="utf-8"))
        functions = [
            node
            for node in ast.walk(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        ]
        for node in ast.walk(tree):
            if not (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "ProtocolError"
            ):
                continue
            inside = [f for f in functions if f.lineno <= node.lineno <= (f.end_lineno or f.lineno)]
            innermost = max(inside, key=lambda f: f.lineno).name if inside else "<module>"
            sites[Site(module, FunctionName(innermost))] += 1
    return sites


def test_every_refusal_of_a_reply_place_is_built_by_the_one_form() -> None:
    """No function builds a ``ProtocolError`` itself but those the form leaves alone."""
    built = _built_by_hand()
    unlisted = sorted(
        f"{s.module}:{s.function} x{n}" for s, n in built.items() if s not in _LEFT_ALONE
    )
    moved = sorted(
        f"{s.module}:{s.function} lists {n}, builds {built[s]}"
        for s, n in _LEFT_ALONE.items()
        if built[s] != n
    )
    assert (unlisted, moved) == ([], [])
