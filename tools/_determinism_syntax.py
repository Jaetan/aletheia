# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The determinism gate's arms over a Python test's syntax tree.

``tools/check_test_determinism.py`` reads each test's code for the primitives
its catalogue spells.  Some sites no primitive spells: an async client built
with no runner leans on a thread its library starts, and a property test with
no seed draws a sample nothing fixes.  These arms find them in the parsed test,
by what the file imports, however it names them.
"""

from __future__ import annotations

import ast
from typing import NewType

from tools._ratchet import CanonicalText

# A test file's text as read.
SourceText = NewType("SourceText", str)
# How many sites of one primitive a file holds.
SiteCount = NewType("SiteCount", int)
# A name or an attribute chain as source spells it, dots included.
DottedName = NewType("DottedName", str)
# A name an import binds in a test.
BoundName = NewType("BoundName", str)

# Each binding's async client runs its sync client's calls on a thread of its
# own unless a test hands it a turn executor: Python's through
# ``asyncio.to_thread`` unless it is given a ``run_in_thread``, Rust's on the
# worker thread its constructors start.  A test that builds one that way leans
# on that thread, which no thread primitive in the test itself spells.
ASYNC_CLIENT_ON_A_THREAD = CanonicalText("thread: an async client on its default thread runner")

# A property test draws its sample from a generator: one no seed fixes is
# seeded from the clock or the operating system, and takes another path on
# every run.  Go's testing/quick draws from the clock unless a check is handed
# a Rand; a hypothesis test draws from the system unless it carries a seed,
# and a hypothesis profile with an example database replays first what an
# earlier run saved.
UNSEEDED_PROPERTY = CanonicalText("random: a property test whose sample no seed fixes")
REPLAYING_PROFILE = CanonicalText("random: a property profile replaying what an earlier run saved")


_ASYNC_MODULE = DottedName("aletheia.asyncio")


def _dotted(node: ast.expr) -> DottedName | None:
    """Spell a name or an attribute chain as dots, or None for anything else."""
    if isinstance(node, ast.Name):
        return DottedName(node.id)
    if isinstance(node, ast.Attribute):
        base = _dotted(node.value)
        return DottedName(f"{base}.{node.attr}") if base is not None else None
    return None


def _spellings(tree: ast.Module, module: DottedName, member: BoundName) -> set[DottedName]:
    """Spell every name by which a file reaches ``module.member``, as its imports bind it.

    The name itself, the member imported by name or under another, and the
    member reached through a name bound to the module.
    """
    spellings = {DottedName(f"{module}.{member}")}
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module == module:
            spellings |= {DottedName(a.asname or a.name) for a in node.names if a.name == member}
        elif isinstance(node, ast.Import):
            spellings |= {
                DottedName(f"{a.asname}.{member}")
                for a in node.names
                if a.name == module and a.asname
            }
    return spellings


def async_clients_on_a_thread(text: SourceText) -> SiteCount:
    """Count the async-client constructions in a Python test that hand it no ``run_in_thread``.

    The client is found by what the file imports: a name bound to
    ``aletheia.asyncio.AletheiaClient``, or an attribute reached through a name
    bound to the module.  A file the parser refuses counts none here; its other
    sites are still read by the catalogue.
    """
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return SiteCount(0)
    spellings = _spellings(tree, _ASYNC_MODULE, BoundName("AletheiaClient"))
    return SiteCount(
        sum(
            1
            for node in ast.walk(tree)
            if isinstance(node, ast.Call)
            and _dotted(node.func) in spellings
            and not any(keyword.arg == "run_in_thread" for keyword in node.keywords)
        )
    )


_HYPOTHESIS = DottedName("hypothesis")


def _callee(node: ast.expr) -> DottedName | None:
    """Spell what a decorator or a call names, its arguments set aside."""
    return _dotted(node.func if isinstance(node, ast.Call) else node)


def unseeded_properties(text: SourceText) -> SiteCount:
    """Count the hypothesis tests in a Python test file that carry no ``@seed``.

    A test is one decorated with hypothesis's ``given``, however the file
    imports it; it is seeded when it is also decorated with hypothesis's
    ``seed``.  A file the parser refuses counts none here.
    """
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return SiteCount(0)
    given = _spellings(tree, _HYPOTHESIS, BoundName("given"))
    seed = _spellings(tree, _HYPOTHESIS, BoundName("seed"))
    return SiteCount(
        sum(
            1
            for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef)
            and any(_callee(d) in given for d in node.decorator_list)
            and not any(_callee(d) in seed for d in node.decorator_list)
        )
    )


def replaying_profiles(text: SourceText) -> SiteCount:
    """Count the hypothesis profiles a Python test file registers with an example database.

    A profile is a call of hypothesis's ``settings.register_profile``, however
    the file imports ``settings``; it replays nothing when it passes
    ``database=None``.  A file the parser refuses counts none here.
    """
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return SiteCount(0)
    register = {
        DottedName(f"{settings}.register_profile")
        for settings in _spellings(tree, _HYPOTHESIS, BoundName("settings"))
    }
    return SiteCount(
        sum(
            1
            for node in ast.walk(tree)
            if isinstance(node, ast.Call)
            and _dotted(node.func) in register
            and not any(
                keyword.arg == "database"
                and isinstance(keyword.value, ast.Constant)
                and keyword.value.value is None
                for keyword in node.keywords
            )
        )
    )
