# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Exhaustive combinatorial grammar coverage for the open/import detection.

Where ``test_agda_open_grammar.py`` curates hand-written fixtures, this module
*generates* the cross-product of the independent grammar axes and asserts the
pure detection (:mod:`tools._agda_opens`) against an expected computed from the
assembled pieces — so the generator is the oracle, derived from the grammar
(``.agda-reference/Parser.y``), not from the detection it checks.

Axes crossed (Parser.y ``Open`` / ``ImportDirective`` / ``ModuleName``):

* keyword form: ``import`` / ``import … as`` / ``open import`` /
  ``open import … as`` / ``open`` / ``open …  {{…}}`` (instance) /
  ``open module N = …`` (module-macro);
* module name: single ``P`` and qualified dotted ``A.B.C``;
* directive set: every subset of ``{public, using, hiding, renaming}`` (the
  ``ImportDirective1`` alternatives), in canonical and reversed order (free
  combination/order per the grammar);
* nesting context: top-level, ``where``, ``let``, record body, and the
  ``private`` / ``abstract`` / ``instance`` / ``macro`` / ``mutual`` /
  ``opaque`` declaration blocks (Declarations nest in all of them).

That is several thousand cases; each is a pure-function assertion (no Agda, so
it cannot hang) on ``find_opens`` / ``provided_set`` / ``open_check_names``.
"""

from __future__ import annotations

import itertools
from typing import TYPE_CHECKING, NamedTuple

import pytest

from tools._agda_opens import OpenInfo, find_opens, open_check_names, provided_set

if TYPE_CHECKING:
    from collections.abc import Iterator

# A module's recorded ``show_module_contents`` export list (the wildcard set).
_SMC: dict[str, list[str]] = {
    "P": ["pa", "pb", "pc", "_op_"],
    "A.B.C": ["da", "db", "_dop_"],
}
# Per-module names guaranteed present in the smc, for the hiding / renaming-src
# pieces (so the wildcard provided-set computation is exercised meaningfully).
_HIDE: dict[str, str] = {"P": "pb", "A.B.C": "db"}
_REN_SRC: dict[str, str] = {"P": "pa", "A.B.C": "da"}

_USING = ("uA", "uB")  # the using-clause entries
_REN_DST = "rD"  # the renaming destination

_DIR_TYPES = ("public", "using", "hiding", "renaming")
_CONTEXTS = (
    "top",
    "where",
    "let",
    "record",
    "private",
    "abstract",
    "instance",
    "macro",
    "mutual",
    "opaque",
)


class Form(NamedTuple):
    """One keyword form: how to build the open line and its classification."""

    name: str
    template: str  # uses {mod} and {dir} placeholders
    alias_target: bool  # module-macro: the open's module is the alias, not {mod}
    is_open: bool
    is_import: bool
    resolvable: bool  # is the wildcard's module present in _SMC?


_FORMS: tuple[Form, ...] = (
    Form(
        "import",
        "import {mod} {dir}",
        alias_target=False,
        is_open=False,
        is_import=True,
        resolvable=False,
    ),
    Form(
        "import-as",
        "import {mod} as Alias {dir}",
        alias_target=False,
        is_open=False,
        is_import=True,
        resolvable=False,
    ),
    Form(
        "open-import",
        "open import {mod} {dir}",
        alias_target=False,
        is_open=True,
        is_import=True,
        resolvable=True,
    ),
    Form(
        "open-import-as",
        "open import {mod} as Alias {dir}",
        alias_target=False,
        is_open=True,
        is_import=True,
        resolvable=True,
    ),
    Form(
        "open",
        "open {mod} {dir}",
        alias_target=False,
        is_open=True,
        is_import=False,
        resolvable=True,
    ),
    Form(
        "instance",
        "open {mod} {{{{...}}}} {dir}",
        alias_target=False,
        is_open=True,
        is_import=False,
        resolvable=True,
    ),
    Form(
        "macro",
        "open module Alias = {mod} {dir}",
        alias_target=True,
        is_open=True,
        is_import=False,
        resolvable=False,
    ),
)


def _piece(dir_type: str, module: str) -> str:
    """Return the source text of one directive piece for ``module``."""
    return {
        "public": "public",
        "using": f"using ({_USING[0]}; {_USING[1]})",
        "hiding": f"hiding ({_HIDE[module]})",
        "renaming": f"renaming ({_REN_SRC[module]} to {_REN_DST})",
    }[dir_type]


def _orderings(subset: tuple[str, ...]) -> list[tuple[str, ...]]:
    """Return canonical + reversed orderings of ``subset`` (deduped for size<=1)."""
    canonical = subset
    reversed_ = tuple(reversed(subset))
    return [canonical] if canonical == reversed_ else [canonical, reversed_]


def _subsets() -> Iterator[tuple[str, ...]]:
    """Yield every subset of the directive types, in canonical order."""
    for size in range(len(_DIR_TYPES) + 1):
        yield from itertools.combinations(_DIR_TYPES, size)


class Case(NamedTuple):
    """One generated source plus the detection outcome expected for it."""

    label: str
    source: str
    target: str
    is_open: bool
    has_using: bool
    check: frozenset[str]
    provided: frozenset[str] | None  # None ⇒ expect an unresolvable wildcard


def _expected_check(form: Form, subset: tuple[str, ...]) -> frozenset[str]:
    """Return the names this open makes prunable (empty if not-open or public)."""
    if not form.is_open or "public" in subset:
        return frozenset()
    names: set[str] = set()
    if "using" in subset:
        names |= set(_USING)
    if "renaming" in subset:
        names.add(_REN_DST)
    return frozenset(names)


def _expected_provided(form: Form, subset: tuple[str, ...], module: str) -> frozenset[str] | None:
    """Return the unqualified set this open injects (text using / smc wildcard)."""
    if not form.is_open:
        return frozenset()
    if "using" in subset:
        names: set[str] = set(_USING)
        if "renaming" in subset:
            names.add(_REN_DST)
        return frozenset(names)
    if not form.resolvable:
        return None  # wildcard whose (macro alias) module a scope query can't resolve
    base = set(_SMC[module])
    if "hiding" in subset:
        base.discard(_HIDE[module])
    if "renaming" in subset:
        base.discard(_REN_SRC[module])
        base.add(_REN_DST)
    return frozenset(base)


def _wrap(line: str, ctx: str) -> str:
    """Place a single open ``line`` into nesting context ``ctx``."""
    if ctx == "top":
        return f"module Fixture where\n{line}\n"
    if ctx == "where":
        return f"module Fixture where\nf = z\n  where {line}\n"
    if ctx == "let":
        return f"module Fixture where\ng = let {line} in z\n"
    if ctx == "record":
        return f"module Fixture where\nrecord Rec : Set where\n  {line}\n"
    return f"module Fixture where\n{ctx}\n  {line}\n"


def _gen_cases() -> Iterator[Case]:
    """Yield the full cross-product of (form × module × directive × order × ctx)."""
    for form in _FORMS:
        modules = ["P"] if form.alias_target else ["P", "A.B.C"]
        for module in modules:
            target = "Alias" if form.alias_target else module
            for subset in _subsets():
                for order in _orderings(subset):
                    pieces = [_piece(t, module) for t in order]
                    line = form.template.format(mod=module, dir=" ".join(pieces)).rstrip()
                    check = _expected_check(form, subset)
                    provided = _expected_provided(form, subset, module)
                    order_id = "+".join(order) or "bare"
                    for ctx in _CONTEXTS:
                        yield Case(
                            label=f"{form.name}|{module}|{order_id}|{ctx}",
                            source=_wrap(line, ctx),
                            target=target,
                            is_open=form.is_open,
                            has_using="using" in subset,
                            check=check,
                            provided=provided,
                        )
                    # Multi-line layout: each directive on its own continuation
                    # line (top level) — stresses _gather_directive's indentation
                    # gathering across every directive combination (same expected).
                    if pieces:
                        multiline = form.template.format(
                            mod=module, dir="\n  " + "\n  ".join(pieces)
                        ).rstrip()
                        yield Case(
                            label=f"{form.name}|{module}|{order_id}|multiline",
                            source=_wrap(multiline, "top"),
                            target=target,
                            is_open=form.is_open,
                            has_using="using" in subset,
                            check=check,
                            provided=provided,
                        )


_CASES: list[Case] = list(_gen_cases())


def _target_open(case: Case) -> OpenInfo:
    """Return the detected open whose module matches the case's target."""
    matches = [o for o in find_opens(case.source) if o.module == case.target]
    assert matches, f"{case.label}: no open found for module {case.target!r}"
    matches.sort(key=lambda o: o.is_open == case.is_open, reverse=True)
    return matches[0]


@pytest.mark.parametrize("case", _CASES, ids=[c.label for c in _CASES])
def test_generated_grammar_case(case: Case) -> None:
    """find_opens / provided_set / open_check_names match the generated expectation."""
    target = _target_open(case)
    assert target.is_open is case.is_open
    assert target.has_using is case.has_using
    assert open_check_names(find_opens(case.source)) == set(case.check)
    provided = provided_set(target, _SMC)
    if case.provided is None:
        assert provided is None
    else:
        assert provided == set(case.provided)


def test_generated_case_count_is_in_the_thousands() -> None:
    """Guard that the generator actually produces exhaustive (thousands of) cases."""
    assert len(_CASES) >= 1000
