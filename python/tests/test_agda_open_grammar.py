# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Grammar-derived regression tests for ``tools._agda_opens`` (open detection).

The fixtures here are SYNTHETIC and derived from Agda's import/open grammar
(``src/full/Agda/Syntax/Parser/Parser.y``) — deliberately NOT drawn from the
project tree, so the detector is verified for *any* Agda a contributor might
write, per the gate's correct-by-construction mandate.

The suite is *pure*: it runs no Agda process.  Each wildcard open's contribution
is read from :data:`RECORDED_SMC`, the ``Cmd_show_module_contents`` outputs
verified against a live Agda this session for the synthetic provider ``P`` and
its derivatives.  That keeps the regression test fast and unable to hang; an
Agda-backed integration test that re-confirms ``RECORDED_SMC`` lands with the
gate port.

Coverage: every directive form (``using`` / ``hiding`` / ``renaming`` / ``public``
and combinations, in both orders), every module-expression form (bare, qualified,
application, record-instance, instance, re-export, open-module-macro), the
no-injection forms (``import`` / ``import as``), local ``where`` / ``let`` opens,
and FN-complete check-name extraction across non-``import`` and local
``using``-opens.  The injected-set primitive :func:`provided_set` is also
checked per form (it feeds the IWYU narrower :mod:`tools.warm_iwyu`).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import NamedTuple

import pytest

from tools._agda_opens import (
    OpenInfo,
    find_opens,
    open_check_names,
    provided_set,
)

# show_module_contents outputs verified against a live Agda this session, for the
# synthetic provider P (pa, pb, _⊕_, record R, module Sub, module PM) and its
# derivatives (Re re-exports P; N is `open module N = P`; HasV / R are records).
RECORDED_SMC: dict[str, list[str]] = {
    "P": ["_⊕_", "R", "pa", "pb"],
    "Re": ["_⊕_", "R", "pa", "pb"],
    "PM": ["pmName"],
    "R": ["rf1", "rf2"],
    "N": ["_⊕_", "R", "pa", "pb"],
    "HasV": ["v"],
    "A.B.C": ["dotName", "dotOp"],
}


class Expect(NamedTuple):
    """The detection outcome expected for one grammar form.

    ``provides_exact`` asserts the whole injected set (text-enumerated forms);
    ``provides_has`` / ``provides_lacks`` assert membership / disjointness
    (wildcard forms read from recorded smc); ``check`` is the subset of
    :func:`open_check_names` the form must contribute.
    """

    is_open: bool
    has_using: bool
    provides_exact: frozenset[str] | None = None
    provides_has: frozenset[str] = frozenset()
    provides_lacks: frozenset[str] = frozenset()
    check: frozenset[str] = frozenset()


@dataclass(frozen=True)
class Form:
    """One grammar form: a single-open module source plus its expected detection."""

    label: str
    source: str
    target: str  # the module name of the open under test
    expect: Expect


def _form(label: str, line: str, target: str, expect: Expect) -> Form:
    """Wrap a single open ``line`` in a module header into a Form fixture."""
    return Form(label=label, source=f"module Fixture where\n{line}\n", target=target, expect=expect)


def _exact(*names: str) -> frozenset[str]:
    """Return a frozenset of ``names`` (for ``provides_exact`` / ``check`` fields)."""
    return frozenset(names)


FORMS: list[Form] = [
    # ---- MODELED: a `using` clause → set read from source text ----
    _form(
        "using",
        "open import P using (pa)",
        "P",
        Expect(is_open=True, has_using=True, provides_exact=_exact("pa"), check=_exact("pa")),
    ),
    _form(
        "using-empty",
        "open import P using ()",
        "P",
        Expect(is_open=True, has_using=True, provides_exact=_exact()),
    ),
    _form(
        "using+renaming",
        "open import P using (pa) renaming (pb to pbAlt)",
        "P",
        Expect(
            is_open=True,
            has_using=True,
            provides_exact=_exact("pa", "pbAlt"),
            check=_exact("pa", "pbAlt"),
        ),
    ),
    _form(
        "using+hiding",
        "open import P using (pa) hiding (pb)",
        "P",
        Expect(is_open=True, has_using=True, provides_exact=_exact("pa"), check=_exact("pa")),
    ),
    _form(
        "renaming+using (reversed order)",
        "open import P renaming (pb to pbAlt) using (pa)",
        "P",
        Expect(
            is_open=True,
            has_using=True,
            provides_exact=_exact("pa", "pbAlt"),
            check=_exact("pa", "pbAlt"),
        ),
    ),
    _form(
        "using(module Sub)",
        "open import P using (module Sub)",
        "P",
        Expect(is_open=True, has_using=True, provides_exact=_exact("Sub"), check=_exact("Sub")),
    ),
    _form(
        # A `public` re-export PROVIDES pa, but pa is NOT a per-file candidate:
        # its uses are downstream, so a per-file gate must not flag it.
        "using+public",
        "open import P using (pa) public",
        "P",
        Expect(is_open=True, has_using=True, provides_exact=_exact("pa")),
    ),
    # ---- WILDCARD: no `using` → set read from show_module_contents ----
    _form(
        "bare",
        "open import P",
        "P",
        Expect(is_open=True, has_using=False, provides_has=_exact("pa", "pb", "_⊕_")),
    ),
    _form(
        "hiding",
        "open import P hiding (pb)",
        "P",
        Expect(
            is_open=True, has_using=False, provides_has=_exact("pa"), provides_lacks=_exact("pb")
        ),
    ),
    _form(
        # Wildcard for PROVISION (brings all of P, pb renamed), yet the rename
        # destination pbAlt is an individually-prunable entry (delete just the
        # `pb to pbAlt` pair) — so it IS a check-name even with no using clause.
        "renaming (no using → wildcard)",
        "open import P renaming (pb to pbAlt)",
        "P",
        Expect(
            is_open=True,
            has_using=False,
            provides_has=_exact("pa", "pbAlt"),
            provides_lacks=_exact("pb"),
            check=_exact("pbAlt"),
        ),
    ),
    _form(
        "renaming-empty (wildcard)",
        "open import P renaming ()",
        "P",
        Expect(is_open=True, has_using=False, provides_has=_exact("pa", "pb")),
    ),
    _form(
        "public (wildcard re-export)",
        "open import P public",
        "P",
        Expect(is_open=True, has_using=False, provides_has=_exact("pa", "pb")),
    ),
    _form(
        "module-open",
        "open P",
        "P",
        Expect(is_open=True, has_using=False, provides_has=_exact("pa", "pb")),
    ),
    _form(
        "module-application",
        "open PM Nat",
        "PM",
        Expect(is_open=True, has_using=False, provides_has=_exact("pmName")),
    ),
    _form(
        "record-instance open",
        "open R r",
        "R",
        Expect(is_open=True, has_using=False, provides_has=_exact("rf1", "rf2")),
    ),
    _form(
        "instance open",
        "open R {{...}}",
        "R",
        Expect(is_open=True, has_using=False, provides_has=_exact("rf1", "rf2")),
    ),
    _form(
        "re-export wildcard",
        "open import Re",
        "Re",
        Expect(is_open=True, has_using=False, provides_has=_exact("pa", "pb", "_⊕_", "R")),
    ),
    # ---- OPEN-MODULE-MACRO ----
    _form(
        "open-module-macro (wildcard)",
        "open module N = P",
        "N",
        Expect(is_open=True, has_using=False, provides_has=_exact("pa", "pb", "_⊕_")),
    ),
    _form(
        "open-module-macro + using",
        "open module N = P using (pa)",
        "N",
        Expect(is_open=True, has_using=True, provides_exact=_exact("pa"), check=_exact("pa")),
    ),
    # ---- NO INJECTION: qualified-only ----
    _form(
        "import", "import P", "P", Expect(is_open=False, has_using=False, provides_exact=_exact())
    ),
    _form(
        "import as",
        "import P as PP",
        "P",
        Expect(is_open=False, has_using=False, provides_exact=_exact()),
    ),
    # ---- OPEN IMPORT ... AS: `as` is in OpenArgs, but `open` still injects ----
    _form(
        # open import M as N opens M unqualified (wildcard) AND binds alias N;
        # it must NOT be misclassified as the qualified-only `import M as N`.
        "open import as (wildcard + alias)",
        "open import P as PP",
        "P",
        Expect(is_open=True, has_using=False, provides_has=_exact("pa", "pb")),
    ),
    _form(
        "open import with module application",
        "open import PM Nat",
        "PM",
        Expect(is_open=True, has_using=False, provides_has=_exact("pmName")),
    ),
    # ---- QUALIFIED (dotted) module name = the whole first token ----
    _form(
        "qualified dotted module + using",
        "open import A.B.C using (dotName)",
        "A.B.C",
        Expect(
            is_open=True,
            has_using=True,
            provides_exact=_exact("dotName"),
            check=_exact("dotName"),
        ),
    ),
    _form(
        "qualified dotted module wildcard",
        "open import A.B.C",
        "A.B.C",
        Expect(is_open=True, has_using=False, provides_has=_exact("dotName", "dotOp")),
    ),
    # ---- DIRECTIVE COMBINATIONS (free order/count; only `using` restricts) ----
    _form(
        "hiding+renaming (no using → wildcard)",
        "open import P hiding (pb) renaming (pa to paAlt)",
        "P",
        Expect(
            is_open=True,
            has_using=False,
            provides_has=_exact("paAlt"),
            provides_lacks=_exact("pa", "pb"),
            check=_exact("paAlt"),
        ),
    ),
    _form(
        "using+hiding+renaming (all three)",
        "open import P using (pa) hiding (xx) renaming (pb to pbAlt)",
        "P",
        Expect(
            is_open=True,
            has_using=True,
            provides_exact=_exact("pa", "pbAlt"),
            check=_exact("pa", "pbAlt"),
        ),
    ),
    _form(
        # `public` BEFORE `using` (free order) — still a public re-export, so its
        # names are provided but never per-file candidates.
        "public before using (reversed order)",
        "open import P public using (pa)",
        "P",
        Expect(is_open=True, has_using=True, provides_exact=_exact("pa")),
    ),
    _form(
        "hiding+public (wildcard re-export)",
        "open import P hiding (pb) public",
        "P",
        Expect(
            is_open=True, has_using=False, provides_has=_exact("pa"), provides_lacks=_exact("pb")
        ),
    ),
    # ---- RENAMING TARGET forms: fixity / operator / module / multiple ----
    _form(
        # RenamingTarget = Id | 'infix'/'infixl'/'infixr' Float Id — the dst is
        # the bare Id; the fixity annotation must be skipped (else dst is wrong → FN).
        "renaming with infixl fixity target",
        "open import P renaming (pb to infixl 6 pbAlt)",
        "P",
        Expect(
            is_open=True,
            has_using=False,
            provides_has=_exact("pbAlt"),
            provides_lacks=_exact("pb"),
            check=_exact("pbAlt"),
        ),
    ),
    _form(
        "renaming with infixr fixity target",
        "open import P renaming (pb to infixr 5 pbAlt)",
        "P",
        Expect(is_open=True, has_using=False, provides_has=_exact("pbAlt"), check=_exact("pbAlt")),
    ),
    _form(
        "renaming an operator (mixfix)",
        "open import P renaming (_⊕_ to _⊗_)",
        "P",
        Expect(
            is_open=True,
            has_using=False,
            provides_has=_exact("_⊗_"),
            provides_lacks=_exact("_⊕_"),
            check=_exact("_⊗_"),
        ),
    ),
    _form(
        # ImportName_ = Id | 'module' Id — a module may be renamed; the dst is prunable.
        "renaming a module",
        "open import P renaming (module R to RAlt)",
        "P",
        Expect(is_open=True, has_using=False, check=_exact("RAlt")),
    ),
    _form(
        "renaming multiple pairs",
        "open import P renaming (pa to x; pb to y)",
        "P",
        Expect(is_open=True, has_using=False, check=_exact("x", "y")),
    ),
    # ---- USING entry forms: operator / multiple ----
    _form(
        "using an operator (mixfix)",
        "open import P using (_⊕_)",
        "P",
        Expect(is_open=True, has_using=True, provides_exact=_exact("_⊕_"), check=_exact("_⊕_")),
    ),
    _form(
        "using multiple names",
        "open import P using (pa; pb)",
        "P",
        Expect(
            is_open=True,
            has_using=True,
            provides_exact=_exact("pa", "pb"),
            check=_exact("pa", "pb"),
        ),
    ),
]


def _target_open(form: Form) -> OpenInfo:
    """Return the open in ``form`` whose module is the one under test."""
    matches = [o for o in find_opens(form.source) if o.module == form.target]
    assert matches, f"{form.label}: no open found for module {form.target!r}"
    # prefer the one matching the expected is_open (handles import-vs-open of same module)
    matches.sort(key=lambda o: o.is_open == form.expect.is_open, reverse=True)
    return matches[0]


@pytest.mark.parametrize("form", FORMS, ids=lambda f: f.label)
def test_classification(form: Form) -> None:
    """find_opens classifies each grammar form's is_open / has_using correctly."""
    target = _target_open(form)
    assert target.is_open is form.expect.is_open
    assert target.has_using is form.expect.has_using


@pytest.mark.parametrize("form", FORMS, ids=lambda f: f.label)
def test_provided_set(form: Form) -> None:
    """provided_set computes each form's injected names (text or recorded smc)."""
    provided = provided_set(_target_open(form), RECORDED_SMC)
    assert provided is not None, f"{form.label}: unexpectedly unresolvable"
    if form.expect.provides_exact is not None:
        assert provided == set(form.expect.provides_exact)
    assert form.expect.provides_has <= provided
    assert form.expect.provides_lacks.isdisjoint(provided)


@pytest.mark.parametrize("form", FORMS, ids=lambda f: f.label)
def test_check_names_contribution(form: Form) -> None:
    """open_check_names yields EXACTLY the names each single-open form makes prunable.

    Exact equality (not ``<=``) pins down both directions: every using-entry and
    rename-destination of a candidate open is flagged, and nothing else is — a
    bare wildcard, a `public` re-export, and a qualified-only `import` all
    contribute the empty set.
    """
    names = open_check_names(find_opens(form.source))
    assert names == set(form.expect.check)


# ---- P1: FN-complete check-name extraction across ALL opens (the audit fix) ----


@pytest.mark.parametrize(
    ("line", "expected"),
    [
        ("open M using (foo)", {"foo"}),  # non-import module-open with using
        ("open module N = M using (bar)", {"bar"}),  # open-module-macro with using
        ("open M using (a) renaming (b to c)", {"a", "c"}),  # combined, non-import
    ],
)
def test_p1_non_import_using_opens_are_flaggable(line: str, expected: set[str]) -> None:
    """A `using` name in a non-`import` open is a prunable check-name (was an FN)."""
    names = open_check_names(find_opens(f"module Fixture where\n{line}\n"))
    assert expected <= names


def test_p1_local_using_open_is_flaggable() -> None:
    """A `using` name in a `where`-local open is a prunable check-name (was an FN)."""
    source = "module Fixture where\ng = x\n  where open import M using (loc)\n"
    assert "loc" in open_check_names(find_opens(source))


def test_renaming_without_using_dest_is_prunable() -> None:
    """`renaming` without `using` is a wildcard, yet its rename dest IS prunable.

    The open is a wildcard for PROVISION (no `using` clause → it brings ALL of
    the module), so `has_using` is False — but the rename destination `b` is an
    explicit, individually-removable entry (delete just the `a to b` pair), so it
    must be a check-name. Treating `renaming`-without-`using` as having no
    prunable entry was an FN (`++ₗ-assoc` is removed by exactly this deletion).
    """
    opens = find_opens("module Fixture where\nopen import M renaming (a to b)\n")
    assert opens[0].has_using is False
    assert open_check_names(opens) == {"b"}


def test_public_reexport_excluded_from_check_names() -> None:
    """A `using`/`renaming` name on a `public` re-export is NOT a per-file candidate.

    Removing a name from a `public` block changes the file's exported surface,
    which can break a downstream consumer the per-file gate cannot see — so such
    names must never be flagged. They still appear in `provided_set` (a public
    open DOES supply them) — only the candidate set excludes them.
    """
    opens = find_opens(
        "module Fixture where\nopen import P using (pa) renaming (pb to pbAlt) public\n"
    )
    assert opens[0].has_public is True
    assert open_check_names(opens) == set()
    # but it still provides the names (for OTHER opens' redundancy decisions)
    assert {"pa", "pbAlt"} <= (provided_set(opens[0], RECORDED_SMC) or set())


# ---- COMMENT / STRING ROBUSTNESS ------------------------------------------
# Agda keywords are reserved, so a keyword token inside a comment or a string
# literal is never a directive.  Stripping must not produce a phantom open
# (over-flag, harmless to confirm but noisy) NOR drop a real open after it (FN).


@pytest.mark.parametrize(
    "line",
    [
        "-- open import P using (dead)",  # line comment
        "{- open import P using (dead) -}",  # block comment
        "{- outer {- open import P -} still open -}",  # nested block comment
        '  s = "open import P using (dead)"',  # string literal
        "{-# COMPILE open import P #-}",  # pragma (a {- … -} block form)
    ],
    ids=["line-comment", "block-comment", "nested-block", "string", "pragma"],
)
def test_keyword_in_noncode_is_not_an_open(line: str) -> None:
    """An ``open``/``import`` token inside a comment or string is never a directive."""
    source = f"module Fixture where\n{line}\nreal = 0\n"
    assert find_opens(source) == []


def test_real_open_after_block_comment_is_found() -> None:
    """A real open after a block comment is still found (stripping must not over-eat)."""
    source = "module Fixture where\n{- a comment -}\nopen import P using (pa)\n"
    assert open_check_names(find_opens(source)) == {"pa"}


def test_trailing_line_comment_after_open_is_ignored() -> None:
    """An inline ``--`` comment after a using clause does not corrupt the name list."""
    source = "module Fixture where\nopen import P using (pa)  -- keep only pa\n"
    assert open_check_names(find_opens(source)) == {"pa"}


# ---- NESTING: opens are found in every declaration-block context -----------
# Open/Import are Declarations; declaration blocks nest in where/let/private/
# instance/abstract/macro/mutual/opaque/record bodies.  The position-independent
# keyword scan must find a nested open's check-name in each (else FN).


@pytest.mark.parametrize(
    "block",
    ["private", "abstract", "instance", "macro", "mutual", "opaque"],
)
def test_open_found_in_block_context(block: str) -> None:
    """A ``using``-open nested in any declaration block contributes its check-name."""
    source = f"module Fixture where\n{block}\n  open import M using (loc)\n"
    assert "loc" in open_check_names(find_opens(source))


def test_open_found_in_let_binding() -> None:
    """A ``let open … using`` inside a term is found (a known live FN class)."""
    source = "module Fixture where\nf = let open M using (loc) in loc\n"
    assert "loc" in open_check_names(find_opens(source))


# ---- LAYOUT: multi-line directives must not truncate the name list (FN) -----
# _gather_directive collects continuation lines by indentation; a multi-line
# using/renaming whose names span lines must still yield ALL of them.


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        ("module F where\nopen import M using\n  (a; b)\n", {"a", "b"}),
        ("module F where\nopen import M using\n  ( a\n  ; b\n  ; c\n  )\n", {"a", "b", "c"}),
        ("module F where\nopen import M renaming\n  ( a to x\n  ; b to y\n  )\n", {"x", "y"}),
        # a sibling declaration after the open must NOT be slurped into its names
        ("module F where\nopen import M using (a; b)\nfoo : Set\nfoo = a\n", {"a", "b"}),
        # nested open with a multi-line using indented under `where`
        (
            "module F where\ng = x\n  where\n    open import M using\n      (a; b)\n",
            {"a", "b"},
        ),
        # multi-line using of OPERATORS — the exact shape (keyword on one line,
        # mixfix names on the next) that the legacy parse_imports mis-reads as an
        # empty using-list (a real false negative the grammar scan must not share).
        ("module F where\nopen import M using\n  (_<|>_; _>>=_)\n", {"_<|>_", "_>>=_"}),
    ],
    ids=[
        "paren-next-line",
        "names-multiline",
        "renaming-multiline",
        "stop-at-sibling",
        "nested-ml",
        "multiline-operators",
    ],
)
def test_multiline_directive_name_list_complete(source: str, expected: set[str]) -> None:
    """A multi-line ``using``/``renaming`` contributes all its names (no truncation)."""
    assert open_check_names(find_opens(source)) == expected


# ---- REPEATED DIRECTIVES: the grammar permits a list of ImportDirective1 ----
# `ImportDirective : ImportDirective1 ImportDirective`, so `using (a) using (b)`
# is grammatical.  Both name lists must be flagged (a first-clause-only parse is
# an under-flag → FN).


def test_repeated_using_clauses_are_all_flagged() -> None:
    """Two ``using`` clauses on one open contribute both name lists (no FN)."""
    source = "module F where\nopen import M using (a) using (b)\n"
    assert open_check_names(find_opens(source)) == {"a", "b"}


def test_repeated_renaming_clauses_are_all_flagged() -> None:
    """Two ``renaming`` clauses on one open contribute both destinations (no FN)."""
    source = "module F where\nopen import M renaming (a to x) renaming (b to y)\n"
    assert open_check_names(find_opens(source)) == {"x", "y"}
