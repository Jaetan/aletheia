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
and the two completeness properties the audit turned on: the unified redundancy
rule and FN-complete check-name extraction across non-``import`` and local
``using``-opens.
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
    redundant_names,
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


# ---- the unified redundancy rule ----


def test_redundancy_detected_via_wildcard_reexport() -> None:
    """A `using`-import re-supplied by a wildcard open is a redundancy candidate."""
    # `pa` arrives both explicitly and via the wildcard re-export of P.
    source = "module Fixture where\nopen import P using (pa)\nopen import Re\n"
    redundant = redundant_names(find_opens(source), RECORDED_SMC)
    assert "pa" in redundant


def test_non_overlapping_using_is_not_redundant() -> None:
    """A `using`-import no other open supplies is NOT flagged redundant."""
    # `pmName` comes only from `open import PM`; nothing else supplies it.
    source = "module Fixture where\nopen import PM using (pmName)\nopen import R\n"
    assert "pmName" not in redundant_names(find_opens(source), RECORDED_SMC)


def test_unresolvable_wildcard_makes_using_a_candidate() -> None:
    """An unresolvable wildcard (smc cannot enumerate) makes every using-name a candidate.

    The sound no-false-negative fallback: a module a top-level scope query cannot
    resolve (e.g. one defined in a local scope) is treated as possibly supplying
    any name, so confirm — not membership — gets the final say.
    """
    source = "module Fixture where\nopen import P using (pa)\nopen LocallyDefined\n"
    # LocallyDefined is absent from RECORDED_SMC → provided_set is None → fallback.
    assert "pa" in redundant_names(find_opens(source), RECORDED_SMC)
