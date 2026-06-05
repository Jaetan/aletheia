# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Pure tests for ``tools.warm_dead_imports`` — synthetic fixtures, no agda, no tree.

Per the project rule to test from the grammar / synthetic fixtures rather than
the current codebase (``memory/project_agda_iwyu.md``: "Test from the GRAMMAR,
not the tree"), every fixture here is hand-built Agda source plus synthetic
Agda-highlighting tokens.  This exercises, without spawning agda or reading any
project file:

* the gate's candidate logic (:func:`detect_dead`) — the unused (dead) sieve,
  that a name still in USE is never flagged (even when a duplicate import or a
  wildcard open also supplies it — redundancy is deliberately NOT flagged), and
  ``public`` re-export exclusion;
* the confirm clause-editing (:func:`texts_without_name`), including the P1
  case of a non-``import`` open and the clause-scoped edit that never touches a
  module path;
* the warm read-loop logic (:func:`read_load`), notably the SILENCE guard that
  makes a wedged agda give up instead of hanging.
"""

from __future__ import annotations

import json
import queue
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from tools.warm_dead_imports import (
    SRC,
    DefSite,
    LoadResult,
    Token,
    all_agda_files,
    changed_agda_files,
    detect_dead,
    read_load,
    remove_and_reload,
    select_files,
    texts_without_name,
)

if TYPE_CHECKING:
    from collections.abc import Callable

# A definition identity: (definitionSite.filepath, definitionSite.position).
type DefId = tuple[str, int]

# The file under analysis; import def-ids point at OTHER files (the modules).
_ABS = "Fixture.agda"


def _tok(text: str, needle: str, occ: int, defid: DefId) -> Token:
    """Build a synthetic highlighting Token for the ``occ``-th ``needle`` in ``text``.

    Ranges are 1-based (Agda's convention, which :func:`detect_dead` decodes);
    ``defid`` becomes the token's ``definitionSite`` (filepath, position).
    """
    idx = -1
    for _ in range(occ + 1):
        idx = text.index(needle, idx + 1)
    site: DefSite = {"filepath": defid[0], "position": defid[1]}
    return {"range": [idx + 1, idx + 1 + len(needle)], "definitionSite": site}


# ---- detect_dead: the candidate matrix -------------------------------------


def test_detect_dead_unused_is_dead() -> None:
    """An imported name whose def-id never reappears in the body is dead."""
    text = "module Fixture where\nopen import P using (usedName; deadName)\nbody = usedName\n"
    tokens = [
        _tok(text, "usedName", 0, ("P.agda", 10)),  # import-clause occurrence
        _tok(text, "deadName", 0, ("P.agda", 20)),  # imported, never used -> dead
        _tok(text, "usedName", 1, ("P.agda", 10)),  # body use -> same def-id -> alive
    ]
    result = detect_dead(text, tokens, _ABS)
    assert result["dead"] == ["deadName"]
    assert result["candidates"] == ["deadName"]  # candidates == dead
    assert result["public_skipped"] == []


def test_detect_dead_used_name_is_never_flagged_redundant() -> None:
    """A name still in USE is alive even if a wildcard ``open`` also supplies it.

    The dead-only contract: redundancy (used here AND wildcard-supplied) is NOT
    flagged — that speculative, anti-IWYU signal is exactly what this gate drops.
    """
    text = (
        "module Fixture where\n"
        "open import P using (usedName)\n"
        "open import W\n"  # wildcard that may also supply usedName — irrelevant now
        "body = usedName\n"
    )
    tokens = [
        _tok(text, "usedName", 0, ("P.agda", 10)),  # import-clause occurrence
        _tok(text, "usedName", 1, ("P.agda", 10)),  # body use -> alive
    ]
    result = detect_dead(text, tokens, _ABS)
    assert result["candidates"] == []  # used -> not flagged; the wildcard is ignored


def test_detect_dead_duplicate_but_used_is_not_flagged() -> None:
    """A name imported twice but USED is alive — no duplicate speculation."""
    text = (
        "module Fixture where\nopen import P using (dup)\nopen import Q using (dup)\nbody = dup\n"
    )
    entity: DefId = ("E.agda", 5)
    tokens = [
        _tok(text, "dup", 0, entity),  # P clause
        _tok(text, "dup", 1, entity),  # Q clause (same entity, re-exported)
        _tok(text, "dup", 2, entity),  # body use -> alive
    ]
    result = detect_dead(text, tokens, _ABS)
    assert result["candidates"] == []  # used -> not a candidate (duplicate not flagged)


def test_detect_dead_public_reexport_excluded() -> None:
    """A name on a ``public`` re-export is reported skipped, never a candidate."""
    text = "module Fixture where\nopen import P using (pub) public\nbody = pub\n"
    tokens = [
        _tok(text, "pub", 0, ("P.agda", 7)),  # public clause
        _tok(text, "pub", 1, ("P.agda", 7)),  # body use
    ]
    result = detect_dead(text, tokens, _ABS)
    assert result["public_skipped"] == ["pub"]
    assert result["candidates"] == []


# ---- texts_without_name: confirm clause-editing over any open --------------


def test_texts_without_name_top_level_using() -> None:
    """Dropping a middle using-entry leaves the rest of the clause."""
    src = "module M where\nopen import P using (a; b)\n"
    assert texts_without_name(src, "a") == ["module M where\nopen import P using (b)\n"]


def test_texts_without_name_renaming_dest() -> None:
    """A renaming destination is removed from its renaming clause."""
    src = "module M where\nopen import P using () renaming (x to y)\n"
    assert texts_without_name(src, "y") == ["module M where\nopen import P using () renaming ()\n"]


def test_texts_without_name_non_import_open() -> None:
    """P1: a using name on a NON-``import`` open is removable (was an FN)."""
    src = "module M where\nopen Q using (foo)\n"
    assert texts_without_name(src, "foo") == ["module M where\nopen Q using ()\n"]


def test_texts_without_name_duplicate_yields_one_variant_per_open() -> None:
    """A name in two opens yields one removal variant per open (test every copy)."""
    src = "module M where\nopen import P using (a)\nopen import P using (a)\n"
    assert texts_without_name(src, "a") == [
        "module M where\nopen import P using ()\nopen import P using (a)\n",
        "module M where\nopen import P using (a)\nopen import P using ()\n",
    ]


def test_texts_without_name_public_skipped() -> None:
    """A ``public`` open is skipped — removing its name would change exports."""
    src = "module M where\nopen import P using (a) public\n"
    assert not texts_without_name(src, "a")


def test_texts_without_name_module_entry() -> None:
    """A ``using (module Sub)`` entry is removed by its bare name ``Sub``."""
    src = "module M where\nopen import P using (module Sub)\n"
    assert texts_without_name(src, "Sub") == ["module M where\nopen import P using ()\n"]


def test_texts_without_name_clause_scoped_not_module_path() -> None:
    """A name equal to the module's last path component never corrupts the path."""
    src = "module M where\nopen import Data.List using (List)\n"
    assert texts_without_name(src, "List") == ["module M where\nopen import Data.List using ()\n"]


# ---- remove_and_reload: the confirm/apply core, against a stub typechecker -----


def _faked_load(required: list[str]) -> Callable[[str], LoadResult]:
    """Build a stand-in for ``WarmAgda.load``: a file type-checks iff it still holds `required`.

    Models ground-truth recompilation deterministically and without a process:
    the file "type-checks" (``ok``) exactly when every substring in `required`
    survives in it.  ``required=[]`` makes every removal pass (a name dead in
    every open it appears in); a substring like ``"open import P using (rel)"``
    makes that one clause load-bearing, so dropping it fails — the mixed
    used/dead case the apply loop must navigate by restoring and trying the next.
    """

    def load(abspath: str) -> LoadResult:
        text = Path(abspath).read_text(encoding="utf-8")
        ok = all(s in text for s in required)
        return LoadResult([], ok=ok, error="" if ok else "boom", warnings=[])

    return load


def test_remove_and_reload_apply_clears_every_dead_occurrence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Apply removes a name from EVERY open it is dead in (multi-occurrence completeness).

    The ``Rational.agda`` regression: a name imported in two where-block opens,
    dead in both.  Removing only the first copy would leave the gate able to flag
    its own output; the apply loop must run to a fixpoint.
    """
    src = (
        "module Fixture where\nopen import P using (rel)\nopen import Q using (rel)\nbody = unit\n"
    )
    path = tmp_path / "Fixture.agda"
    _ = path.write_text(src, encoding="utf-8")
    monkeypatch.setattr("tools.warm_dead_imports.SRC", tmp_path)

    removed = remove_and_reload(_faked_load([]), "Fixture.agda", "rel", 0, keep=True)

    assert removed is True
    final = path.read_text(encoding="utf-8")
    assert "using (rel)" not in final  # BOTH copies gone, not just the first
    assert final.count("using ()") == 2


def test_remove_and_reload_apply_keeps_the_used_occurrence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """When a name is used in one open and dead in another, apply removes only the dead one.

    Recompilation is the arbiter: dropping the USED copy fails to type-check, so
    that variant is restored and only the genuinely-dead copy goes.
    """
    src = (
        "module Fixture where\nopen import P using (rel)\nopen import Q using (rel)\nbody = unit\n"
    )
    path = tmp_path / "Fixture.agda"
    _ = path.write_text(src, encoding="utf-8")
    monkeypatch.setattr("tools.warm_dead_imports.SRC", tmp_path)

    # P's `rel` is load-bearing: a file type-checks only while that exact open survives.
    removed = remove_and_reload(
        _faked_load(["open import P using (rel)"]), "Fixture.agda", "rel", 0, keep=True
    )

    assert removed is True
    final = path.read_text(encoding="utf-8")
    assert "open import P using (rel)" in final  # used copy retained
    assert "open import Q using ()" in final  # dead copy removed


def test_remove_and_reload_confirm_probes_without_editing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Confirm mode (``keep=False``) reports removability but leaves the file untouched."""
    src = "module Fixture where\nopen import P using (rel)\nbody = unit\n"
    path = tmp_path / "Fixture.agda"
    _ = path.write_text(src, encoding="utf-8")
    monkeypatch.setattr("tools.warm_dead_imports.SRC", tmp_path)

    removed = remove_and_reload(_faked_load([]), "Fixture.agda", "rel", 0, keep=False)

    assert removed is True
    assert path.read_text(encoding="utf-8") == src  # probe-only: nothing written back


# ---- the warm read loop (no process): silence guard + terminals ------------


def _reader(items: list[str | None]) -> Callable[[], str | None]:
    """Return a ``read_line`` callable over ``items`` (exhaustion raises ``queue.Empty``).

    ``queue.Empty`` models agda going SILENT (no further output) — the condition
    the real reader signals via its timed queue read.  A ``None`` item is the EOF
    sentinel (process exited).
    """
    it = iter(items)

    def read_line() -> str | None:
        try:
            return next(it)
        except StopIteration:
            raise queue.Empty from None

    return read_line


def _display(kind: str, **info: object) -> str:
    """Encode a DisplayInfo response line with the given ``info`` kind/fields."""
    return json.dumps({"kind": "DisplayInfo", "info": {"kind": kind, **info}})


def test_read_load_success() -> None:
    """HighlightingInfo + Status{checked} + InteractionPoints → ok with tokens."""
    hl = json.dumps(
        {
            "kind": "HighlightingInfo",
            "info": {"payload": [{"range": [1, 5], "definitionSite": None}]},
        }
    )
    status = json.dumps({"kind": "Status", "status": {"checked": True}})
    interaction_points = json.dumps({"kind": "InteractionPoints"})
    state = read_load(_reader([hl, status, interaction_points]))
    assert state.ok is True
    assert len(state.tokens) == 1


def test_read_load_failure_terminal() -> None:
    """A failed load (Error + JumpToError + Status{checked:false}) ends not-ok."""
    err = _display("Error", error={"message": "boom"})
    jump = json.dumps({"kind": "JumpToError"})
    status = json.dumps({"kind": "Status", "status": {"checked": False}})
    state = read_load(_reader([err, jump, status]))
    assert state.ok is False
    assert state.error == "boom"


def test_read_load_silence_gives_up_not_ok() -> None:
    """A wedged process (silence) yields a not-ok partial state, never a hang."""
    state = read_load(_reader([]))
    assert state.ok is False


def test_read_load_eof_raises() -> None:
    """EOF mid-load (process died) raises rather than reporting a clean result."""
    with pytest.raises(RuntimeError):
        read_load(_reader([None]))


# ---- Layer-2 orchestration: file-scope mode dispatch (no silent skip) -------


def testselect_files_all_is_the_whole_tree() -> None:
    """``--all`` selects every src .agda (onboarding / periodic sweep)."""
    selected = select_files(["--all"])
    assert selected == all_agda_files()
    assert selected, "the source tree should contain .agda files"


def testselect_files_diff_matches_changed_set() -> None:
    """``--diff`` selects exactly the .agda changed vs main (per-push scope)."""
    assert select_files(["--diff"]) == changed_agda_files()


def testselect_files_explicit_passthrough_filters_flags() -> None:
    """Explicit paths pass through; ``--``-flags are not treated as files."""
    assert select_files(["--confirm", "A.agda", "B.agda"]) == ["A.agda", "B.agda"]


def testselect_files_no_mode_no_files_is_usage_error() -> None:
    """No mode flag and no files is a usage error (None ⇒ the caller exits 2)."""
    assert select_files(["--confirm"]) is None
    assert select_files([]) is None


def testall_agda_files_are_src_relative_and_real() -> None:
    """Whole-tree paths are src-relative .agda files that exist on disk."""
    files = all_agda_files()
    assert all(f.endswith(".agda") for f in files)
    assert all((SRC / f).is_file() for f in files[:5])
