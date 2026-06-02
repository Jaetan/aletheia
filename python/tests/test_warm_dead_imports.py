"""Pure tests for ``tools.warm_dead_imports`` — synthetic fixtures, no agda, no tree.

Per the project rule to test from the grammar / synthetic fixtures rather than
the current codebase (``memory/project_agda_iwyu.md``: "Test from the GRAMMAR,
not the tree"), every fixture here is hand-built Agda source plus synthetic
Agda-highlighting tokens plus synthetic ``show_module_contents`` results.  This
exercises, without spawning agda or reading any project file:

* the gate's candidate logic (:func:`detect_dead`) — the unused-sieve,
  def-id duplicate detection (and that an *overload* is NOT a duplicate), the
  wildcard-redundancy signal, the unresolvable-wildcard confirm-all fallback,
  and ``public`` re-export exclusion;
* the confirm clause-editing (:func:`texts_without_name`), including the P1
  case of a non-``import`` open and the clause-scoped edit that never touches a
  module path;
* the warm read-loop logic (:func:`read_load` / :func:`read_module_contents`),
  notably the SILENCE guard that makes an unresolvable ``show_module_contents``
  return ``None`` instead of hanging — the regression test for a real hang.
"""

from __future__ import annotations

import json
import queue
from typing import TYPE_CHECKING

import pytest

from tools.warm_dead_imports import (
    DefSite,
    Token,
    detect_dead,
    read_load,
    read_module_contents,
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


def test_detect_dead_unused_and_wildcard_redundant() -> None:
    """An unused name is dead; a used name a wildcard also supplies is redundant."""
    text = (
        "module Fixture where\n"
        "open import P using (usedName; deadName)\n"
        "open import W\n"
        "body = usedName\n"
    )
    tokens = [
        _tok(text, "usedName", 0, ("P.agda", 10)),  # import-clause occurrence
        _tok(text, "deadName", 0, ("P.agda", 20)),  # imported, never used -> dead
        _tok(text, "usedName", 1, ("P.agda", 10)),  # body use -> same def-id -> alive
    ]
    result = detect_dead(text, tokens, _ABS, {"W": ["usedName", "wOther"]})
    assert result["dead"] == ["deadName"]
    assert result["wildcard_redundant"] == ["usedName"]  # W (wildcard) also supplies it
    assert result["candidates"] == ["deadName", "usedName"]
    assert result["duplicates"] == []
    assert result["public_skipped"] == []


def test_detect_dead_duplicate_same_defid() -> None:
    """Two imports of the SAME entity (one def-id) make one a removable duplicate."""
    text = (
        "module Fixture where\nopen import P using (dup)\nopen import Q using (dup)\nbody = dup\n"
    )
    entity: DefId = ("E.agda", 5)
    tokens = [
        _tok(text, "dup", 0, entity),  # P clause
        _tok(text, "dup", 1, entity),  # Q clause (same entity, re-exported)
        _tok(text, "dup", 2, entity),  # body use -> alive, but still a duplicate
    ]
    result = detect_dead(text, tokens, _ABS, {})
    assert result["duplicates"] == ["dup"]
    assert "dup" in result["candidates"]


def test_detect_dead_overload_is_not_duplicate() -> None:
    """Two same-NAMED but distinct entities (different def-ids) are not paired."""
    text = "module Fixture where\nopen import P using (ov)\nopen import Q using (ov)\nbody = ov\n"
    tokens = [
        _tok(text, "ov", 0, ("A.agda", 1)),  # P clause
        _tok(text, "ov", 1, ("B.agda", 2)),  # Q clause — DIFFERENT entity
        _tok(text, "ov", 2, ("A.agda", 1)),  # body uses P's
    ]
    result = detect_dead(text, tokens, _ABS, {})
    assert result["duplicates"] == []  # distinct def-ids -> not a duplicate
    assert result["candidates"] == []  # used, no wildcard, no dup -> nothing


def test_detect_dead_public_reexport_excluded() -> None:
    """A name on a ``public`` re-export is reported skipped, never a candidate."""
    text = "module Fixture where\nopen import P using (pub) public\nbody = pub\n"
    tokens = [
        _tok(text, "pub", 0, ("P.agda", 7)),  # public clause
        _tok(text, "pub", 1, ("P.agda", 7)),  # body use
    ]
    result = detect_dead(text, tokens, _ABS, {})
    assert result["public_skipped"] == ["pub"]
    assert result["candidates"] == []


def test_detect_dead_unresolvable_wildcard_falls_back_to_all() -> None:
    """A wildcard whose module smc cannot enumerate makes every name a candidate.

    The sound, no-false-negative fallback that replaced disqualification: when a
    non-``using`` open's module is absent from ``module_contents`` (e.g. one
    defined in a local scope), confirm — not membership — must decide, so every
    check-name is nominated.
    """
    text = (
        "module Fixture where\n"
        "open import P using (a; b)\n"
        "open LocalMod\n"  # non-import wildcard, absent from module_contents
        "body = a\n"
    )
    tokens = [
        _tok(text, "a", 0, ("P.agda", 1)),
        _tok(text, "b", 0, ("P.agda", 2)),
        _tok(text, "a", 1, ("P.agda", 1)),  # body uses a (b is unused)
    ]
    result = detect_dead(text, tokens, _ABS, {})  # no entry for LocalMod
    assert set(result["wildcard_redundant"]) == {"a", "b"}
    assert set(result["candidates"]) >= {"a", "b"}


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


def test_read_module_contents_resolvable() -> None:
    """A ModuleContents display yields its full export names (mixfix included)."""
    line = _display("ModuleContents", contents=[{"name": "a"}, {"name": "_⊕_"}])
    assert read_module_contents(_reader([line])) == ["a", "_⊕_"]


def test_read_module_contents_empty_module() -> None:
    """A genuinely empty module returns [] (distinct from None=unresolvable)."""
    line = _display("ModuleContents", contents=[])
    assert read_module_contents(_reader([line])) == []


def test_read_module_contents_silence_returns_none() -> None:
    """THE HANG GUARD: an unresolvable module → agda silent → None, never a hang."""
    assert read_module_contents(_reader([])) is None


def test_read_module_contents_error_display_returns_none() -> None:
    """An Error display (module not in scope) is unresolvable → None."""
    line = _display("Error", error={"message": "Not in scope"})
    assert read_module_contents(_reader([line])) is None


def test_read_module_contents_eof_returns_none() -> None:
    """Process exit mid-query returns None rather than raising."""
    assert read_module_contents(_reader([None])) is None


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
