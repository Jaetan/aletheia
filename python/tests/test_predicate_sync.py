"""Agda/Python ``PredicateType`` enum synchronization.

Mirrors ``test_error_code_sync.py``: guards the Python
``PredicateType`` enum in ``aletheia.protocols`` against drift from
Agda's signal-predicate JSON tags emitted by
``src/Aletheia/LTL/JSON/Format.agda``.

Rationale: the binding-layer ``PredicateType`` enum is the cross-
binding machine-readable contract — Go and C++ have parallel enums.
Without this reciprocal test, an Agda addition or rename ships as a
silent wire-value mismatch that surfaces only when a property fails to
parse at runtime.
"""

import re
from pathlib import Path

import pytest

from aletheia.protocols import PredicateType


_AGDA_FILE = (
    Path(__file__).resolve().parents[2]
    / "src"
    / "Aletheia"
    / "LTL"
    / "JSON"
    / "Format.agda"
)
_AGDA_FILE_MISSING = not _AGDA_FILE.exists()
_SKIP_REASON = (
    "Agda source required for PredicateType drift test but not at "
    f"{_AGDA_FILE} — skip from installed-wheel test runs; "
    "``pytest.fail`` stays for structural parse failures."
)

# Lines like:    ("predicate" , JString (toList "equals")) ∷ ("signal" , JString s) ...
# Post Path-A JSON-mirror: kind-discriminator literals are wrapped in `(toList "…")`
# because `JString : List Char → JSON`.
_PREDICATE_TAG_RE = re.compile(
    r'"predicate"\s*,\s*JString\s+\(toList\s+"([^"\n]+)"\)'
)


def _collect_agda_predicate_tags() -> set[str]:
    """Read every JSON tag emitted alongside ``"predicate"`` in Format.agda."""
    text = _AGDA_FILE.read_text(encoding="utf-8")
    return set(_PREDICATE_TAG_RE.findall(text))


@pytest.mark.skipif(_AGDA_FILE_MISSING, reason=_SKIP_REASON)
class TestPredicateTypeSync:
    """Python ``PredicateType`` mirrors Agda's JSON tag set."""

    def test_agda_tags_parsed(self) -> None:
        """The Agda parser found *some* tags — fails fast on a broken regex."""
        agda_tags = _collect_agda_predicate_tags()
        assert agda_tags, (
            "parsed zero predicate tags — the regex or Agda layout changed"
        )
        # Smoke-check the well-known lattice endpoints.
        assert "equals" in agda_tags
        assert "between" in agda_tags
        assert "stableWithin" in agda_tags

    def test_every_agda_tag_is_in_python_enum(self) -> None:
        """Adding an Agda predicate forces a Python enum update."""
        agda_tags = _collect_agda_predicate_tags()
        python_tags = {member.value for member in PredicateType}
        missing_in_python = agda_tags - python_tags
        assert not missing_in_python, (
            "Agda emits predicate tags that have no Python PredicateType "
            f"member: {sorted(missing_in_python)}. Add them to "
            "``aletheia/protocols.py::PredicateType`` (and mirror in "
            "Go/C++)."
        )

    def test_every_python_tag_is_in_agda(self) -> None:
        """Python does not claim tags Agda never emits — prevents stale members."""
        agda_tags = _collect_agda_predicate_tags()
        python_tags = {member.value for member in PredicateType}
        unused_in_python = python_tags - agda_tags
        assert not unused_in_python, (
            "Python PredicateType declares values Agda never emits: "
            f"{sorted(unused_in_python)}. Either remove from the enum "
            "or add the matching clause in LTL/JSON/Format.agda."
        )
