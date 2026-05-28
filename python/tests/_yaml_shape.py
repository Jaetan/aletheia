"""YAML shape helpers shared by parity tests.

Both ``test_feature_matrix_parity`` and ``test_log_events_parity`` validate
the shape of a YAML manifest before iterating it.  The validation logic
(dict-with-string-keys narrowing) is identical between the two tests, so
the helper lives here to keep pylint's R0801 duplicate-code clean.
"""

from __future__ import annotations

from typing import cast


def as_str_object_dict(value: object, context: str) -> dict[str, object]:
    """Validate that ``value`` is a dict with string keys; cast and return it."""
    assert isinstance(value, dict), f"{context}: expected mapping, got {type(value).__name__}"
    narrowed: dict[object, object] = cast("dict[object, object]", value)
    for key in narrowed:
        assert isinstance(key, str), f"{context}: non-string key {key!r} in mapping"
    return cast("dict[str, object]", value)
