"""Cross-binding log event vocabulary parity — Python side.

Reads ``docs/LOG_EVENTS.yaml`` and asserts that the canonical event set
declared there exactly matches the Python ``LogEvent`` enum.  Every emitted
event in the running client is already validated against ``LogEvent`` by
``test_logging.py::TestLoggingSchema::test_all_emitted_events_are_known`` —
this file closes the loop by anchoring the enum itself to the cross-binding
SSOT, so a future enum edit cannot drift away from Go and C++.

Companion gates: ``go/aletheia/log_events_test.go`` and
``cpp/tests/test_log_events_parity.cpp`` — together the three tests are the
"missing mechanism" that R18 cluster 10 attached alongside the surface fix
of Go's rogue 16th ``dbc.text_parsed`` event.
"""

from __future__ import annotations

from pathlib import Path
from typing import cast

import yaml

from aletheia.client._log import KNOWN_EVENTS, LogEvent

_VALID_LEVELS: frozenset[str] = frozenset({"debug", "info", "warn"})

_REPO_ROOT = Path(__file__).resolve().parents[2]
_YAML_PATH = _REPO_ROOT / "docs" / "LOG_EVENTS.yaml"


def _as_str_object_dict(value: object, context: str) -> dict[str, object]:
    """Validate that ``value`` is a dict with string keys; cast and return it."""
    assert isinstance(value, dict), (
        f"{context}: expected mapping, got {type(value).__name__}"
    )
    narrowed: dict[object, object] = cast("dict[object, object]", value)
    for key in narrowed:
        assert isinstance(key, str), (
            f"{context}: non-string key {key!r} in mapping"
        )
    return cast("dict[str, object]", value)


def _load_events() -> list[dict[str, object]]:
    """Load and return the event list with minimal shape guarantees."""
    with _YAML_PATH.open("r", encoding="utf-8") as fh:
        raw: object = yaml.safe_load(fh)
    root = _as_str_object_dict(raw, "LOG_EVENTS.yaml root")
    events_raw: object = root.get("events")
    assert isinstance(events_raw, list), (
        "LOG_EVENTS.yaml must contain an 'events' list"
    )
    narrowed_list: list[object] = cast("list[object]", events_raw)
    assert narrowed_list, "LOG_EVENTS.yaml 'events' list is empty"
    validated: list[dict[str, object]] = []
    for idx, evt in enumerate(narrowed_list):
        validated.append(_as_str_object_dict(evt, f"events[{idx}]"))
    return validated


_EVENTS: list[dict[str, object]] = _load_events()


def _event_name(event: dict[str, object]) -> str:
    name: object = event["name"]
    assert isinstance(name, str)
    return name


def _event_level(event: dict[str, object]) -> str:
    level: object = event["level"]
    assert isinstance(level, str)
    return level


def test_yaml_schema_well_formed() -> None:
    """Every YAML row carries name (str), level ∈ valid set, description (str)."""
    seen: set[str] = set()
    for idx, evt in enumerate(_EVENTS):
        name = _event_name(evt)
        assert name, f"events[{idx}]: empty name"
        assert "." in name, (
            f"events[{idx}]: name {name!r} missing 'namespace.action' separator"
        )
        assert name not in seen, f"events[{idx}]: duplicate name {name!r}"
        seen.add(name)

        level = _event_level(evt)
        assert level in _VALID_LEVELS, (
            f"events[{idx}]: level {level!r} not in {_VALID_LEVELS}"
        )

        desc: object = evt.get("description")
        assert isinstance(desc, str) and desc, (
            f"events[{idx}]: missing or empty description"
        )


def test_yaml_matches_log_event_enum() -> None:
    """The YAML name set is exactly the LogEvent enum value set."""
    yaml_names = {_event_name(e) for e in _EVENTS}
    enum_names = {e.value for e in LogEvent}
    assert yaml_names == enum_names, (
        f"LogEvent enum drifted from LOG_EVENTS.yaml.\n"
        f"In YAML but not enum: {yaml_names - enum_names}\n"
        f"In enum but not YAML: {enum_names - yaml_names}"
    )
    # And the cached frozenset is consistent with both.
    assert KNOWN_EVENTS == yaml_names


def test_yaml_event_count_matches_documented_total() -> None:
    """The YAML carries exactly 15 events — the count documented in
    ``python/aletheia/client/_log.py``, ``go/aletheia/doc.go``, and
    ``cpp/include/aletheia/log.hpp``.  Bumping the count requires a
    coordinated edit across all four files plus a CHANGELOG entry."""
    assert len(_EVENTS) == 15, (
        f"expected 15 cross-binding events, found {len(_EVENTS)}"
    )
