# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Cross-binding wire-code vocabulary parity — Python side.

Reads ``docs/WIRE_CODES.yaml`` (the cross-binding SSOT, itself anchored to
the Agda kernel by the ``check-wire-codes`` run_ci gate) and asserts the
Python ``IssueCode`` / ``ErrorCode`` StrEnums are each an exact mirror of
their YAML section — reciprocal set equality, so a missing member AND a
stale member both fail.  The Python enums are closed vocabularies, which is
why the reciprocal direction is checkable at all; the runtime decode path
deliberately passes unknown codes through as raw strings (forward
compatibility) and is not touched by this test.

Clones the ``test_log_events_parity.py`` shape: each binding's parity test
loads the YAML natively, so this file is the Python leg of the
kernel → SSOT → binding chain.
"""

from __future__ import annotations

from pathlib import Path
from typing import cast

import yaml
from _yaml_shape import as_str_object_dict

from aletheia.codes import ErrorCode, IssueCode

_REPO_ROOT = Path(__file__).resolve().parents[2]
_YAML_PATH = _REPO_ROOT / "docs" / "WIRE_CODES.yaml"


def _load_section(section: str) -> list[dict[str, object]]:
    """Load one WIRE_CODES.yaml section's entries with minimal shape guarantees."""
    with _YAML_PATH.open("r", encoding="utf-8") as fh:
        raw: object = yaml.safe_load(fh)
    root = as_str_object_dict(raw, "WIRE_CODES.yaml root")
    entries_raw: object = root.get(section)
    assert isinstance(entries_raw, list), f"WIRE_CODES.yaml must contain a '{section}' list"
    narrowed: list[object] = cast("list[object]", entries_raw)
    assert narrowed, f"WIRE_CODES.yaml '{section}' list is empty"
    return [as_str_object_dict(entry, f"{section}[{idx}]") for idx, entry in enumerate(narrowed)]


_ISSUE_ENTRIES: list[dict[str, object]] = _load_section("issue_codes")
_ERROR_ENTRIES: list[dict[str, object]] = _load_section("error_codes")


def _entry_name(entry: dict[str, object]) -> str:
    name: object = entry["name"]
    assert isinstance(name, str)
    return name


def _names(entries: list[dict[str, object]]) -> set[str]:
    """Return one section's wire-code names as a set."""
    return {_entry_name(entry) for entry in entries}


def test_yaml_schema_well_formed() -> None:
    """Every row in both sections carries a unique name and a description."""
    for section, entries in (("issue_codes", _ISSUE_ENTRIES), ("error_codes", _ERROR_ENTRIES)):
        seen: set[str] = set()
        for idx, entry in enumerate(entries):
            name = _entry_name(entry)
            assert name, f"{section}[{idx}]: empty name"
            assert name not in seen, f"{section}[{idx}]: duplicate name {name!r}"
            seen.add(name)
            desc: object = entry.get("description")
            assert isinstance(desc, str), f"{section}[{idx}] ({name}): missing description"
            assert desc, f"{section}[{idx}] ({name}): empty description"


def test_issue_codes_match_python_enum() -> None:
    """The YAML issue_codes set is exactly the ``IssueCode`` value set."""
    yaml_names = _names(_ISSUE_ENTRIES)
    enum_values = {member.value for member in IssueCode}
    assert yaml_names == enum_values, (
        f"IssueCode drifted from docs/WIRE_CODES.yaml.\n"
        f"In YAML but not enum: {sorted(yaml_names - enum_values)}\n"
        f"In enum but not YAML: {sorted(enum_values - yaml_names)}"
    )


def test_error_codes_match_python_enum() -> None:
    """The YAML error_codes set is exactly the ``ErrorCode`` value set."""
    yaml_names = _names(_ERROR_ENTRIES)
    enum_values = {member.value for member in ErrorCode}
    assert yaml_names == enum_values, (
        f"ErrorCode drifted from docs/WIRE_CODES.yaml.\n"
        f"In YAML but not enum: {sorted(yaml_names - enum_values)}\n"
        f"In enum but not YAML: {sorted(enum_values - yaml_names)}"
    )


def test_yaml_sections_disjoint() -> None:
    """No wire string appears in both vocabularies.

    Issue codes are unprefixed by design (they only appear nested under
    ``issues[].code``), so a name colliding with an error-envelope code
    would make a decoded code ambiguous for any consumer pooling them.
    """
    overlap = _names(_ISSUE_ENTRIES) & _names(_ERROR_ENTRIES)
    assert not overlap, f"codes present in BOTH vocabularies: {sorted(overlap)}"
