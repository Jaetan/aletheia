#!/usr/bin/env python3
"""tools/check_runbook_coverage.py — Enforce runbook coverage of every log event.

Offline enforcer for AGENTS.md cat 22 (Operational runbook — log-keyed
symptom → cause → action).  The runbook at ``docs/operations/RUNBOOK.md``
must contain a per-event entry for every event listed in
``docs/LOG_EVENTS.yaml``.  An event the bindings emit but the runbook
does not explain is a finding — the operator is left blind.

Strategy:

1. Load every ``name`` field under ``events:`` in ``LOG_EVENTS.yaml``.
2. Read ``RUNBOOK.md``.  An event is "covered" iff a heading line
   (``#### `<name>``` or ``#### `<name>` ...``) appears in the runbook.
3. Report any uncovered events; exit non-zero if any are missing.

Exit codes:
  0 — every event in the YAML is covered by an entry in the runbook.
  1 — at least one event is uncovered.
  2 — usage error / file missing.

This is a coverage gate, not a content gate.  Each runbook entry's
internal structure (Symptom / Cause / Action) is enforced by review
rather than by parsing — content quality is judgment, not regex.

Forward-revert verified: deleting a ``#### `dbc.parsed``` heading from
RUNBOOK.md fires this script; restoring it returns to exit 0.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml


REPO_ROOT = Path(__file__).resolve().parent.parent
LOG_EVENTS_YAML = REPO_ROOT / "docs" / "LOG_EVENTS.yaml"
RUNBOOK_MD = REPO_ROOT / "docs" / "operations" / "RUNBOOK.md"


def _load_event_names(yaml_path: Path) -> list[str]:
    if not yaml_path.is_file():
        sys.stderr.write(f"check-runbook: {yaml_path} not found\n")
        sys.exit(2)
    with yaml_path.open(encoding="utf-8") as f:
        doc = yaml.safe_load(f)
    events = doc.get("events", []) if isinstance(doc, dict) else []
    names: list[str] = []
    for entry in events:
        if isinstance(entry, dict) and isinstance(entry.get("name"), str):
            names.append(entry["name"])
    if not names:
        sys.stderr.write(
            f"check-runbook: no events parsed from {yaml_path}\n"
        )
        sys.exit(2)
    return names


def _covered_events(runbook_path: Path, names: list[str]) -> set[str]:
    if not runbook_path.is_file():
        sys.stderr.write(f"check-runbook: {runbook_path} not found\n")
        sys.exit(2)
    text = runbook_path.read_text(encoding="utf-8")
    covered: set[str] = set()
    for name in names:
        # Heading anchor: `#### `<name>`` at the start of a line, allowing
        # trailing content on the same line for future expansion.
        pattern = re.compile(
            rf"^####\s+`{re.escape(name)}`",
            flags=re.MULTILINE,
        )
        if pattern.search(text):
            covered.add(name)
    return covered


def main() -> int:
    """Verify every LOG_EVENTS.yaml event is documented in RUNBOOK.md."""
    names = _load_event_names(LOG_EVENTS_YAML)
    covered = _covered_events(RUNBOOK_MD, names)
    missing = [n for n in names if n not in covered]
    if missing:
        sys.stderr.write(
            "check-runbook: log events emitted by the bindings but not "
            "covered by docs/operations/RUNBOOK.md:\n"
        )
        for name in missing:
            sys.stderr.write(f"  - {name}\n")
        sys.stderr.write(
            f"\nfound {len(covered)}/{len(names)} events covered; expected all.\n"
            "Add a `#### `<event>`` entry to RUNBOOK.md or remove the event "
            "from LOG_EVENTS.yaml.\n"
        )
        return 1
    print(f"check-runbook: all {len(names)} log events covered by RUNBOOK.md")
    return 0


if __name__ == "__main__":
    sys.exit(main())
