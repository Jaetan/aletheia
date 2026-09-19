# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The record a C++ ratchet gate compares its tree against.

Two gates keep one: ``tools/check_cpp_index_loops.py`` over the counting loops
AGENTS/cpp.md cat 27 refuses, and ``tools/check_cpp_restated_types.py`` over
the declarations cat 34 refuses.  Reading the record is the same work for both,
so it is written once.

It lives here rather than in ``tools/_common.py`` because it needs PyYAML, and
``_common`` is imported by the pre-commit hook under an interpreter that has no
third-party packages.  Only the two gates import this module, and they run
under the project's virtual environment.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

import yaml

if TYPE_CHECKING:
    from pathlib import Path


def read_ratchet_rows(repo: Path, record: Path, key: str) -> dict[tuple[str, str], int] | str:
    """Read a ratchet record's rows, or the reason it could not be read.

    A ratchet record is a YAML mapping carrying one list under ``key``, each
    entry naming a file, the canonical text of the thing recorded, and how many
    of them that file holds.  The rows come back keyed by file and by text, the
    counts of identical rows added, which is the shape a ratchet compares its
    tree against.  Keying on text rather than on a line number is what keeps an
    edit elsewhere in a file from churning the record.

    A string is the reason the record could not be read, for the caller to
    print before exiting non-zero: a record that cannot be read is a gate that
    cannot run, never a gate that passes.
    """
    path = repo / record
    if not path.is_file():
        return f"{record} is missing; the gate has no record to ratchet against"
    document: object = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(document, dict):
        return f"{record} is not a mapping"
    listed = cast("dict[str, object]", document).get(key)
    if not isinstance(listed, list):
        return f"{record} has no `{key}:` list"
    rows: dict[tuple[str, str], int] = {}
    for entry in cast("list[object]", listed):
        if not isinstance(entry, dict):
            return f"{record} carries a row that is not a mapping"
        row = cast("dict[str, object]", entry)
        identity = (str(row.get("file", "")), str(row.get("text", "")))
        rows[identity] = rows.get(identity, 0) + int(cast("int", row.get("count", 1)))
    return rows
