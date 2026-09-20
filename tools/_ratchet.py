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

from typing import TYPE_CHECKING, NamedTuple, NewType, cast

import yaml

from tools._common import RelPath

if TYPE_CHECKING:
    from pathlib import Path

# The text a row is keyed by, a loop header or a declaration, in the one spelling
# the gate's own canonicaliser produces: whitespace collapsed, read from the source.
# Only that canonicaliser, and the record reader, mint one.
CanonicalText = NewType("CanonicalText", str)


class RowKey(NamedTuple):
    """What one row of a ratchet record names: a file, and the text found in it."""

    file: RelPath
    text: CanonicalText


# A record's rows, or a tree's observation of them: how many of each key there are.
type RatchetRows = dict[RowKey, int]


class Row(NamedTuple):
    """One row as the record spells it: its key, and how many of it the file holds."""

    key: RowKey
    held: int


def as_row(file: RelPath, text: CanonicalText, count: int) -> str:
    """Render one row the way the record spells it, so a diagnostic can be pasted.

    The text is double-quoted with its backslashes and quotes escaped: a
    backslash in a character literal the text carries would otherwise be read
    by YAML as an escape, and the pasted row would name a different thing.
    """
    quoted = text.replace("\\", "\\\\").replace('"', '\\"')
    return f'  - file: {file}\n    text: "{quoted}"\n    count: {count}'


def read_ratchet_rows(repo: Path, record: Path, key: str) -> RatchetRows | str:
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
    rows: RatchetRows = {}
    for entry in cast("list[object]", listed):
        parsed = _read_row(record, entry)
        if isinstance(parsed, str):
            return parsed
        rows[parsed.key] = rows.get(parsed.key, 0) + parsed.held
    return rows


def _read_row(record: Path, entry: object) -> Row | str:
    """Read one row into its key and count, or the reason it could not be read."""
    if not isinstance(entry, dict):
        return f"{record} carries a row that is not a mapping"
    row = cast("dict[str, object]", entry)
    file, text, count = row.get("file"), row.get("text"), row.get("count", 1)
    if not isinstance(file, str) or not isinstance(text, str):
        return f"{record} carries a row without a `file:` and a `text:` string"
    if isinstance(count, bool) or not isinstance(count, int) or count < 1:
        return f"{record} carries a row whose `count:` is not a positive integer: {count!r}"
    return Row(RowKey(RelPath(file), CanonicalText(text)), count)
