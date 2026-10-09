# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The phase table names one current phase, and every document uses the table's word for it.

The phase table of ``PROJECT_STATUS.md`` is the authority on which phase the
project is in: exactly one of its rows has a status cell other than the
completion mark, and that cell's word is the one ``docs/PITCH.md`` uses in its
sentence ``Phase <n> is <word>``, as does the same sentence wherever another
tracked document carries it.  The pitch must carry the sentence.  A status
document without a table, or a table with no open row or several, holds no
current phase, and the arm reports that rather than passing on nothing.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NamedTuple

from tools._common import RelPath, prose_lines

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

STATUS = RelPath("PROJECT_STATUS.md")
PITCH = RelPath("docs/PITCH.md")
COMPLETE = Prose("✅")

# A phase row: the phase label, its title, then the status cell.
_ROW = re.compile(r"^\|\s*(\d+(?:\.\d+)?)\s*\|[^|]+\|\s*([^|]+?)\s*\|")


class _Phase(NamedTuple):
    """One row of the phase table: its label and the status cell's text."""

    label: Prose
    status: Prose


def _lines(rel: RelPath, text: Prose) -> list[Prose]:
    """Return the prose lines of the document ``rel``, whose text is ``text``."""
    return [Prose(line) for _, line in prose_lines(rel, text)]


def _current_phase(status: Prose) -> _Phase | Prose:
    """Return the one row of the status document's table that is not complete, or the finding."""
    rows = [
        _Phase(Prose(m.group(1)), Prose(m.group(2).strip()))
        for line in _lines(STATUS, status)
        if (m := _ROW.match(line)) is not None
    ]
    if not rows:
        return Prose(f"{STATUS}: no phase table")
    open_rows = [row for row in rows if row.status != COMPLETE]
    if len(open_rows) != 1:
        listed = ", ".join(f"{row.label} ({row.status})" for row in open_rows)
        count = f"{len(open_rows)} phases are not complete, so there is no one current phase"
        return Prose(f"{STATUS}: {count}: {listed}")
    return open_rows[0]


def _words(rel: RelPath, text: Prose, label: Prose) -> list[Prose]:
    """Return every word a document's sentences give the phase ``label``, in order of appearance.

    A sentence reads ``Phase <label> is <word>`` in any case, its word being the run of letters
    and spaces after ``is``, trimmed: punctuation, any other character or the line's end ends it.
    """
    sentence = rf"\bPhase {re.escape(label)} is ([a-z ]+)"
    return [
        Prose(m.group(1).strip())
        for line in _lines(rel, text)
        for m in re.finditer(sentence, line, re.IGNORECASE)
    ]


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per disagreement with the phase table, or per document it cannot read.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Every tracked Markdown file's text, by its repo-relative path.

    Returns:
        The findings, each naming the document concerned; none when the table
        names one current phase and every sentence about it uses the table's word.

    """
    del root, tracked
    if STATUS not in documents:
        return [Prose(f"{STATUS}: not a tracked document")]
    current = _current_phase(documents[STATUS])
    if not isinstance(current, _Phase):
        return [current]
    if PITCH not in documents:
        return [Prose(f"{PITCH}: not a tracked document")]
    word = current.status.lower()
    out: list[Prose] = []
    for rel, text in documents.items():
        words = _words(rel, text, current.label)
        if rel == PITCH and not words:
            out.append(Prose(f"{PITCH}: says nothing about phase {current.label}"))
        out.extend(
            Prose(f"{rel}: says phase {current.label} is {theirs!r}; the table says {word!r}")
            for theirs in words
            if theirs.lower() != word
        )
    return out
