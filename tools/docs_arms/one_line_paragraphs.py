# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Outside fenced code, every paragraph, list item and blockquote of the building guide is one line.

The subject is ``docs/development/BUILDING.md``. An indented line that is not a list item, a
prose line under a prose, item or ``>`` line, and a ``>`` line under another are each a finding
naming the line that continues the block. Headings, table rows, list items at any indent and
``---`` breaks may follow one another. The fenced blocks are the ones ``tools._common.prose_lines``
drops; the shape of a line is read from its original text, because that helper's inline-code
mask moves a line's first column. A subject missing from the documents, or one with nothing but
blank lines outside fenced code, is a finding too.
"""

from __future__ import annotations

import enum
import re
from typing import TYPE_CHECKING

from tools._common import RelPath, prose_lines

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

SUBJECT = RelPath("docs/development/BUILDING.md")


class Shape(enum.Enum):
    """What a line outside fenced code is, as Markdown reads it."""

    HEADING = "heading"
    TABLE = "table"
    ITEM = "item"
    QUOTE = "quote"
    CONTINUATION = "continuation"
    RULE = "rule"
    PROSE = "prose"


# The first pattern a line matches gives its shape; a line matching none is prose.
_SHAPES = (
    (re.compile(r"^#{1,6} "), Shape.HEADING),
    (re.compile(r"^\|"), Shape.TABLE),
    (re.compile(r"^[ \t]*(?:- |\* |\d+\. )"), Shape.ITEM),
    (re.compile(r"^>"), Shape.QUOTE),
    (re.compile(r"^[ \t]"), Shape.CONTINUATION),
    (re.compile(r"^---\s*$"), Shape.RULE),
)


def shape(line: Prose) -> Shape:
    """Return the shape of one non-blank line outside fenced code."""
    return next((kind for pattern, kind in _SHAPES if pattern.match(line)), Shape.PROSE)


def _wrap(previous: Shape | None, current: Shape) -> Prose | None:
    """Return how a ``current`` line continues the ``previous`` line's block, else None."""
    match previous, current:
        case (_, Shape.CONTINUATION) | (Shape.ITEM, Shape.PROSE):
            return Prose("continues a list item or paragraph")
        case (Shape.PROSE, Shape.PROSE):
            return Prose("wraps the paragraph above it")
        case (Shape.QUOTE, Shape.PROSE | Shape.QUOTE):
            return Prose("wraps the blockquote above it")
        case _:
            return None


def paragraph_findings(rel: RelPath, text: Prose) -> list[Prose]:
    """Return one finding per line of ``text`` that continues the block above it.

    Blank lines and fence markers end a block. A finding names the line that wraps;
    a document with nothing but blank lines outside fenced code is itself a finding.
    """
    outside = {lineno for lineno, _ in prose_lines(rel, text)}
    lines = text.splitlines()
    found: list[Prose] = []
    previous: Shape | None = None
    seen = False
    for lineno, line in enumerate(lines, start=1):
        if lineno not in outside or not line.strip():
            previous = None
            continue
        seen = True
        current = shape(Prose(line))
        if (wrap := _wrap(previous, current)) is not None:
            found.append(Prose(f"{rel}: line {lineno} {wrap}"))
        previous = current
    if not seen:
        found.append(Prose(f"{rel}: no paragraph outside fenced code to check"))
    return found


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return the arm's findings over the tracked documents under ``root``.

    ``tracked`` is every tracked path; ``documents`` every tracked Markdown file's
    text, by its repo-relative path. Only the subject is read; its absence is a finding.
    """
    del root, tracked
    if SUBJECT not in documents:
        return [Prose(f"{SUBJECT}: not among the tracked documents")]
    return paragraph_findings(SUBJECT, documents[SUBJECT])
