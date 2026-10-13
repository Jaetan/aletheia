# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Outside fenced code, every paragraph, list item and blockquote of the building guide is one line.

The subject is ``docs/development/BUILDING.md``, read as CommonMark (``tools._markdown``). A line
that holds more of a paragraph, a list item or a blockquote than its first line does is a finding
naming it, whatever block it holds, indented code, a heading or a table row among them: a
paragraph's second line and after, wherever the paragraph sits; a blockquote's second line and
after; and a list item's second line and after, but the lines of a list nested in it through
items alone. At the top level, headings, table rows, list items, thematic breaks and indented
code may follow one another. Fenced code is not read, and a line of spaces and tabs alone is
blank. A subject missing from the documents, or one with nothing but blank lines outside fenced
code, is a finding too.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import _markdown
from tools.docs_arms import BUILDING_GUIDE, missing

from aletheia.common_types import PositiveInt, Prose

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping, Sequence
    from pathlib import Path

    from tools._common import RelPath


_PARAGRAPH = Prose("wraps the paragraph above it")
_QUOTE = Prose("wraps the blockquote above it")
_ITEM = Prose("continues a list item or paragraph")


def _nested_in(inner: _markdown.Block, item: _markdown.Block) -> bool:
    """Whether the list ``inner`` sits right inside an item at the depth of ``item``.

    A list nested deeper lies inside one that does, and one inside a quote does not.
    """
    return inner.within == (*item.within, "item")


def paragraph_findings(rel: RelPath, text: Prose) -> list[Prose]:
    """Return one finding per line of ``text`` that continues the block above it, in line order.

    A document with nothing but blank lines outside fenced code is itself a finding.
    """
    lines = _markdown.lines(text)
    found_blocks = _markdown.blocks(text)
    fenced = {
        number
        for block in found_blocks
        if block.kind == "fence"
        for number in range(block.first, block.last + 1)
    }
    found: dict[PositiveInt, Prose] = {}

    def mark(numbers: Iterable[PositiveInt], why: Prose) -> None:
        for number in numbers:
            if number not in fenced and lines[number - 1].strip(" \t"):
                _ = found.setdefault(number, why)

    for block in found_blocks:
        later = range(block.first + 1, block.last + 1)
        if block.kind == "item":
            nested = {
                number
                for inner in found_blocks
                if inner.kind == "list" and _nested_in(inner, block)
                for number in range(inner.first, inner.last + 1)
            }
            mark((number for number in later if number not in nested), _ITEM)
        elif block.kind == "quote":
            mark(later, _QUOTE)
        elif block.kind == "paragraph":
            mark(later, _PARAGRAPH)
    out = [Prose(f"{rel}: line {number} {found[number]}") for number in sorted(found)]
    if not any(
        line.strip(" \t") for number, line in enumerate(lines, start=1) if number not in fenced
    ):
        out.append(Prose(f"{rel}: no paragraph outside fenced code to check"))
    return out


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return the arm's findings over the tracked documents under ``root``.

    ``tracked`` is every tracked path; ``documents`` each tracked Markdown file's text
    the work tree gives, by repo-relative path. Only the subject is read; its absence
    is a finding.
    """
    del root
    if BUILDING_GUIDE not in documents:
        return [missing(BUILDING_GUIDE, tracked, Prose("its paragraphs are unchecked"))]
    return paragraph_findings(BUILDING_GUIDE, documents[BUILDING_GUIDE])
