# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The arms of the documentation gate: one claim about the tracked documents per module.

Each arm's ``findings(root, tracked, documents)`` returns its findings, one per
defect, naming the file concerned; a scan that finds nothing it expects is a
finding too.  ``root`` is the repository's resolved path, ``tracked`` every
tracked path as ``git ls-files`` prints it, and ``documents`` the text of every
tracked Markdown file in the order of ``tracked``, read once by
``tools/check_docs.py`` for all of its checks.  The heading, tracked-directory,
paragraph and link-destination readers here are shared by the gate's link checks and the arms.
"""

from __future__ import annotations

import re
from collections import Counter
from pathlib import PurePosixPath
from typing import TYPE_CHECKING

from tools._common import FENCE, INLINE_CODE, RelPath, prose_lines

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping, Sequence
    from pathlib import Path

    type Arm = Callable[[Path, Sequence[RelPath], Mapping[RelPath, Prose]], list[Prose]]

# An ATX heading opens on a run of one to six # before a space, a tab or the line's end.
ATX_OPEN = re.compile(r"#{1,6}(?:[ \t]|$)")
_ATX = re.compile(ATX_OPEN.pattern + r"[ \t]*(.*?)[ \t]*#*[ \t]*$")
_HTML_ANCHOR = re.compile(r'(?:name|id)="([^"]+)"')
_LINK_TOKEN = re.compile(r"[^ \t\n]+")


def tracked_dirs(tracked: Iterable[RelPath]) -> set[RelPath]:
    """Return every directory on the way to a tracked file, the ones a fresh checkout creates."""
    return {
        RelPath("/".join(parts[:i]))
        for parts in (PurePosixPath(path).parts for path in tracked)
        for i in range(1, len(parts))
    }


def destination(raw: Prose) -> Prose:
    """Return the destination of a link written ``raw``, a title after it dropped.

    Leading spaces, tabs and line breaks are dropped and the destination ends at
    the next one, "" when nothing is left; any other space, U+00A0 among them, stays in it.
    """
    token = _LINK_TOKEN.search(raw)
    return Prose(token.group() if token else "")


def paragraphs(rel: RelPath, text: Prose) -> list[Prose]:
    """Return each paragraph of the prose of document ``rel``, its lines joined by line breaks.

    The prose drops fenced code and masks each inline code span to one backtick,
    which no link destination holds, so a line holding only a code span is paragraph
    text.  A blank line, a line of spaces and tabs alone, or fenced code ends a
    paragraph, and no link or definition crosses it.
    """
    prose = {number for number, _ in prose_lines(rel, text)}
    out: list[Prose] = []
    lines: list[Prose] = []
    for number, raw in enumerate(text.splitlines(), start=1):
        line = INLINE_CODE.sub("`", raw)
        if number in prose and line.strip(" \t"):
            lines.append(Prose(line))
        elif lines:
            out.append(Prose("\n".join(lines)))
            lines = []
    if lines:
        out.append(Prose("\n".join(lines)))
    return out


def headings(text: Prose) -> list[Prose]:
    """Return the text of every ATX heading of ``text`` outside fenced code, code spans kept."""
    out: list[Prose] = []
    in_fence = False
    for line in text.splitlines():
        if FENCE.match(line):
            in_fence = not in_fence
        elif not in_fence and (m := _ATX.match(line)) is not None:
            out.append(Prose(m.group(1)))
    return out


def slug(heading: Prose) -> Prose:
    """Return GitHub's anchor slug for ``heading``, each whitespace character one hyphen."""
    s = heading.strip().lower().replace("`", "")
    s = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", s)  # [t](u) -> t
    s = re.sub(r"[^\w\s-]", "", s)  # drop punctuation, keep the spaces around it
    return Prose(re.sub(r"\s", "-", s))


def header_slugs(text: Prose) -> set[Prose]:
    """Return every anchor ``text`` defines: its headings' slugs and its HTML ``name``/``id``.

    A repeated slug takes GitHub's ``-1``, ``-2`` suffixes in order of appearance.
    """
    slugs: set[Prose] = set()
    seen = Counter[Prose]()
    for heading in headings(text):
        base = slug(heading)
        slugs.add(Prose(f"{base}-{seen[base]}") if seen[base] else base)
        seen[base] += 1
    slugs.update(Prose(anchor) for anchor in _HTML_ANCHOR.findall(text))
    return slugs
