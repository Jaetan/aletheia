# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The arms of the documentation gate: one claim about the tracked documents per module.

Each arm's ``findings(root, tracked, documents)`` returns its findings, one per
defect, naming the file concerned; a scan that finds nothing it expects is a
finding too.  ``root`` is the repository's resolved path, ``tracked`` every
tracked path as ``git ls-files`` prints it, and ``documents`` the text of every
tracked Markdown file the work tree gives, in the order of ``tracked``, read once
by ``tools/check_docs.py`` for all of its checks.  A tracked file the work tree
cannot give is a finding, never an error: ``read_tracked_bytes`` is the one read
of a tracked file, ``read_tracked`` its text, and ``missing`` words the finding
for a file an arm needs and has no text of.  The heading, tracked-directory,
paragraph and link-destination readers here are shared by the gate's link checks
and the arms.
"""

from __future__ import annotations

import re
from collections import Counter
from dataclasses import dataclass
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, NewType

from tools._common import FENCE, INLINE_CODE, RelPath, prose_lines

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterable, Mapping, Sequence
    from pathlib import Path

    type Arm = Callable[[Path, Sequence[RelPath], Mapping[RelPath, Prose]], list[Prose]]

# An ATX heading opens on a run of one to six # before a space, a tab or the line's end.
ATX_OPEN = re.compile(r"#{1,6}(?:[ \t]|$)")
_ATX = re.compile(ATX_OPEN.pattern + r"[ \t]*(.*?)[ \t]*#*[ \t]*$")
_HTML_ANCHOR = re.compile(r'(?:name|id)="([^"]+)"')
_LINK_TOKEN = re.compile(r"[^ \t\n]+")

# The bytes of a file as the work tree holds them.
FileBytes = NewType("FileBytes", bytes)


@dataclass(frozen=True)
class Unread:
    """A tracked file the work tree could not give, and the finding saying what went unchecked."""

    finding: Prose


def _unreadable(rel: RelPath, unchecked: Prose) -> Prose:
    """Word the finding for the tracked file ``rel`` the work tree could not give."""
    return Prose(f"{rel}: could not be read, so {unchecked}")


def read_tracked_bytes(root: Path, rel: RelPath, unchecked: Prose) -> FileBytes | Unread:
    """Return the bytes of the tracked file ``rel`` under ``root``, or an ``Unread`` if it has none.

    A path the work tree lacks, a directory, or a file that may not be opened is
    unread, its finding ``<rel>: could not be read, so <unchecked>``.
    """
    try:
        return FileBytes((root / rel).read_bytes())
    except OSError:
        return Unread(_unreadable(rel, unchecked))


def read_tracked(root: Path, rel: RelPath, unchecked: Prose) -> Prose | Unread:
    """Return the text of the tracked file ``rel`` under ``root``, or the ``Unread`` of its read.

    The bytes decode as UTF-8, a byte that is not UTF-8 reading as U+FFFD, so it
    never stops the read; a line ends at LF, CRLF or a lone CR, each read as LF.
    """
    data = read_tracked_bytes(root, rel, unchecked)
    if isinstance(data, Unread):
        return data
    return Prose(str(data, "utf-8", "replace").replace("\r\n", "\n").replace("\r", "\n"))


def missing(rel: RelPath, tracked: Collection[RelPath], unchecked: Prose) -> Prose:
    """Return the finding for ``rel``, a file an arm needs and has no text of.

    A tracked file it lacks is one the work tree could not give, worded as
    ``read_tracked`` words it; any other is ``<rel>: not tracked, so <unchecked>``.
    """
    if rel in tracked:
        return _unreadable(rel, unchecked)
    return Prose(f"{rel}: not tracked, so {unchecked}")


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
