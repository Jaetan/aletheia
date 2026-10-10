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
for a file an arm needs and has no text of.  A document's structure, its
headings, links, code spans, tables and prose, is read through ``tools._markdown``;
the tracked-directory reader and GitHub's anchors are here.
"""

from __future__ import annotations

import re
from collections import Counter
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, NewType

from tools import _markdown
from tools._common import RelPath

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterable, Mapping, Sequence
    from pathlib import Path

    type Arm = Callable[[Path, Sequence[RelPath], Mapping[RelPath, Prose]], list[Prose]]


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


def slug(heading: Prose) -> Prose:
    """Return GitHub's anchor slug for a heading whose rendered text is ``heading``.

    The text is trimmed of whitespace at its ends and lowered, every character but
    a word character (a letter, a digit or another numeral, an underscore), a hyphen
    or whitespace dropped, and each whitespace character becomes one hyphen.
    """
    s = re.sub(r"[^\w\s-]", "", heading.strip().lower())
    return Prose(re.sub(r"\s", "-", s))


def html_anchors(raw: Prose) -> list[Prose]:
    """Return the fragments the HTML ``raw`` names: every element's ``id``, every ``a``'s ``name``.

    The HTML is read as a browser reads it: a comment, a declaration, the text of
    a raw-text or RCDATA element (``script``, ``style``, ``textarea`` and ``title``
    among them) and any attribute but those two name nothing, an attribute a tag
    repeats counts once, its first, and a value's character references are decoded.
    """
    found: list[Prose] = []
    reader = HTMLParser()
    reader.handle_starttag = lambda tag, attrs: found.extend(
        Prose(value)
        for name, value in dict(reversed(attrs)).items()
        if value is not None and (name == "id" or (name == "name" and tag == "a"))
    )
    reader.feed(raw)
    return found


def header_slugs(text: Prose) -> set[Prose]:
    """Return every anchor ``text`` defines: its headings' slugs and its HTML fragments.

    A repeated slug takes GitHub's ``-1``, ``-2`` suffixes in order of appearance.
    An HTML fragment comes only from HTML the document carries, never from code.
    """
    slugs: set[Prose] = set()
    seen = Counter[Prose]()
    for heading in _markdown.headings(text):
        base = slug(heading.text)
        slugs.add(Prose(f"{base}-{seen[base]}") if seen[base] else base)
        seen[base] += 1
    slugs.update(anchor for raw in _markdown.html(text) for anchor in html_anchors(raw))
    return slugs
