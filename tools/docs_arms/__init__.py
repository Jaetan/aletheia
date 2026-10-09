# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The arms of the documentation gate: one claim about the tracked documents per module.

Each arm's ``findings(root, tracked, documents)`` returns its findings, one per
defect, naming the file concerned; a scan that finds nothing it expects is a
finding too.  ``root`` is the repository, ``tracked`` every tracked path as
``git ls-files`` prints it, and ``documents`` the text of every tracked Markdown
file, read once by ``tools/check_docs.py`` for all of its checks.  The heading
and tracked-directory readers here are shared by the gate's link checks and the arms.
"""

from __future__ import annotations

import re
from collections import Counter
from pathlib import PurePosixPath
from typing import TYPE_CHECKING

from tools._common import RelPath

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping, Sequence
    from pathlib import Path

    type Arm = Callable[[Path, Sequence[RelPath], Mapping[RelPath, Prose]], list[Prose]]

_ATX = re.compile(r"^#{1,6}\s+(.*?)\s*#*\s*$")
_HTML_ANCHOR = re.compile(r'(?:name|id)="([^"]+)"')
_FENCE = re.compile(r"^\s*(```|~~~)")


def tracked_dirs(tracked: Iterable[RelPath]) -> set[RelPath]:
    """Return every directory on the way to a tracked file, the ones a fresh checkout creates."""
    return {
        RelPath("/".join(parts[:i]))
        for parts in (PurePosixPath(path).parts for path in tracked)
        for i in range(1, len(parts))
    }


def headings(text: Prose) -> list[Prose]:
    """Return the text of every ATX heading of ``text`` outside fenced code, code spans kept."""
    out: list[Prose] = []
    in_fence = False
    for line in text.splitlines():
        if _FENCE.match(line):
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
