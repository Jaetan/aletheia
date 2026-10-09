# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The sections README.md and docs/PITCH.md both carry are one text.

Each document is read without the other, so both open with the same two sections, the bug
classes the proof removes and the comparison with the tested decoders. The arm holds the two
copies equal: each shared section is read from its heading up to the next heading of the same
level or shallower, which differs by design, with blank lines and horizontal rules dropped as
each document's own spacing, and a line's indentation and trailing blanks kept as content. A
document the pair names that is not tracked, or does not carry a shared heading, is a
finding, since the comparison then holds nothing.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NamedTuple

from tools._common import RelPath

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path


class SharedOpening(NamedTuple):
    """Two documents and the headings of the sections they carry as one text."""

    first: RelPath
    second: RelPath
    headings: tuple[Prose, ...]


PAIRS: tuple[SharedOpening, ...] = (
    SharedOpening(
        RelPath("README.md"),
        RelPath("docs/PITCH.md"),
        (
            Prose("## The pain this removes"),
            Prose("## Why switch from cantools / python-can / hand-rolled scripts?"),
        ),
    ),
)

# A horizontal rule once stripped: three or more of one of ``-``, ``*``, ``_``, spaced or not.
_RULE = re.compile(r"^([-*_])(?:[ \t]*\1){2,}$")
_SHOWN = 120


def section(text: Prose, heading: Prose) -> list[Prose] | None:
    """Return the heading's section as its non-blank lines, horizontal rules dropped.

    The section runs from the line that is ``heading`` to the next heading of the same level or
    shallower, exclusive. None when ``text`` has no such heading line.
    """
    lines = text.split("\n")
    if heading not in lines:
        return None
    level = len(heading) - len(heading.lstrip("#"))
    closes = re.compile(rf"^#{{1,{level}}} ")
    body: list[Prose] = []
    for line in lines[lines.index(heading) + 1 :]:
        if closes.match(line):
            break
        if line.strip() and not _RULE.match(line.strip()):
            body.append(Prose(line))
    return [heading, *body]


def _missing(pair: SharedOpening, documents: Mapping[RelPath, Prose]) -> list[Prose]:
    """One finding per document of the pair that is not a tracked document."""
    return [
        Prose(f"{rel}: not tracked, so the opening {other} shares is uncheckable")
        for rel, other in ((pair.first, pair.second), (pair.second, pair.first))
        if rel not in documents
    ]


def _lost(
    pair: SharedOpening, heading: Prose, a: list[Prose] | None, b: list[Prose] | None
) -> list[Prose]:
    """One finding per document of the pair lacking ``heading``, ``a`` and ``b`` their sections."""
    sides = ((pair.first, a, pair.second, b), (pair.second, b, pair.first, a))
    return [
        Prose(
            f"{rel}: no longer carries {heading!r}, "
            + (f"which {other} still does" if theirs is not None else f"nor does {other}")
        )
        for rel, ours, other, theirs in sides
        if ours is None
    ]


def _compare(pair: SharedOpening, documents: Mapping[RelPath, Prose]) -> list[Prose]:
    """One finding per document that lost a shared heading and per shared section that differs."""
    out: list[Prose] = []
    first, second = documents[pair.first], documents[pair.second]
    for heading in pair.headings:
        a, b = section(first, heading), section(second, heading)
        if a is None or b is None:
            out.extend(_lost(pair, heading, a, b))
            continue
        if a == b:
            continue
        only_a = "; ".join(ln[:_SHOWN] for ln in a if ln not in b) or "nothing"
        only_b = "; ".join(ln[:_SHOWN] for ln in b if ln not in a) or "nothing"
        sides = f"only in {pair.first}: {only_a}; only in {pair.second}: {only_b}"
        out.append(
            Prose(f"{pair.first}: {heading!r} is not the text {pair.second} carries; {sides}")
        )
    return out


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per shared section that drifted or per document that cannot be compared.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Every tracked Markdown file's text, by its repo-relative path.

    Returns:
        Each finding names the repository-relative path of the document concerned.

    """
    del root, tracked
    out: list[Prose] = []
    for pair in PAIRS:
        missing = _missing(pair, documents)
        out.extend(missing)
        if not missing:
            out.extend(_compare(pair, documents))
    return out
