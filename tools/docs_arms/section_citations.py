# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A section number cited beside a Markdown link names a heading of the link's target.

A document cites a section of another by number, inside a link's text
(``[CANCELLATION.md § 2.2](path)``), right after the link (``[path](path)
§ 2.2``, the number allowed on the next line), or both, and every such number
is read.  The documents are read as CommonMark (``tools._markdown``): a link is
an inline or reference link, never an image or an autolink, and neither a code
span nor code is read for a number.  The link's own anchor is held by the link
check; the number beside it is held here, in every tracked document: the target
is a tracked Markdown document and one of its headings, as it reads, starts with
that number and no more digits; a target the work tree cannot give is named as
unread.  The subject that is untracked or unread, or that carries no such
citation, is a finding, so the scan cannot pass by matching nothing.
"""

from __future__ import annotations

import posixpath
import re
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, NamedTuple
from urllib.parse import unquote

from tools import _markdown
from tools._common import MARKDOWN_SUFFIXES, RelPath
from tools.docs_arms import missing

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Collection, Iterator, Mapping, Sequence
    from pathlib import Path

# The document this arm expects a section citation in.
SUBJECT = RelPath("go/README.md")
_SUBJECT_UNCHECKED = Prose("the section citations this arm expects in it are unchecked")

# A section number as the prose cites it: a section sign, then dotted digits.
_SECTION = re.compile(r"§\s*(\d+(?:\.\d+)*)")
# The number cited right after a link, the text after it opening on it.
_AFTER = re.compile(r"\s*" + _SECTION.pattern)


class Citation(NamedTuple):
    """One section number cited beside one link, both as CommonMark reads them."""

    section: Prose
    target: Prose


def citations(text: Prose) -> Iterator[Citation]:
    """Yield every section number cited beside a link in document ``text``."""
    for found in _markdown.links(text):
        if found.kind != "link":
            continue
        after = _AFTER.match(found.after)
        for section in (
            *(s.group(1) for s in _SECTION.finditer(found.prose)),
            *((after.group(1),) if after else ()),
        ):
            yield Citation(Prose(section), Prose(found.destination))


def starts_with_section(heading: Prose, section: Prose) -> bool:
    """Whether ``heading`` opens with the whole of ``section``, not with a longer number."""
    return re.match(rf"{re.escape(section)}(?!\.?\d)", heading) is not None


def _document_findings(
    rel: RelPath, tracked: Collection[RelPath], documents: Mapping[RelPath, Prose]
) -> tuple[list[Prose], bool]:
    """Return the findings of one document and whether it cited any section at all.

    A target is the path the link spells, joined to the document's directory and
    normalised as written, never through a symlink, since ``documents`` and
    ``tracked`` name paths as git does.  One missing from ``documents`` is a
    tracked Markdown file the read could not give, or no tracked document at all.
    """
    out: list[Prose] = []
    cited = False
    for section, target in citations(documents[rel]):
        cited = True
        path = unquote(target.partition("#")[0])
        # A target outside the root walks up to a ``../`` path that no document has.
        written = posixpath.normpath(posixpath.join(posixpath.dirname(rel), path))
        tgt_rel = rel if path == "" else RelPath(written)
        if tgt_rel not in documents:
            unread = tgt_rel in tracked and PurePosixPath(tgt_rel).suffix in MARKDOWN_SUFFIXES
            why = "which could not be read" if unread else "not a tracked document"
            out.append(Prose(f"{rel}: § {section} cited beside a link to {target}, {why}"))
            continue
        if not any(
            starts_with_section(h.text, section) for h in _markdown.headings(documents[tgt_rel])
        ):
            out.append(
                Prose(f"{rel}: § {section} cited beside a link to {tgt_rel} names no heading there")
            )
    return out, cited


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per section citation that its target does not answer.

    One more names the subject when it is untracked or unread, or cites no section.
    """
    del root
    tracked_set = frozenset(tracked)
    out: list[Prose] = []
    citing: set[RelPath] = set()
    for rel in documents:
        doc_findings, cited = _document_findings(rel, tracked_set, documents)
        out.extend(doc_findings)
        if cited:
            citing.add(rel)
    if SUBJECT not in documents:
        out.append(missing(SUBJECT, tracked_set, _SUBJECT_UNCHECKED))
    elif SUBJECT not in citing:
        out.append(
            Prose(f"{SUBJECT}: carries no section citation beside a link, which this arm expects")
        )
    return out
