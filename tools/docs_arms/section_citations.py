# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A section number cited beside a Markdown link names a heading of the link's target.

A document cites a section of another by number, either inside a link's text
(``[CANCELLATION.md § 2.2](path)``) or right after the link (``[path](path)
§ 2.2``, the number allowed on the next line).  The link's own anchor is held
by the link check; the number beside it is held here, in every tracked
document: the target is a tracked Markdown document and one of its headings,
outside code fences, starts with that number and no more digits.  The subject
that is not among the documents, or that carries no such citation, is a
finding, so the scan cannot pass by matching nothing.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NamedTuple

from tools._common import RelPath, prose_lines
from tools.docs_arms import headings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping, Sequence
    from pathlib import Path

# The document this arm expects a section citation in.
SUBJECT = RelPath("go/README.md")

# A section number as the prose cites it: a section sign, then dotted digits.
_SECTION = re.compile(r"§\s*(\d+(?:\.\d+)*)")
# An inline link, with the section number cited right after it when there is one.
_LINK = re.compile(r"\[(?P<text>[^\]]*)\]\((?P<target>[^)]+)\)(?:\s*§\s*(?P<after>\d+(?:\.\d+)*))?")


class Citation(NamedTuple):
    """One section number cited beside one link, both as the document spells them."""

    section: Prose
    target: Prose


def citations(rel: RelPath, text: Prose) -> Iterator[Citation]:
    """Yield every section number cited beside a link in the prose of document ``rel``."""
    for m in _LINK.finditer("\n".join(line for _, line in prose_lines(rel, text))):
        in_text = _SECTION.search(m.group("text"))
        section = in_text.group(1) if in_text else m.group("after")
        if section is not None:
            yield Citation(Prose(section), Prose(m.group("target").strip().split(" ", 1)[0]))


def starts_with_section(heading: Prose, section: Prose) -> bool:
    """Whether ``heading`` opens with the whole of ``section``, not with a longer number."""
    return re.match(rf"{re.escape(section)}(?!\.?\d)", heading) is not None


def _document_findings(
    root: Path, rel: RelPath, documents: Mapping[RelPath, Prose]
) -> tuple[list[Prose], bool]:
    """Return the findings of one document and whether it cited any section at all."""
    out: list[Prose] = []
    cited = False
    doc = root / rel
    for section, target in citations(rel, documents[rel]):
        cited = True
        path = target.partition("#")[0]
        tgt = doc if path == "" else (doc.parent / path).resolve()
        tgt_rel = RelPath(tgt.relative_to(root).as_posix()) if tgt.is_relative_to(root) else None
        if tgt_rel is None or tgt_rel not in documents:
            out.append(
                Prose(f"{rel}: § {section} cited beside a link to {target}, not a tracked document")
            )
            continue
        if not any(starts_with_section(h, section) for h in headings(documents[tgt_rel])):
            out.append(
                Prose(f"{rel}: § {section} cited beside a link to {tgt_rel} names no heading there")
            )
    return out, cited


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per section citation that its target does not answer.

    One more names the subject when it is not among the documents or cites no section.
    """
    del tracked
    root = root.resolve()
    out: list[Prose] = []
    citing: set[RelPath] = set()
    for rel in documents:
        doc_findings, cited = _document_findings(root, rel, documents)
        out.extend(doc_findings)
        if cited:
            citing.add(rel)
    if SUBJECT not in documents:
        out.append(Prose(f"{SUBJECT}: not among the tracked documents, the subject of this arm"))
    elif SUBJECT not in citing:
        out.append(
            Prose(f"{SUBJECT}: carries no section citation beside a link, which this arm expects")
        )
    return out
