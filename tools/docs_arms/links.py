# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every relative link and anchor in a tracked document resolves in a fresh checkout.

A link ``[text](target)`` or a reference definition ``[id]: target``, outside
fenced code and inline code spans, names a target relative to its document.
The target resolves when git tracks it, as a file or as a directory on the way
to one, or when it is the repository root: a fresh checkout holds what git
tracks, so a gitignored file sitting in one working tree does not count. A
target outside the repository is a finding even when it exists. An anchor
``#slug``, alone or after a tracked Markdown target, must be one of that
document's anchors, compared without case: a heading's GitHub slug, suffixed
``-1``, ``-2`` for a repeat, or an HTML ``name`` or ``id``. An anchor into any
other file is not checked. A link's title is not part of its target, and a
link with a scheme (``http://``, ``https://``, ``mailto:``, ``tel:``), a
``#!`` route or an ``<...>`` autolink is not resolved. A tree whose documents
carry no link to resolve is a finding, the scan holding nothing.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NamedTuple

from tools._common import RelPath, prose_lines
from tools.docs_arms import header_slugs, tracked_dirs

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

# Inline [text](target) and reference-style [id]: target.
_INLINE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
_REFDEF = re.compile(r"^\s*\[[^\]]+\]:\s*(\S+)")
_UNRESOLVED = ("http://", "https://", "mailto:", "tel:", "#!", "<")
_ROOT = RelPath(".")


class Checkout(NamedTuple):
    """What a fresh checkout holds: every tracked file, every directory on the way to one."""

    files: frozenset[RelPath]
    dirs: frozenset[RelPath]

    def holds(self, rel: RelPath) -> bool:
        """Whether ``rel``, repo-relative, is the root, a tracked file or a tracked directory."""
        return rel == _ROOT or rel in self.files or rel in self.dirs


def links(rel: RelPath, text: Prose) -> list[Prose]:
    """Return the link targets of document ``rel`` outside fenced code and inline code spans."""
    return [
        Prose(target)
        for _, line in prose_lines(rel, text)
        for pattern in (_INLINE, _REFDEF)
        for target in pattern.findall(line)
    ]


def _link_finding(
    root: Path,
    rel: RelPath,
    raw: Prose,
    checkout: Checkout,
    anchors: Mapping[RelPath, set[Prose]],
) -> Prose | None:
    """Return the finding for one link of document ``rel``, or None when it resolves.

    ``anchors`` holds each document's anchors in lower case, as they are compared.
    """
    link = raw.strip().split(" ", 1)[0]
    if link.startswith(_UNRESOLVED):
        return None
    target, _, anchor = link.partition("#")
    source = root / rel
    resolved = source if target == "" else (source.parent / target).resolve()
    if not resolved.is_relative_to(root):
        return Prose(f"{rel}: link escapes the repo -> {link}")
    rel_target = RelPath(resolved.relative_to(root).as_posix())
    if not checkout.holds(rel_target):
        return Prose(f"{rel}: broken link -> {link}")
    if anchor and rel_target in anchors and anchor.lower() not in anchors[rel_target]:
        return Prose(f"{rel}: broken anchor -> {link}")
    return None


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per link of a tracked document that does not resolve.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Every tracked Markdown file's text, by its repo-relative path.

    Returns:
        The findings, each naming the document that holds the link.

    """
    root = root.resolve()
    checkout = Checkout(frozenset(tracked), frozenset(tracked_dirs(tracked)))
    anchors = {
        rel: {Prose(slug.lower()) for slug in header_slugs(text)} for rel, text in documents.items()
    }
    found = [(rel, raw) for rel, text in documents.items() for raw in links(rel, text)]
    if not any(not raw.strip().startswith(_UNRESOLVED) for _, raw in found):
        return [Prose("README.md: no tracked document carries a link to resolve")]
    return [
        finding
        for rel, raw in found
        if (finding := _link_finding(root, rel, raw, checkout, anchors)) is not None
    ]
