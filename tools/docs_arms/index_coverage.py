# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""docs/INDEX.md names every tracked document under docs/ and AGENTS/ and the root AGENTS.md.

The index calls itself the complete guide to the documentation, so a tracked
Markdown document under ``docs/`` or ``AGENTS/``, or the root ``AGENTS.md``,
that the index never names is a document a reader navigating by name cannot
reach. A document is named when its file name stands in the index as a whole
name, as ``names`` reads one. Whether the mention is a well-formed link is for
the gate's link check. The index is tracked and does not name itself; a tree
with no document to check against it is a finding, not a pass.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._common import RelPath
from tools.docs_arms import missing

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

INDEX = RelPath("docs/INDEX.md")
"""The index every document in scope must be named in."""

_SCOPE_PREFIXES = ("docs/", "AGENTS/")
_SCOPE_FILES = frozenset({RelPath("AGENTS.md")})


def in_scope(rel: RelPath) -> bool:
    """Return whether ``rel`` is a document the index must name.

    Args:
        rel: A tracked Markdown file's repo-relative POSIX path.

    Returns:
        True for a document under ``docs/`` or ``AGENTS/`` or the root
        ``AGENTS.md``, the index itself excepted.

    """
    return rel != INDEX and (rel.startswith(_SCOPE_PREFIXES) or rel in _SCOPE_FILES)


def names(index_text: Prose, file_name: RelPath) -> bool:
    """Return whether ``index_text`` mentions ``file_name`` as a whole name.

    Args:
        index_text: The index's full text, code spans included, since a name
            quoted in backticks still tells a reader where to look.
        file_name: The document's file name without its directory.

    Returns:
        True when the name occurs neither preceded nor followed by a letter, a
        digit or an underscore, so ``DESIGN.md`` is found inside neither
        ``SOMEIP_DESIGN.md`` nor ``DESIGN.mdx``; a dot or a hyphen is a
        boundary, so a name closing a sentence counts, as does the tail of
        ``OLD-DESIGN.md``.

    """
    pattern = r"(?<![A-Za-z0-9_])" + re.escape(file_name) + r"(?![A-Za-z0-9_])"
    return re.search(pattern, index_text) is not None


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per document in scope the index does not name.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        A finding naming the index for each unnamed document, in the order of
        ``documents``; one finding when the index is untracked or unread, or when no
        document read is in scope, since a scan over nothing holds nothing.

    """
    del root
    if INDEX not in documents:
        return [missing(INDEX, tracked, Prose("whether it names every document is unchecked"))]
    in_scope_docs = [rel for rel in documents if in_scope(rel)]
    if not in_scope_docs:
        return [Prose(f"{INDEX}: no document read under docs/ or AGENTS/ to check against it")]
    index_text = documents[INDEX]
    return [
        Prose(f"{INDEX}: does not name {rel}")
        for rel in in_scope_docs
        if not names(index_text, RelPath(rel.rsplit("/", 1)[-1]))
    ]
