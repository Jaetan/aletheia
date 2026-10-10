# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every heading of a tracked document opens on a run of ``#``.

A setext heading is a paragraph that a line of ``=`` or ``-`` under it turns into a heading:
the paragraph above a ``---`` meant as a thematic break renders as a heading, as large as a
section's and with an anchor of its own. The documents write every heading as an ATX heading, so
a setext heading is a finding naming its first line. Each document is read as CommonMark
(``tools._markdown``), so an underline inside code is not read. A tree with no document read is a
finding, the scan holding nothing.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import _markdown

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    from tools._common import RelPath


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per setext heading of a tracked document.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings, each naming the document and the heading's first line, in the order of
        ``documents``; one naming ``README.md`` when no document was read.

    """
    del root, tracked
    if not documents:
        return [Prose("README.md: no document was read, so no heading is checked")]
    return [
        Prose(
            f"{rel}: line {heading.line} is a heading only because a line of = or - follows it; "
            + "write it with a run of #, or put a blank line before a thematic break"
        )
        for rel, text in documents.items()
        for heading in _markdown.headings(text)
        if heading.setext
    ]
