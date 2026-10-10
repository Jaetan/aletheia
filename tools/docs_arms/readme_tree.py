# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The project tree README.md prints names exactly the top-level directories git tracks.

A curated tree reads as the whole shape of the project and goes stale silently
when a directory is added or removed, so the tree is compared with the
top-level directories a tracked path passes through. The tree is the first code
block (as CommonMark reads code blocks, ``tools._markdown``) whose first line
that is not blank reads ``aletheia/`` from its first column, spaces and tabs
after it allowed; its top-level directories are named by its lines opening on
``├── `` or ``└── ``, each name the run of characters, neither whitespace nor
``/``, that follows those marks and ends at a ``/``, so an entry with no ``/``
after its name is a file. A directory the tree lists and the repository
does not track is a finding, as is a tracked directory the tree omits. A README
printing no tree, untracked, or that the work tree cannot give, is a finding too,
so the scan never passes for want of a subject.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools import _markdown
from tools._common import RelPath
from tools.docs_arms import missing

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

README = RelPath("README.md")

# The tree: a code block whose first line that is not blank reads ``aletheia/``.
_ROOT = re.compile(r"(?:[ \t]*\n)*aletheia/[ \t]*(?:\n|$)")
# A top-level branch naming a directory. The lazy match stops at the first slash, so a
# branch drawn as a path such as ``src/Aletheia/`` names its top directory.
_BRANCH = re.compile(r"^[├└]── ([^/\s]+)/", re.MULTILINE)


def _listed(text: Prose) -> set[RelPath] | None:
    """Return the top-level directories the tree in ``text`` lists, or None without a tree."""
    for block in _markdown.code_blocks(text):
        if (root := _ROOT.match(block)) is not None:
            return {RelPath(m.group(1)) for m in _BRANCH.finditer(block, root.end())}
    return None


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per disagreement between README.md's tree and the tracked directories.

    Args:
        root: The repository root.
        tracked: Every tracked path, repo-relative, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        A finding for each directory listed but untracked, each tracked but
        unlisted, a README without a tree, or a README untracked or unread. The
        untracked listed ones come first, then the unlisted tracked ones, each
        in name order.

    """
    del root
    if README not in documents:
        return [missing(README, tracked, Prose("its project tree is unchecked"))]
    listed = _listed(documents[README])
    if listed is None:
        return [Prose(f"{README}: prints no project tree")]
    directories = {RelPath(path.split("/")[0]) for path in tracked if "/" in path}
    out = [
        Prose(f"{README}: the tree lists {name}/, which the repository does not track")
        for name in sorted(listed - directories)
    ]
    out.extend(
        Prose(f"{README}: the repository tracks {name}/, which the tree omits")
        for name in sorted(directories - listed)
    )
    return out
