# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The project tree README.md prints names exactly the top-level directories git tracks.

A curated tree reads as the whole shape of the project and goes stale silently
when a directory is added or removed, so the tree block opening ``aletheia/`` is
compared with the first path component of every tracked file: a directory the
tree lists and the repository does not track is a finding, as is a tracked
directory the tree omits. A README printing no tree, or a repository tracking
no README, is a finding too, so the scan never passes for want of a subject.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._common import RelPath

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

README = RelPath("README.md")

# The tree block: a line reading ``aletheia/`` followed by its branch lines, nested
# ones drawn under a ``│`` included.
_TREE = re.compile(r"^aletheia/\n((?:[├└│].*\n)+)", re.MULTILINE)
# A top-level branch naming a directory. The lazy match stops at the first slash, so a
# branch drawn as a path such as ``src/Aletheia/`` names its top directory.
_BRANCH = re.compile(r"^[├└]── (\S+?)/", re.MULTILINE)


def _listed(text: Prose) -> set[RelPath] | None:
    """Return the top-level directories the tree in ``text`` lists, or None without a tree."""
    match = _TREE.search(text)
    if match is None:
        return None
    return {RelPath(m.group(1)) for m in _BRANCH.finditer(match.group(1))}


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per disagreement between README.md's tree and the tracked directories.

    Args:
        root: The repository root.
        tracked: Every tracked path, repo-relative, as ``git ls-files`` prints it.
        documents: Every tracked Markdown file's text, by its repo-relative path.

    Returns:
        A finding for each directory listed but untracked, each tracked but
        unlisted, a README without a tree, or no tracked README at all. The
        untracked listed ones come first, then the unlisted tracked ones, each
        in name order.

    """
    del root
    if README not in documents:
        return [Prose(f"{README}: not a tracked document")]
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
