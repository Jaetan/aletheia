# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every repository path the building guide names in backticks is tracked.

The guide is ``docs/development/BUILDING.md``.  A span in backticks names a
tree path when it is a path under a top-level source directory, a Dockerfile,
a bare Cabal or Markdown file name, or the project's own ``aletheia.agda-lib``;
the standard library's ``.agda-lib`` the guide names lives outside the tree.
A path with a directory part resolves when a tracked file or directory carries
it; a bare name resolves when a tracked file carries it as its base name, since
the guide names such files from the directory that holds them.  Build outputs
(``build/``, ``cpp/build``, ``python/.venv``) are not tracked and are not
checked.  A guide absent from the documents, or naming no tree path at all, is
a finding too, since the arm then checks nothing.
"""

from __future__ import annotations

import re
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, NamedTuple

from tools._common import RelPath
from tools.docs_arms import missing, tracked_dirs

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

GUIDE = RelPath("docs/development/BUILDING.md")

_SOURCE_DIRS = (
    "tools",
    "docs",
    "cpp",
    "go",
    "rust",
    "python",
    "src",
    "haskell-shim",
    "examples",
    "probes",
    "packaging",
    "benchmarks",
)
_TREE_PATH = re.compile(
    r"(?:(?:"
    + "|".join(_SOURCE_DIRS)
    + r")/[A-Za-z0-9_./-]+|Dockerfile[.A-Za-z]*|[A-Za-z_.-]+\.(?:cabal|md)|aletheia\.agda-lib)$"
)
_BUILD_OUTPUT = re.compile(r"(?:^|/)build(?:/|$)|\.venv")
_SPAN = re.compile(r"`([^`\s]+)`")


class _TrackedIndex(NamedTuple):
    """What a fresh checkout carries: its files, the directories on the way to one, base names."""

    files: frozenset[RelPath]
    dirs: frozenset[RelPath]
    names: frozenset[RelPath]


def _index(tracked: Sequence[RelPath]) -> _TrackedIndex:
    return _TrackedIndex(
        frozenset(tracked),
        frozenset(tracked_dirs(tracked)),
        frozenset(RelPath(PurePosixPath(path).name) for path in tracked),
    )


def tree_paths(text: Prose) -> list[RelPath]:
    """Return the tree paths ``text`` names in backticks, build outputs dropped, each once.

    A trailing slash names a directory and is dropped; the paths come back in
    the order the text first names them.
    """
    seen: dict[RelPath, None] = {}
    for span in _SPAN.findall(text):
        if _TREE_PATH.match(span) and not _BUILD_OUTPUT.search(span):
            seen.setdefault(RelPath(span.rstrip("/")), None)
    return list(seen)


def _resolves(path: RelPath, index: _TrackedIndex) -> bool:
    if "/" in path:
        return path in index.files or path in index.dirs
    return path in index.names


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per tree path the guide names that nothing tracks.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        A finding per untracked path the guide names, or one finding when the
        guide is not among ``documents`` or names no tree path.

    """
    del root
    if GUIDE not in documents:
        return [missing(GUIDE, tracked, Prose("the tree paths it names are unchecked"))]
    paths = tree_paths(documents[GUIDE])
    if not paths:
        return [Prose(f"{GUIDE}: names no tree path in backticks; the arm checks nothing")]
    index = _index(tracked)
    return [Prose(f"{GUIDE}: not tracked: {path}") for path in paths if not _resolves(path, index)]
