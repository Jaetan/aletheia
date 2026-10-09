# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Run a documentation arm over files planted in a directory, as the gate runs it over a checkout.

The gate hands every arm the repository root, the tracked paths and the text of
every tracked Markdown file.  A test plants the files under a directory and
names which of them are tracked: each file it wrote, less those it leaves
untracked, plus those tracked but absent from the work tree.  No repository is
built, since an arm's claim is over the paths and texts it is handed; which
paths git tracks is the gate's own reading, held by its tests.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._common import RelPath
from tools.check_docs import read_documents

if TYPE_CHECKING:
    from collections.abc import Collection, Mapping
    from pathlib import Path

    from tools.docs_arms import Arm

    from aletheia.common_types import Prose


def plant(root: Path, files: Mapping[RelPath, Prose]) -> Path:
    """Write ``files`` under ``root``, making the directories they need, and return ``root``."""
    for rel, text in files.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text(text, encoding="utf-8")
    return root


def tracked_paths(
    root: Path, *, untracked: Collection[RelPath] = (), absent: Collection[RelPath] = ()
) -> list[RelPath]:
    """Name the paths the gate would read as tracked, in the order ``git ls-files`` gives.

    Every file under ``root`` outside a ``.git`` directory, less ``untracked``,
    plus ``absent``: tracked paths with nothing on disk.
    """
    written = {
        RelPath(path.relative_to(root).as_posix())
        for path in root.rglob("*")
        if path.is_file() and ".git" not in path.relative_to(root).parts
    }
    return sorted((written - set(untracked)) | set(absent))


def run_planted(
    arm: Arm,
    root: Path,
    *,
    untracked: Collection[RelPath] = (),
    absent: Collection[RelPath] = (),
) -> list[Prose]:
    """Run ``arm`` over ``root`` with the inputs the gate gives it, the tracked paths as named."""
    tracked = tracked_paths(root, untracked=untracked, absent=absent)
    return arm(root, tracked, read_documents(root, tracked))
