# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every documented build tree is ignored, and no top-level venv but the sanctioned one is.

The C++ build file tells a reader which directories to configure with ``cmake -B``,
and the documents tell a reader which binary to build from ``go/`` with
``go build -o``; each of those paths is ignored, so a reader who follows the text
leaves nothing untracked behind. The one venv the project sanctions is ignored and
a venv at the top or in any other top-level directory is not, so a stray venv shows
up in ``git status``. The claim is about the tracked rules, not about what sits in
one working tree, so the tracked ignore files alone are asked, copied into a fresh
repository: a venv's own ``*`` file, the clone's ``info/exclude`` and the user's
global excludes would otherwise answer for them. A build file naming no tree, or
no document printing the Go build, is a finding: the scan would otherwise hold
nothing.
"""

from __future__ import annotations

import re
import shutil
from pathlib import Path, PurePosixPath
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING

from tools._common import RelPath, find_executable, git_clean_env, run_capture
from tools.docs_arms import tracked_dirs

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence

_IGNORE_FILE = RelPath(".gitignore")
_BUILD_FILE = RelPath("cpp/CMakeLists.txt")
_SANCTIONED_VENV = RelPath("python/.venv")
_BUILD_TREE = re.compile(r"cmake -B ([A-Za-z0-9_.-]+)")
_GO_BUILD = re.compile(r"go build -o ([A-Za-z0-9_.-]+) \./cmd/aletheia")


def _inside(tree: RelPath) -> RelPath:
    """Return a path inside ``tree``: a directory rule matches only what the tree holds."""
    return RelPath(f"{tree}/probe")


def _stray_venvs(tracked: Sequence[RelPath]) -> list[RelPath]:
    """Return a venv at the top and in every top-level directory, the sanctioned one left out."""
    tops = sorted(d for d in tracked_dirs(tracked) if "/" not in d)
    venvs = [RelPath(".venv"), *(RelPath(f"{top}/.venv") for top in tops)]
    return [venv for venv in venvs if venv != _SANCTIONED_VENV]


def _ignored(root: Path, tracked: Sequence[RelPath], paths: Sequence[RelPath]) -> set[RelPath]:
    """Return the subset of ``paths`` the tracked ignore files match.

    Every tracked ``.gitignore`` is copied into a fresh repository, made with
    no template so it has no ``info/exclude``, and the paths are asked there
    with the global excludes set aside, so no untracked rule answers.
    ``git check-ignore`` exits 1 when no path is ignored, which is an answer;
    any other failure is raised.
    """
    git = find_executable("git")
    with TemporaryDirectory() as scratch:
        fresh = Path(scratch)
        init = run_capture([git, "init", "-q", "--template=", str(fresh)], env=git_clean_env())
        if init.returncode != 0:
            message = f"git init failed in {fresh}: {init.stderr.strip()}"
            raise RuntimeError(message)
        for rel in tracked:
            if PurePosixPath(rel).name == _IGNORE_FILE:
                (fresh / rel).parent.mkdir(parents=True, exist_ok=True)
                _ = shutil.copyfile(root / rel, fresh / rel)
        asked = [git, "-C", str(fresh), "-c", "core.excludesFile=/dev/null", "check-ignore"]
        result = run_capture([*asked, "--", *paths], env=git_clean_env())
    if result.returncode not in (0, 1):
        message = f"git check-ignore failed: {result.stderr.strip()}"
        raise RuntimeError(message)
    return {RelPath(line) for line in result.stdout.splitlines()}


def _documented_trees(root: Path, tracked: Sequence[RelPath]) -> tuple[list[RelPath], list[Prose]]:
    """Return the build trees the C++ build file documents, or the finding of a scan that cannot."""
    if _BUILD_FILE not in tracked:
        return [], [Prose(f"{_BUILD_FILE}: the C++ build file is not tracked")]
    text = (root / _BUILD_FILE).read_text(encoding="utf-8", errors="replace")
    trees = sorted({RelPath(f"cpp/{name}") for name in _BUILD_TREE.findall(text)})
    if not trees:
        return [], [Prose(f"{_BUILD_FILE}: the build file documents no build directory")]
    return trees, []


def _documented_binaries(documents: Mapping[RelPath, Prose]) -> dict[RelPath, RelPath]:
    """Return each Go binary a document builds from ``go/``, with the first document printing it."""
    binaries: dict[RelPath, RelPath] = {}
    for rel, text in documents.items():
        for name in _GO_BUILD.findall(text):
            binaries.setdefault(RelPath(f"go/{name}"), rel)
    return binaries


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per documented path the ignore rules miss, or stray venv they hide.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Every tracked Markdown file's text, by its repo-relative path.

    Returns:
        The findings, each naming the file concerned; empty when the claim holds.

    """
    trees, out = _documented_trees(root, tracked)
    binaries = _documented_binaries(documents)
    strays = _stray_venvs(tracked)
    if not binaries:
        out.append(
            Prose(f"{_IGNORE_FILE}: no tracked document prints a build of the Go command line")
        )
    asked = (
        [_inside(tree) for tree in trees]
        + list(binaries)
        + [_inside(_SANCTIONED_VENV)]
        + [_inside(stray) for stray in strays]
    )
    ignored = _ignored(root, tracked, asked)
    out.extend(
        Prose(f"{_IGNORE_FILE}: a documented build tree is not ignored: {tree} ({_BUILD_FILE})")
        for tree in trees
        if _inside(tree) not in ignored
    )
    out.extend(
        Prose(f"{_IGNORE_FILE}: a documented Go build output is not ignored: {binary} ({rel})")
        for binary, rel in binaries.items()
        if binary not in ignored
    )
    if _inside(_SANCTIONED_VENV) not in ignored:
        out.append(Prose(f"{_IGNORE_FILE}: the sanctioned venv is not ignored: {_SANCTIONED_VENV}"))
    out.extend(
        Prose(f"{_IGNORE_FILE}: a venv outside the sanctioned path is hidden: {stray}")
        for stray in strays
        if _inside(stray) in ignored
    )
    return out
