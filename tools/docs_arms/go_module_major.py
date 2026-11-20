# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The release runbook's Go tag makes the core Go module fetchable at the release's version.

The runbook tags a release ``go/vX.Y.Z`` beside ``vX.Y.Z`` and pushes both, and
Go serves the module at ``go/vX.Y.Z`` only when the path ``go/go.mod`` declares
carries that major: a path ending ``/vX`` for a major of two or more, no such
suffix below.  The release's version is the one ``haskell-shim/aletheia.cabal``
states, the first of its numbers the major.  A path whose major differs is a
finding naming both, as is a runbook no longer tagging or pushing ``go/vX.Y.Z``
on a line of its own, and a file untracked, unread or without its path or
version, since each leaves the tag with nothing to hold.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath
from tools._manifests import GoModule, ManifestError, ManifestText, go_module
from tools.docs_arms import Unread, missing, read_tracked

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

# The version the cabal file states, as it spells it; and a major version, its first number.
CabalVersion = NewType("CabalVersion", str)
Major = NewType("Major", int)

RUNBOOK = RelPath("docs/development/RELEASE.md")
GO_MOD = RelPath("go/go.mod")
CABAL = RelPath("haskell-shim/aletheia.cabal")
GO_TAG = Prose("git tag -s go/vX.Y.Z")
GO_PUSH = Prose("git push origin ... go/vX.Y.Z")
# Go's first major whose module path must end in the matching /vN.
FIRST_SUFFIXED = Major(2)

# A major suffix Go accepts: v and a number without a leading zero, the path's last element.
_SUFFIX = re.compile(r"/v([1-9][0-9]*)$")
# Cabal's field names are case-insensitive, and a blank may precede the colon.
_VERSION = re.compile(
    r"^version[ \t]*:\s*(([0-9]+)(?:\.[0-9]+)*)[ \t]*$", re.MULTILINE | re.IGNORECASE
)
_TAG_LINE = re.compile(r"^git tag -s go/vX\.Y\.Z\b", re.MULTILINE)
_PUSH_LINE = re.compile(r"^git push origin\b.*\sgo/vX\.Y\.Z\b", re.MULTILINE)


def path_finding(path: GoModule, version: CabalVersion, major: Major) -> Prose | None:
    """Return the finding of a module ``path`` whose major is not the release ``major``, or None."""
    suffix = _SUFFIX.search(path)
    carried = Major(int(suffix[1])) if suffix else None
    if major >= FIRST_SUFFIXED and carried != major:
        has = f"ends /v{carried}" if carried is not None else "carries no major suffix Go accepts"
        return Prose(
            f"{GO_MOD}: the module path {path} {has}, where {CABAL}'s version {version} is a "
            + f"release of major {major}: Go fetches the tag go/v{major}.x.y only for a path "
            + f"ending /v{major}"
        )
    if major < FIRST_SUFFIXED and carried is not None:
        return Prose(
            f"{GO_MOD}: the module path {path} ends /v{carried}, where {CABAL}'s version "
            + f"{version} is a release of major {major}: Go fetches the tag go/v{major}.x.y "
            + "only for a path without a major suffix"
        )
    return None


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return the findings of the core Go module's path against the release's major.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The runbook's findings, untracked or unread, or no longer tagging or
        pushing the Go tag on a line of its own; then each of ``go/go.mod`` and
        the cabal file untracked, unread or without its module path or version;
        or, all read, the path's finding.

    """
    unchecked = Prose("the major the Go module's path carries is unchecked")
    out: list[Prose] = []
    if RUNBOOK not in documents:
        out.append(missing(RUNBOOK, tracked, unchecked))
    else:
        for line, step, shown in ((_TAG_LINE, "tags", GO_TAG), (_PUSH_LINE, "pushes", GO_PUSH)):
            if line.search(documents[RUNBOOK]) is None:
                out.append(
                    Prose(f"{RUNBOOK}: no longer {step} the Go module ({shown}), so {unchecked}")
                )
    texts: dict[RelPath, Prose] = {}
    for rel in (GO_MOD, CABAL):
        if rel not in tracked:
            out.append(missing(rel, tracked, unchecked))
            continue
        text = read_tracked(root, rel, unchecked)
        if isinstance(text, Unread):
            out.append(text.finding)
        else:
            texts[rel] = text
    if GO_MOD not in texts or CABAL not in texts:
        return out
    try:
        path = go_module(ManifestText(texts[GO_MOD]), Prose(str(GO_MOD)))
    except ManifestError as exc:
        return [*out, Prose(f"{exc}, so {unchecked}")]
    stated = _VERSION.search(texts[CABAL])
    if stated is None:
        return [*out, Prose(f"{CABAL}: states no version, so {unchecked}")]
    found = path_finding(path, CabalVersion(stated[1]), Major(int(stated[2])))
    return [*out, found] if found is not None else out
