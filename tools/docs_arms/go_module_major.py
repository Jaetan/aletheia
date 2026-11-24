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

A release moves a major with ``python -m tools.go_release move-major``, which
rewrites every tracked spelling of a module's path; a spelling it would not
find, or one written since, is held here.  Every tracked file but the history
(``CHANGELOG.md``, ``.archive/``) and the checksums (each ``go.sum``) spells a
module of the workspace ``go/go.work`` names, matched by its longest path, at
the major that module's ``go.mod`` declares: a spelling at another is a finding
naming the file, the spelling and the module's path.
"""

from __future__ import annotations

import posixpath
import re
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath
from tools._manifests import GoModule, ManifestError, ManifestText, go_module, go_uses
from tools.docs_arms import Unread, missing, read_tracked, read_tracked_bytes

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
GO_WORK = RelPath("go/go.work")
# The tracked files whose spellings are the past or a hash, never a module's path now.
_HISTORY = re.compile(r"^(?:CHANGELOG\.md|\.archive/.*|(?:.*/)?go\.sum)$")
# What makes a path's spelling go on: a character a path element holds, or a dot before one.
_GOES_ON = r"[A-Za-z0-9_~\-]|\.[A-Za-z0-9_~\-]"
_ELEMENT = r"[A-Za-z0-9_~\-]+(?:\.[A-Za-z0-9_~\-]+)*"
_SPELLED_MAJOR = re.compile(r"/v([0-9]+)(?=/|$)")
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


def _base(path: GoModule) -> GoModule:
    """Return ``path`` without its major suffix."""
    return GoModule(_SUFFIX.sub("", path))


def _workspace(
    root: Path, tracked: Sequence[RelPath], core: GoModule, unchecked: Prose
) -> list[GoModule] | Prose:
    """Return each module path go/go.work uses, the core first; the core alone without a go.work."""
    if GO_WORK not in tracked:
        return [core]
    work = read_tracked(root, GO_WORK, unchecked)
    if isinstance(work, Unread):
        return work.finding
    paths = [core]
    try:
        for use in go_uses(ManifestText(work), Prose(str(GO_WORK))):
            manifest = RelPath(posixpath.normpath(posixpath.join("go", use, "go.mod")))
            if manifest == GO_MOD:
                continue
            text = read_tracked(root, manifest, unchecked) if manifest in tracked else None
            if text is None or isinstance(text, Unread):
                return missing(manifest, tracked, unchecked)
            paths.append(go_module(ManifestText(text), Prose(str(manifest))))
    except ManifestError as exc:
        return Prose(f"{exc}, so {unchecked}")
    return paths


def stray_spellings(
    root: Path, tracked: Sequence[RelPath], paths: Sequence[GoModule]
) -> list[Prose]:
    """Return each spelling of a workspace module's path at a major its go.mod does not declare.

    ``paths`` holds the core first; a spelling belongs to the module whose path,
    less its major, is the longest prefix of it.
    """
    owners = sorted(paths, key=lambda path: len(_base(path)), reverse=True)
    spelling = re.compile(re.escape(_base(paths[0])) + f"(?:/{_ELEMENT})*(?!{_GOES_ON})")
    found: list[Prose] = []
    for rel in tracked:
        if _HISTORY.match(rel):
            continue
        data = read_tracked_bytes(root, rel, Prose(""))
        if isinstance(data, Unread):
            continue
        try:
            text = str(data, "utf-8")
        except UnicodeDecodeError:
            continue
        for spelled in dict.fromkeys(match[0] for match in spelling.finditer(text)):
            owner = next(
                path
                for path in owners
                if spelled == _base(path) or spelled.startswith(f"{_base(path)}/")
            )
            major = _SPELLED_MAJOR.match(spelled.removeprefix(_base(owner)))
            as_spelled = _base(owner) + (major[0] if major else "")
            if as_spelled != owner:
                found.append(
                    Prose(f"{rel}: spells {as_spelled}, where the module's path is {owner}")
                )
    return found


def _runbook_findings(
    tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose], unchecked: Prose
) -> list[Prose]:
    """Return the runbook's findings: untracked or unread, or not tagging or pushing the Go tag."""
    if RUNBOOK not in documents:
        return [missing(RUNBOOK, tracked, unchecked)]
    return [
        Prose(f"{RUNBOOK}: no longer {step} the Go module ({shown}), so {unchecked}")
        for line, step, shown in ((_TAG_LINE, "tags", GO_TAG), (_PUSH_LINE, "pushes", GO_PUSH))
        if line.search(documents[RUNBOOK]) is None
    ]


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
    out = _runbook_findings(tracked, documents, unchecked)
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
    if found is not None:
        out.append(found)
    paths = _workspace(
        root, tracked, path, Prose("the spellings of the Go modules' paths are unchecked")
    )
    if isinstance(paths, list):
        return [*out, *stray_spellings(root, tracked, paths)]
    return [*out, paths]
