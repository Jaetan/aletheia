# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The command line requires every module the Excel module requires, at that version or later.

Built outside the Go workspace, the command line resolves the Excel module at
the commit its ``go.mod`` names, whose own requirements can be older than the
tree's, and selects for each module the newest version any requirement names.
So that it selects, for each module ``go/excel/go.mod`` requires, at least the
version the Excel module's tree requires, ``go/cmd/aletheia/go.mod`` requires
that module at that version or later, indirect requirements included.  Versions
are ordered as Go orders them, by Semantic Versioning precedence, build metadata
such as ``+incompatible`` aside.  Each module required below the Excel module's
version, or not at all, is a finding, as is a version either file spells that
the ordering cannot read and a file untracked, unread or carrying a require its
reader refuses, since each leaves the claim with nothing to hold.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NamedTuple, NewType

from tools._common import RelPath
from tools._manifests import (
    GoModule,
    GoRequire,
    GoVersion,
    ManifestError,
    ManifestText,
    go_requires,
)
from tools.docs_arms import Unread, missing, read_tracked

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

EXCEL_GO_MOD = RelPath("go/excel/go.mod")
CLI_GO_MOD = RelPath("go/cmd/aletheia/go.mod")

# A number of a version's release, and a pre-release identifier that is not one.
VersionNumber = NewType("VersionNumber", int)
PreReleaseWord = NewType("PreReleaseWord", str)

# A module version as Go spells one: vMAJOR.MINOR.PATCH, a pre-release, build metadata.
_SEMVER = re.compile(
    r"v(?P<major>0|[1-9]\d*)\.(?P<minor>0|[1-9]\d*)\.(?P<patch>0|[1-9]\d*)"
    + r"(?:-(?P<pre>[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?(?:\+[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?",
    re.ASCII,
)
_NUMERIC = re.compile(r"\d+")


class _Identifier(NamedTuple):
    """One pre-release identifier as precedence orders it: numbers first, by value; then words."""

    word: bool
    number: VersionNumber
    text: PreReleaseWord


class Precedence(NamedTuple):
    """A version's place in Semantic Versioning precedence, compared field by field."""

    release: tuple[VersionNumber, VersionNumber, VersionNumber]
    # A release ranks above every pre-release of it.
    final: bool
    pre: tuple[_Identifier, ...]


class _Required(NamedTuple):
    """A module's required version, and its place in precedence."""

    version: GoVersion
    place: Precedence


def precedence(version: GoVersion) -> Precedence | None:
    """Return ``version``'s place in Semantic Versioning precedence, or None for no Go version."""
    found = _SEMVER.fullmatch(version)
    if found is None:
        return None
    release = (
        VersionNumber(int(found["major"])),
        VersionNumber(int(found["minor"])),
        VersionNumber(int(found["patch"])),
    )
    if found["pre"] is None:
        return Precedence(release, final=True, pre=())
    return Precedence(
        release,
        final=False,
        pre=tuple(
            _Identifier(word=False, number=VersionNumber(int(part)), text=PreReleaseWord(""))
            if _NUMERIC.fullmatch(part)
            else _Identifier(word=True, number=VersionNumber(0), text=PreReleaseWord(part))
            for part in found["pre"].split(".")
        ),
    )


def _requires(root: Path, tracked: Sequence[RelPath], rel: RelPath) -> list[GoRequire] | Prose:
    """Return the requires of the go.mod at ``rel``, or the finding leaving the claim unheld."""
    unchecked = Prose("the command line's requirements are unchecked")
    if rel not in tracked:
        return missing(rel, tracked, unchecked)
    text = read_tracked(root, rel, unchecked)
    if isinstance(text, Unread):
        return text.finding
    try:
        return go_requires(ManifestText(text), Prose(rel))
    except ManifestError as exc:
        return Prose(str(exc))


def _ordered(
    rel: RelPath, requires: Sequence[GoRequire]
) -> dict[GoModule, _Required] | list[Prose]:
    """Return each module ``requires`` names with its version's place, or a finding per unread."""
    ordered: dict[GoModule, _Required] = {}
    unread: list[Prose] = []
    for found in requires:
        place = precedence(found.version)
        if place is None:
            unread.append(
                Prose(f"{rel}: requires {found.module} at {found.version}, no Go module version")
            )
        else:
            ordered[found.module] = _Required(found.version, place)
    return unread or ordered


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per module the Excel module requires and the command line falls behind.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text; this arm reads none of it.

    Returns:
        The findings in the Excel module's order of requires: a module the
        command line requires below that version, or not at all.  Instead,
        each version either file spells that is no Go module version; instead
        again, a file untracked, unread or carrying a require its reader refuses.

    """
    del documents
    excel = _requires(root, tracked, EXCEL_GO_MOD)
    cli = _requires(root, tracked, CLI_GO_MOD)
    if not isinstance(excel, list) or not isinstance(cli, list):
        return [result for result in (excel, cli) if not isinstance(result, list)]
    excel_ordered = _ordered(EXCEL_GO_MOD, excel)
    cli_ordered = _ordered(CLI_GO_MOD, cli)
    if isinstance(excel_ordered, list) or isinstance(cli_ordered, list):
        return [
            *(excel_ordered if isinstance(excel_ordered, list) else []),
            *(cli_ordered if isinstance(cli_ordered, list) else []),
        ]
    out: list[Prose] = []
    for module, wanted in excel_ordered.items():
        held = cli_ordered.get(module)
        if held is None:
            out.append(
                Prose(
                    f"{CLI_GO_MOD}: requires no {module}, which {EXCEL_GO_MOD} requires"
                    + f" at {wanted.version}"
                )
            )
        elif held.place < wanted.place:
            out.append(
                Prose(
                    f"{CLI_GO_MOD}: requires {module} at {held.version}, below the"
                    + f" {wanted.version} {EXCEL_GO_MOD} requires"
                )
            )
    return out
