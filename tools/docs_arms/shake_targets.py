# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every ``cabal run shake -- <target>`` a tracked document shows is a target the build defines.

The commands sit in fenced blocks, so each document is read whole rather than
through its prose lines, and a wrapped command may put the target on the line
after the separator, in prose or behind a shell's backslash continuation, so
the two are matched across whitespace and continuations. The targets are the
phony ones of the build program, ``Shakefile.hs`` and the modules under
``shake/``. The findings: a document naming a target no rule defines, one per
target; a ``Shakefile.hs`` untracked, a source of the build program unread, or
a program defining no phony target, which leaves nothing to check against; and
a building guide untracked, unread or showing no shake command, since that is
the document the commands are kept in.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._common import SHAKEFILE, GateName, RelPath, is_shake_source
from tools.docs_arms import Unread, missing, read_tracked

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

BUILDING_GUIDE = RelPath("docs/development/BUILDING.md")

# A declaration opens its line; a comment that spells one declares nothing.
_PHONY = re.compile(r'^\s*phony\s+"([a-z][a-z0-9-]*)"', re.MULTILINE)
_INVOCATION = re.compile(r"\bcabal run shake --(?:\s|\\\n)+([a-z][a-z0-9-]*)")
_TARGETS_UNCHECKED = Prose("the shake targets the documents name are unchecked")
_COMMANDS_UNCHECKED = Prose("the shake commands it keeps are unchecked")


def phony_targets(text: Prose) -> set[GateName]:
    """Return every phony target the build program's source ``text`` defines."""
    return {GateName(name) for name in _PHONY.findall(text)}


def named_targets(text: Prose) -> set[GateName]:
    """Return every target a ``cabal run shake`` command of ``text`` names, fences included."""
    return {GateName(name) for name in _INVOCATION.findall(text)}


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per target a document names that no rule of the build defines.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings, each naming the document concerned: per document in the
        order of ``documents``, by target name within one, then the building
        guide when it is not among them or shows no shake command; alone,
        ``Shakefile.hs`` when it is untracked, each source of the build program
        that is unread, or ``Shakefile.hs`` when the program defines no target.

    """
    if SHAKEFILE not in tracked:
        return [missing(SHAKEFILE, tracked, _TARGETS_UNCHECKED)]
    texts: list[Prose] = []
    unread: list[Prose] = []
    for rel in filter(is_shake_source, tracked):
        source = read_tracked(root, rel, _TARGETS_UNCHECKED)
        if isinstance(source, Unread):
            unread.append(source.finding)
        else:
            texts.append(source)
    if unread:
        return unread
    defined = {target for text in texts for target in phony_targets(text)}
    if not defined:
        return [Prose(f"{SHAKEFILE}: the build program defines no phony target")]
    out: list[Prose] = []
    guide_shows_a_command = False
    for rel, text in documents.items():
        named = named_targets(text)
        if rel == BUILDING_GUIDE and named:
            guide_shows_a_command = True
        out.extend(
            Prose(f"{rel}: names a shake target no rule defines: {target}")
            for target in sorted(named - defined)
        )
    if BUILDING_GUIDE not in documents:
        out.append(missing(BUILDING_GUIDE, tracked, _COMMANDS_UNCHECKED))
    elif not guide_shows_a_command:
        out.append(Prose(f"{BUILDING_GUIDE}: shows no cabal run shake command"))
    return out
