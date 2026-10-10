# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every ``cabal run shake -- <target>`` a tracked document shows is a target the Shakefile defines.

The commands sit in fenced blocks, so each document is read whole rather than
through its prose lines, and a wrapped command may put the target on the line
after the separator, in prose or behind a shell's backslash continuation, so
the two are matched across whitespace and continuations. The findings:
a document naming a target ``Shakefile.hs`` does not define, one per target;
a Shakefile untracked, unread or defining no phony target, which leaves
nothing to check against; and a building guide untracked, unread or showing
no shake command, since that is the document the commands are kept in.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._common import GateName, RelPath
from tools.docs_arms import Unread, missing, read_tracked

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

SHAKEFILE = RelPath("Shakefile.hs")
BUILDING_GUIDE = RelPath("docs/development/BUILDING.md")

_PHONY = re.compile(r'\bphony\s+"([a-z][a-z0-9-]*)"')
_INVOCATION = re.compile(r"\bcabal run shake --(?:\s|\\\n)+([a-z][a-z0-9-]*)")
_TARGETS_UNCHECKED = Prose("the shake targets the documents name are unchecked")
_COMMANDS_UNCHECKED = Prose("the shake commands it keeps are unchecked")


def phony_targets(text: Prose) -> set[GateName]:
    """Return every phony target the Shakefile source ``text`` defines."""
    return {GateName(name) for name in _PHONY.findall(text)}


def named_targets(text: Prose) -> set[GateName]:
    """Return every target a ``cabal run shake`` command of ``text`` names, fences included."""
    return {GateName(name) for name in _INVOCATION.findall(text)}


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per target a document names that the Shakefile does not define.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings, each naming the document concerned: per document in the
        order of ``documents``, by target name within one, then the building
        guide when it is not among them or shows no shake command; alone, the
        Shakefile when it is untracked, unread or defines no target.

    """
    if SHAKEFILE not in tracked:
        return [missing(SHAKEFILE, tracked, _TARGETS_UNCHECKED)]
    shakefile = read_tracked(root, SHAKEFILE, _TARGETS_UNCHECKED)
    if isinstance(shakefile, Unread):
        return [shakefile.finding]
    defined = phony_targets(shakefile)
    if not defined:
        return [Prose(f"{SHAKEFILE}: defines no phony target")]
    out: list[Prose] = []
    guide_shows_a_command = False
    for rel, text in documents.items():
        named = named_targets(text)
        if rel == BUILDING_GUIDE and named:
            guide_shows_a_command = True
        out.extend(
            Prose(f"{rel}: names a shake target {SHAKEFILE} does not define: {target}")
            for target in sorted(named - defined)
        )
    if BUILDING_GUIDE not in documents:
        out.append(missing(BUILDING_GUIDE, tracked, _COMMANDS_UNCHECKED))
    elif not guide_shows_a_command:
        out.append(Prose(f"{BUILDING_GUIDE}: shows no cabal run shake command"))
    return out
