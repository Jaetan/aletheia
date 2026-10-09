# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every ``cabal run shake -- <target>`` a tracked document shows is a target the Shakefile defines.

The commands sit in fenced blocks, so each document is read whole rather than
through its prose lines, and a wrapped command may put the target on the line
after the separator, in prose or behind a shell's backslash continuation, so
the two are matched across whitespace and continuations. The findings:
a document naming a target ``Shakefile.hs`` does not define, one per target;
a Shakefile missing from the tracked tree or defining no phony target, which
leaves nothing to check against; and a building guide showing no shake
command, since that is the document the commands are kept in.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._common import GateName, RelPath

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

SHAKEFILE = RelPath("Shakefile.hs")
BUILDING_GUIDE = RelPath("docs/development/BUILDING.md")

_PHONY = re.compile(r'\bphony\s+"([a-z][a-z0-9-]*)"')
_INVOCATION = re.compile(r"\bcabal run shake --(?:\s|\\\n)+([a-z][a-z0-9-]*)")


def phony_targets(shakefile: Path) -> set[GateName]:
    """Return every phony target ``shakefile`` defines."""
    text = shakefile.read_text(encoding="utf-8", errors="replace")
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
        documents: Every tracked Markdown file's text, by its repo-relative path.

    Returns:
        The findings, each naming the document concerned; the Shakefile when it
        is untracked or defines no target; the building guide when it shows no
        shake command.

    """
    if SHAKEFILE not in tracked:
        return [Prose(f"{SHAKEFILE}: not a tracked file")]
    defined = phony_targets(root / SHAKEFILE)
    if not defined:
        return [Prose(f"{SHAKEFILE}: defines no phony target")]
    out: list[Prose] = []
    guide_shows_a_command = False
    for rel, text in sorted(documents.items()):
        named = named_targets(text)
        if rel == BUILDING_GUIDE and named:
            guide_shows_a_command = True
        out.extend(
            Prose(f"{rel}: names a shake target {SHAKEFILE} does not define: {target}")
            for target in sorted(named - defined)
        )
    if not guide_shows_a_command:
        out.append(Prose(f"{BUILDING_GUIDE}: shows no cabal run shake command"))
    return out
