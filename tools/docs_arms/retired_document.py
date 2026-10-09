# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The dependency ledger has one home, the Dependencies and Licenses section of the building guide.

The file that once held the ledger is retired: no tracked file bears its name,
and no tracked file outside the changelog, which records the move, names it,
so every reader is sent to the section. The guide itself must be tracked and
carry the section as a heading outside any code fence. This module names the
retired file to look for it, so its own lines are left out of the scan.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import TYPE_CHECKING

from tools._common import RelPath
from tools.docs_arms import headings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence

RETIRED_DOCUMENT = RelPath("DEPENDENCIES.md")
LEDGER = RelPath("docs/development/BUILDING.md")
LEDGER_SECTION = Prose("Dependencies and Licenses")
RECORD_OF_THE_MOVE = RelPath("CHANGELOG.md")

_NAMES_RETIRED = re.compile(rf"\b{re.escape(RETIRED_DOCUMENT)}\b")
_SELF = Path(__file__).resolve()


def _ledger_findings(documents: Mapping[RelPath, Prose]) -> list[Prose]:
    """Return the findings about the guide: untracked, or without the ledger's section."""
    if LEDGER not in documents:
        return [Prose(f"{LEDGER}: is not tracked, the ledger has no home")]
    if LEDGER_SECTION not in headings(documents[LEDGER]):
        return [Prose(f"{LEDGER}: has no {LEDGER_SECTION} section, the ledger's one home")]
    return []


def _mention_findings(root: Path, rel: RelPath, documents: Mapping[RelPath, Prose]) -> list[Prose]:
    """Return one finding per line of the tracked file ``rel`` that names the retired file."""
    text = documents.get(rel)
    if text is None:
        try:
            text = Prose((root / rel).read_text(encoding="utf-8", errors="replace"))
        except OSError:
            return [Prose(f"{rel}: could not be read, so its lines are unchecked")]
    if RETIRED_DOCUMENT not in text:  # most files never spell the name: skip their lines
        return []
    return [
        Prose(f"{rel}: line {number} names {RETIRED_DOCUMENT}, whose ledger lives in {LEDGER}")
        for number, line in enumerate(text.splitlines(), start=1)
        if _NAMES_RETIRED.search(line)
    ]


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return the findings over the tree at ``root``, one per defect, each naming its file.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Every tracked Markdown file's text, by its repo-relative path; any
            other tracked file is read from ``root``, since the claim covers every one.

    Returns:
        The findings, empty when the ledger has its one home and nothing else names
        the retired file.

    """
    root = root.resolve()
    own = RelPath(_SELF.relative_to(root).as_posix()) if _SELF.is_relative_to(root) else None
    found = _ledger_findings(documents)
    found.extend(
        Prose(f"{rel}: is tracked, a second home for the ledger beside {LEDGER}")
        for rel in tracked
        if Path(rel).name == RETIRED_DOCUMENT
    )
    for rel in tracked:
        if rel not in (RECORD_OF_THE_MOVE, own):
            found.extend(_mention_findings(root, rel, documents))
    return found
