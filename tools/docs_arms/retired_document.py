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
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath
from tools.docs_arms import Unread, headings, missing, read_tracked

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence

RETIRED_DOCUMENT = RelPath("DEPENDENCIES.md")
LEDGER = RelPath("docs/development/BUILDING.md")
LEDGER_SECTION = Prose("Dependencies and Licenses")
RECORD_OF_THE_MOVE = RelPath("CHANGELOG.md")

_NAME = re.escape(RETIRED_DOCUMENT)
# The name as a whole word, its left boundary tested by a lookbehind after it: a pattern
# opening on its literal text is scanned for as fast as a substring.
_NAMES_RETIRED = re.compile(rf"{_NAME}(?<!\w{_NAME})\b")
_SELF = Path(__file__).resolve()

# A line of a file, counted from one.
LineNumber = NewType("LineNumber", int)


def _ledger_findings(tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]) -> list[Prose]:
    """Return the findings about the guide: untracked, unread, or without the ledger's section."""
    if LEDGER not in documents:
        return [missing(LEDGER, tracked, Prose("the ledger's one home is unchecked"))]
    if LEDGER_SECTION not in headings(documents[LEDGER]):
        return [Prose(f"{LEDGER}: has no {LEDGER_SECTION} section, the ledger's one home")]
    return []


def _mention_findings(root: Path, rel: RelPath, documents: Mapping[RelPath, Prose]) -> list[Prose]:
    """Return one finding per line of the tracked file ``rel`` that names the retired file.

    A line ends where the read puts a newline: at LF, CRLF or a lone CR, never at a form
    feed or another separator ``str.splitlines`` also honours; one pass counts the
    newlines between consecutive mentions.
    """
    text = documents.get(rel)
    if text is None:
        text = read_tracked(root, rel, Prose("its lines are unchecked"))
        if isinstance(text, Unread):
            return [text.finding]
    numbers: dict[LineNumber, None] = {}
    line, counted = 1, 0
    for mention in _NAMES_RETIRED.finditer(text):
        line += text.count("\n", counted, mention.start())
        counted = mention.start()
        numbers[LineNumber(line)] = None
    return [
        Prose(f"{rel}: line {number} names {RETIRED_DOCUMENT}, whose ledger lives in {LEDGER}")
        for number in numbers
    ]


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return the findings over the tree at ``root``, each naming its file.

    One finding per defect, and one per claim a file the work tree cannot give leaves unchecked.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative
            path; any other tracked file is read from ``root``, since the claim covers
            every one, a byte that is not UTF-8 not stopping the read.

    Returns:
        The findings, empty when the ledger has its one home and nothing else names
        the retired file.

    """
    own = RelPath(_SELF.relative_to(root).as_posix()) if _SELF.is_relative_to(root) else None
    found = _ledger_findings(tracked, documents)
    found.extend(
        Prose(f"{rel}: is tracked, a second home for the ledger beside {LEDGER}")
        for rel in tracked
        if Path(rel).name == RETIRED_DOCUMENT
    )
    for rel in tracked:
        if rel not in (RECORD_OF_THE_MOVE, own):
            found.extend(_mention_findings(root, rel, documents))
    return found
