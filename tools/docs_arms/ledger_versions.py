# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The building guide's dependency ledger states no version, and says where the versions are.

Each layer's pins live in the build file the ledger names, so a version written
beside them is a second copy every bump has to find.  The section headed
``## Dependencies and Licenses`` is read line by line, its tables, code and
prose alike: no line may carry a version number, which is digits with a dot
between, a leading ``v`` taken with them (an SPDX licence identifier such as
``LGPL-3.0`` or ``BSL-1.0`` is not one, its number joined to its name), and no
table may have a ``Version`` or ``Versions`` column in its header.  The section
names where the versions are instead, in the sentence ``Versions are not
repeated here``.  A building guide untracked, unread or without the section is
a finding, since it leaves the claim with nothing to hold.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools import _markdown
from tools.docs_arms import BUILDING_GUIDE, missing

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    from tools._common import RelPath

LEDGER = Prose("## Dependencies and Licenses")
WHERE_THE_VERSIONS_ARE = Prose("Versions are not repeated here")

# Digits with a dot between, not joined to a name or another number before them.
_VERSION = re.compile(r"(?<![-\w.])v?\d+\.\d+(?:\.\d+)*")
_VERSION_COLUMN = re.compile(r"versions?", re.IGNORECASE)


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per version the ledger states, and one if it lost its pointer.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings, each naming the guide and the line: a version column per
        table header holding one, a version per number a line states, in line
        order, then the missing pointer; alone, the guide untracked or
        unread, or holding no ledger section.

    """
    del root
    if BUILDING_GUIDE not in documents:
        return [missing(BUILDING_GUIDE, tracked, Prose("its dependency ledger is unchecked"))]
    text = documents[BUILDING_GUIDE]
    found = _markdown.section(text, LEDGER)
    if found is None:
        return [Prose(f"{BUILDING_GUIDE}: has no {LEDGER} section")]
    out: list[Prose] = [
        Prose(f"{BUILDING_GUIDE}:{row.line}: a ledger table has a version column")
        for row in _markdown.table_rows(text)
        if found.first <= row.line < found.end
        and row.header
        and any(_VERSION_COLUMN.fullmatch(cell.strip()) for cell in row.shown)
    ]
    lines = _markdown.lines(text)[found.first - 1 : found.end - 1]
    out.extend(
        Prose(f"{BUILDING_GUIDE}:{number}: the ledger states the version {version[0]}")
        for number, line in enumerate(lines, start=found.first)
        for version in _VERSION.finditer(line)
    )
    if not any(WHERE_THE_VERSIONS_ARE in line for line in lines):
        out.append(Prose(f"{BUILDING_GUIDE}: the ledger no longer says {WHERE_THE_VERSIONS_ARE!r}"))
    return out
