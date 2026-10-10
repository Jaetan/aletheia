# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every ``aletheia_<name>`` C symbol the building guide names is a foreign export of the shim.

The guide is ``docs/development/BUILDING.md``; the shim is ``haskell-shim/src/AletheiaFFI.hs``,
whose ``foreign export ccall`` lines are the C entry points the shared library carries. A symbol
is read wherever the guide spells it, in prose or in a code span, since a reader copies it from
either. A guide naming no symbol, a shim exporting none, and either file untracked or unread are
findings too: the arm then holds nothing. A shim byte that is not UTF-8 ends the name it sits in
rather than vanishing or stopping the read; the exports after it are read.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._common import RelPath
from tools.docs_arms import Unread, missing, read_tracked

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

GUIDE = RelPath("docs/development/BUILDING.md")
SHIM = RelPath("haskell-shim/src/AletheiaFFI.hs")

_NAMED = re.compile(r"\baletheia_[a-z_]+")
_EXPORTED = re.compile(r"^foreign export ccall (aletheia_[a-z_]+)", re.MULTILINE)
_NO_GUIDE = Prose("the arm has no guide to read")
_NO_EXPORTS = Prose("the arm has no exports to check the guide against")


def symbols_named(text: Prose) -> set[Prose]:
    """Return every ``aletheia_<name>`` token ``text`` spells, in prose or in a code span."""
    return {Prose(match) for match in _NAMED.findall(text)}


def symbols_exported(text: Prose) -> set[Prose]:
    """Return the C symbols the shim source ``text`` exports with ``foreign export ccall``."""
    return {Prose(match) for match in _EXPORTED.findall(text)}


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per symbol the guide names and the shim does not export, in name order.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings, each naming the file concerned; empty when every symbol the guide names
        is exported.

    """
    if GUIDE not in documents:
        return [missing(GUIDE, tracked, _NO_GUIDE)]
    if SHIM not in tracked:
        return [missing(SHIM, tracked, _NO_EXPORTS)]
    named = symbols_named(documents[GUIDE])
    if not named:
        return [Prose(f"{GUIDE}: names no aletheia_<name> symbol; the arm has nothing to hold")]
    shim = read_tracked(root, SHIM, _NO_EXPORTS)
    if isinstance(shim, Unread):
        return [shim.finding]
    exported = symbols_exported(shim)
    if not exported:
        return [Prose(f"{SHIM}: has no foreign export ccall line; the arm has nothing to hold")]
    return [
        Prose(f"{GUIDE}: names {symbol}, which {SHIM} does not export")
        for symbol in sorted(named - exported)
    ]
