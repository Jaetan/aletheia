# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Each Python row of the building guide's dependency ledger names its distribution's licence.

A row of ``### Runtime, Python layer`` names a distribution in its first cell
and a licence in its third; the licence is held to what the distribution
installed beside this interpreter records, its ``License-Expression`` (PEP
639), else its ``License``.  The gate runs in the project's one venv, which
installs every extra, so a distribution it does not find is a finding rather
than a skip, as is a row whose licence cell is missing or empty; a building guide untracked,
unread or without the section is a finding too.  The Rust rows' licences are
held where the crates are, after the Rust tests (``tools/check_rust_licences.py``).
"""

from __future__ import annotations

import importlib.metadata
from typing import TYPE_CHECKING

from tools._manifests import DistributionName
from tools.docs_arms import BUILDING_GUIDE, missing, section_rows
from tools.docs_arms.ledger_packages import PYTHON_LAYER

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence
    from pathlib import Path

    from tools._common import RelPath

_LICENCE_CELL = 2


def installed_licence(name: DistributionName) -> Prose | None:
    """Return the licence the distribution ``name`` installed here records, or None if absent."""
    try:
        recorded = importlib.metadata.metadata(name)
    except importlib.metadata.PackageNotFoundError:
        return None
    return Prose(recorded.get("License-Expression") or recorded.get("License") or "")


def licence_findings(
    guide: Prose, installed: Callable[[DistributionName], Prose | None]
) -> list[Prose]:
    """Return one finding per Python row of ``guide`` whose licence ``installed`` does not record.

    ``installed`` answers a distribution's recorded licence, or None when it is
    not installed.  The findings name the guide and the row's line, in row order.
    """
    rows = section_rows(guide, PYTHON_LAYER)
    if rows is None:
        return [Prose(f"{BUILDING_GUIDE}: has no {PYTHON_LAYER} section")]
    out: list[Prose] = []
    for row in rows:
        name = DistributionName(row.shown[0])
        where = f"{BUILDING_GUIDE}:{row.line}"
        if len(row.shown) <= _LICENCE_CELL or not row.shown[_LICENCE_CELL]:
            out.append(Prose(f"{where}: the row for {name} states no licence"))
            continue
        recorded = installed(name)
        if recorded is None:
            out.append(Prose(f"{where}: {name} is not installed, so its licence is unchecked"))
        elif recorded != row.shown[_LICENCE_CELL]:
            out.append(
                Prose(
                    f"{where}: the ledger says {name} is {row.shown[_LICENCE_CELL]}, "
                    + f"its metadata records {recorded!r}"
                )
            )
    return out


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per Python row whose licence the installed distribution does not record.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings of ``licence_findings`` over the guide and the installed
        distributions; alone, the guide untracked or unread.

    """
    del root
    if BUILDING_GUIDE not in documents:
        return [missing(BUILDING_GUIDE, tracked, Prose("its Python licences are unchecked"))]
    return licence_findings(documents[BUILDING_GUIDE], installed_licence)
