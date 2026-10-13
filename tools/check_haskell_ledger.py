# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the building guide's Haskell ledger to what the kernel library links and the bundle carries.

The section ``### Runtime, Haskell layer`` of ``docs/development/BUILDING.md``
holds three tables, in this order, each held to the library both ways:

* the Haskell packages: the GHC packages among the libraries the bundle
  carries, the runtime system named ``GHC RTS``, each row's licence the one
  ``ghc-pkg`` records for its package;
* the other libraries the bundle carries, which GHC's lib directory supplies;
* the system libraries the library links and the bundle does not carry: each
  is a ``lib<name>`` some row names, and each row names at least one of them,
  since the C library's parts a row lists (``libpthread``, ``librt``,
  ``libdl``) are libraries of their own before glibc 2.34 and part of ``libc``
  after it, so which of them a build links is the toolchain's.

The libraries the bundle carries are the dist rule's own reading, every
library ``ldd`` resolves under GHC's lib directory (``getGhcDeps`` in
``shake/Shared.hs``), handed in by the Shake target ``check-haskell-ledger``,
which builds the library first.  What the library links is what ``ldd`` resolves
for it, an entry it resolves to no file of a name (the vDSO, the dynamic loader,
a preloaded library) aside.

Usage::

    python -m tools.check_haskell_ledger LIBRARY BUNDLED...

Exit 0 when the three tables hold; 1 when a table and the library disagree or
a row's licence is not the one ghc-pkg records; 2 when the guide, its section
or its three tables cannot be read, ldd or ghc-pkg is not on the search path,
or ldd cannot read the library.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType, cast

from tools import _markdown
from tools._common import emit, find_executable, run_capture
from tools.docs_arms import BUILDING_GUIDE
from tools.sbom_generate import GhcPackage, ghc_library

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable

REPO = Path(__file__).resolve().parent.parent
HELD, DIFFERS, UNCHECKED = ExitStatus(0), ExitStatus(1), ExitStatus(2)

HASKELL_LAYER = Prose("### Runtime, Haskell layer (`libaletheia-ffi.so`)")
# The row the runtime system's package, ``rts``, is listed under.
RTS_ROW = Prose("GHC RTS")
RTS = GhcPackage("rts")

# A shared library's name without its ``lib`` and its ``.so`` suffixes.
LibraryName = NewType("LibraryName", str)

_TABLES = 3
_LICENCE_CELL = 1
# ``libgmp.so.10 => /usr/lib/.../libgmp.so.10 (0x...)``: the name and what it resolves to.
_RESOLVED = re.compile(r"^\s*(\S+)\s+=>\s+(\S+)", re.MULTILINE)
_FILE = re.compile(r"^lib(.+?)\.so")
_NAMED = re.compile(r"\blib([A-Za-z0-9_+-]+)")


class HaskellTables(NamedTuple):
    """The body rows of the Haskell section's three tables, in the order the guide holds them."""

    packages: list[_markdown.Row]
    others: list[_markdown.Row]
    system: list[_markdown.Row]


class LedgerUnreadError(Exception):
    """The guide's Haskell section, or its three tables, could not be read."""


def library_name(path: Path) -> LibraryName | None:
    """Return the name of the shared library at ``path``, or None if it is not ``lib<name>.so``."""
    found = _FILE.match(path.name)
    return None if found is None else LibraryName(found[1])


def linked(ldd_output: Prose) -> set[LibraryName]:
    """Return every library ``ldd_output`` resolves to a file by name, by its library name."""
    return {
        name
        for found in _RESOLVED.finditer(ldd_output)
        if (name := library_name(Path(found[1]))) is not None
    }


def tables(guide: Prose) -> HaskellTables:
    """Return the body rows of each table of the guide's Haskell section, raising unless three."""
    section = _markdown.section(guide, HASKELL_LAYER)
    if section is None:
        message = f"{BUILDING_GUIDE}: has no {HASKELL_LAYER} section"
        raise LedgerUnreadError(message)
    found: list[list[_markdown.Row]] = []
    for row in _markdown.table_rows(guide):
        if section.first <= row.line < section.end:
            if row.header:
                found.append([])
            elif found:
                found[-1].append(row)
    if len(found) != _TABLES:
        message = f"{BUILDING_GUIDE}: {HASKELL_LAYER} holds {len(found)} tables, not {_TABLES}"
        raise LedgerUnreadError(message)
    return HaskellTables(found[0], found[1], found[2])


def _compared(table: Prose, held: set[Prose], listed: set[Prose], beyond: Prose) -> list[Prose]:
    """Return a finding per name in ``held`` the table lacks, then per name it adds.

    ``beyond`` says what a name the table adds is not, to end its finding.
    """
    return [
        *(Prose(f"the {table} table lacks {name}") for name in sorted(held - listed)),
        *(Prose(f"the {table} table names {name}, {beyond}") for name in sorted(listed - held)),
    ]


def _named(rows: Iterable[_markdown.Row]) -> set[Prose]:
    """Return every ``lib<name>`` the first cells of ``rows`` name, by its name."""
    return {Prose(found[1]) for row in rows for found in _NAMED.finditer(row.shown[0])}


def ledger_findings(
    guide: Prose,
    links: set[LibraryName],
    bundled: Iterable[Path],
    licence_of: Callable[[GhcPackage], Prose | None],
) -> list[Prose]:
    """Return every way the guide's Haskell tables and the library disagree.

    ``links`` is what the library links, ``bundled`` the libraries the bundle
    carries, and ``licence_of`` answers the licence ghc-pkg records for a
    package, or None when it records none.  Raises ``LedgerUnreadError`` when
    the section or its three tables cannot be read.
    """
    found = tables(guide)
    carried = list(bundled)
    held = {library.package for so in carried if (library := ghc_library(so)) is not None}
    beside = {
        name for so in carried if ghc_library(so) is None and (name := library_name(so)) is not None
    }
    carried_names = {name for so in carried if (name := library_name(so)) is not None}
    by_row = {
        RTS if row.shown[0] == RTS_ROW else GhcPackage(row.shown[0]): row for row in found.packages
    }
    out = [
        *_compared(
            Prose("Haskell package"),
            {Prose(p) for p in held},
            {Prose(p) for p in by_row},
            Prose("which the bundle does not carry"),
        ),
        *_compared(
            Prose("bundled library"),
            {Prose(n) for n in beside},
            _named(found.others),
            Prose("which the bundle does not carry"),
        ),
        *_system_findings(found.system, {Prose(n) for n in links - carried_names}),
    ]
    return [*out, *_licence_findings(by_row, held, licence_of)]


def _system_findings(rows: list[_markdown.Row], linked_here: set[Prose]) -> list[Prose]:
    """Return a finding per system library no row names, then per row naming none linked."""
    named = _named(rows)
    return [
        *(Prose(f"the system library table lacks {name}") for name in sorted(linked_here - named)),
        *(
            Prose(
                f"the system library table's row {row.shown[0]!r} names no library "
                + "the library links from the system"
            )
            for row in rows
            if not _named([row]) & linked_here
        ),
    ]


def _licence_findings(
    by_row: dict[GhcPackage, _markdown.Row],
    held: set[GhcPackage],
    licence_of: Callable[[GhcPackage], Prose | None],
) -> list[Prose]:
    """Return a finding per carried package whose row's licence ghc-pkg does not record."""
    out: list[Prose] = []
    for package, row in by_row.items():
        if package not in held:
            continue
        recorded = licence_of(package)
        stated = row.shown[_LICENCE_CELL] if len(row.shown) > _LICENCE_CELL else None
        if recorded != stated:
            out.append(
                Prose(f"{package}: the ledger says {stated!r}, ghc-pkg records {recorded!r}")
            )
    return out


def ghc_pkg_licence(package: GhcPackage) -> Prose | None:
    """Return the licence ghc-pkg records for ``package``, or None when it records none."""
    read = run_capture([find_executable("ghc-pkg"), "field", package, "license", "--simple-output"])
    words = read.stdout.split()
    return Prose(words[0]) if read.returncode == 0 and words else None


def main() -> ExitStatus:
    """Report each way the Haskell ledger and the library on the command line disagree."""
    parser = argparse.ArgumentParser(description="Hold the Haskell ledger to the library.")
    _ = parser.add_argument("library", type=Path, help="the kernel library ldd reads")
    _ = parser.add_argument(
        "bundled", type=Path, nargs="+", help="the libraries the bundle carries beside it"
    )
    args = parser.parse_args()
    library, bundled = cast("Path", args.library), cast("list[Path]", args.bundled)
    try:
        ldd = run_capture([find_executable("ldd"), str(library)])
        if ldd.returncode != 0:
            emit(f"check-haskell-ledger: ldd cannot read {library}: {ldd.stderr.strip()}")
            return UNCHECKED
        guide = Prose((REPO / BUILDING_GUIDE).read_text(encoding="utf-8"))
        found = ledger_findings(guide, linked(Prose(ldd.stdout)), bundled, ghc_pkg_licence)
    except (OSError, RuntimeError, LedgerUnreadError) as exc:
        emit(f"check-haskell-ledger: {exc}; the Haskell ledger is unchecked")
        return UNCHECKED
    for finding in found:
        emit(f"check-haskell-ledger: {BUILDING_GUIDE}: {finding}")
    if found:
        return DIFFERS
    emit("check-haskell-ledger: the Haskell ledger names what the library links and carries")
    return HELD


if __name__ == "__main__":
    sys.exit(main())
