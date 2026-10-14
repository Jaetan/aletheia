# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the Rust rows of the building guide's dependency ledger to the licences cargo records.

A row of ``### Runtime, Rust layer`` in ``docs/development/BUILDING.md`` names
a crate in its first cell and a licence in its second; the licence is held to
the ``license`` that ``cargo metadata --offline`` records for the crate, read
in the directory of every tracked ``Cargo.toml`` under ``rust/`` (the first
directory that resolves a crate answers for it) and filtered to the platform
rustc builds for here: the tests fetch only the crates that platform builds,
and an unfiltered read resolves every platform's.  Which crates the rows name is
the documentation gate's ledger arm's claim; this one is the licences, and runs
in the Rust lane after the Rust tests, which leave every crate the manifests
resolve in cargo's registry, so the read needs no network.

Usage::

    python -m tools.check_rust_licences

Exit 0 when every row's licence is the one cargo records; 1 when a row's
differs, names a crate cargo does not resolve, or states none; 2 when the guide
or its section cannot be read, no Cargo manifest is tracked, cargo is not on
the search path, or it cannot read a manifest's metadata offline, which leaves
the licences unchecked.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NewType, TypedDict, cast

from tools._common import emit, find_executable, git_ls_files, run_capture
from tools.docs_arms import BUILDING_GUIDE, section_rows
from tools.docs_arms.ledger_packages import RUST_LAYER, rust_manifests

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

REPO = Path(__file__).resolve().parent.parent
HELD, DIFFERS, UNCHECKED = ExitStatus(0), ExitStatus(1), ExitStatus(2)

# A Rust crate's name, as cargo reports it, and a platform as rustc names it.
CrateName = NewType("CrateName", str)
Platform = NewType("Platform", str)

_LICENCE_CELL = 1


class _Package(TypedDict):
    name: CrateName
    license: Prose | None


class _Metadata(TypedDict):
    packages: list[_Package]


class CargoUnreadError(Exception):
    """cargo could not read a manifest's metadata offline."""


def host_platform() -> Platform:
    """Return the platform rustc builds for here, raising ``CargoUnreadError`` if it names none."""
    read = run_capture([find_executable("rustc"), "-vV"])
    host = next(
        (
            line.removeprefix("host: ")
            for line in read.stdout.splitlines()
            if line.startswith("host: ")
        ),
        "",
    )
    if read.returncode != 0 or not host:
        message = f"rustc -vV names no host platform: {read.stderr.strip()}"
        raise CargoUnreadError(message)
    return Platform(host)


def cargo_licences(directories: list[Path], platform: Platform) -> dict[CrateName, Prose | None]:
    """Return the licence cargo records for every crate the manifests in ``directories`` resolve.

    The resolution is filtered to ``platform``.  Raises ``CargoUnreadError``
    naming the directory whose metadata cargo could not read offline.
    """
    cargo = find_executable("cargo")
    recorded: dict[CrateName, Prose | None] = {}
    for directory in directories:
        offline = ["metadata", "--format-version", "1", "--offline", "--filter-platform", platform]
        read = run_capture([cargo, *offline], cwd=directory)
        if read.returncode != 0:
            message = f"{directory}: cargo metadata --offline failed: {read.stderr.strip()}"
            raise CargoUnreadError(message)
        for package in cast("_Metadata", json.loads(read.stdout))["packages"]:
            _ = recorded.setdefault(package["name"], package["license"])
    return recorded


def licence_findings(guide: Prose, recorded: Mapping[CrateName, Prose | None]) -> list[Prose]:
    """Return one finding per Rust row of ``guide`` whose licence ``recorded`` does not hold.

    Raises ``ValueError`` when the guide has no Rust section.
    """
    rows = section_rows(guide, RUST_LAYER)
    if rows is None:
        message = f"{BUILDING_GUIDE}: has no {RUST_LAYER} section"
        raise ValueError(message)
    out: list[Prose] = []
    for row in rows:
        name = CrateName(row.shown[0])
        where = f"{BUILDING_GUIDE}:{row.line}"
        if len(row.shown) <= _LICENCE_CELL or not row.shown[_LICENCE_CELL]:
            out.append(Prose(f"{where}: the row for {name} states no licence"))
        elif name not in recorded:
            out.append(Prose(f"{where}: cargo resolves no crate {name}"))
        elif recorded[name] != row.shown[_LICENCE_CELL]:
            out.append(
                Prose(
                    f"{where}: the ledger says {name} is {row.shown[_LICENCE_CELL]}, "
                    + f"cargo records {recorded[name]!r}"
                )
            )
    return out


def main() -> ExitStatus:
    """Report each Rust row whose licence is not the one cargo records."""
    parser = argparse.ArgumentParser(
        description="Hold the Rust rows of the dependency ledger to the licences cargo records."
    )
    _ = parser.parse_args()
    tracked = git_ls_files(REPO)
    manifests = rust_manifests(tracked)
    if not manifests:
        emit("check-rust-licences: no Cargo.toml is tracked under rust/; licences unchecked")
        return UNCHECKED
    try:
        guide = Prose((REPO / BUILDING_GUIDE).read_text(encoding="utf-8"))
        recorded = cargo_licences([(REPO / rel).parent for rel in manifests], host_platform())
        found = licence_findings(guide, recorded)
    except (OSError, RuntimeError, ValueError, CargoUnreadError) as exc:
        emit(f"check-rust-licences: {exc}; licences unchecked")
        return UNCHECKED
    for finding in found:
        emit(f"check-rust-licences: {finding}")
    if found:
        return DIFFERS
    emit("check-rust-licences: every Rust row names the licence cargo records for its crate")
    return HELD


if __name__ == "__main__":
    sys.exit(main())
