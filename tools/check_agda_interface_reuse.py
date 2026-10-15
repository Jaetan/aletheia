# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold that Agda reuses an interface whatever its date, judging it by hashes alone.

The build-tree cache every workflow restores, ``_build/`` among its paths, comes
back with each file's modification time reset.  A checker that judged an
interface by its date against its source's would re-check every module on every
run; Agda judges one by the hash of its source and the hashes of the interfaces
it imports, which is what that cache rests on.  This is a fact about Agda rather
than the tree, so the gate runs when the Agda release the workflows install
moves (``tools/pin_scope.py``).

It is shown in a copy of the project's sources, so the tree's interfaces are
neither redated nor removed; the copy's first check writes its own.  With every
interface then dated 2020 and every source dated now, checking a module
re-checks nothing; with the interface of a module it imports deleted, it
re-checks exactly that one and writes it back.  The checker prints one
``Checking`` line per module it checks and none for an interface it loads.  The
module and the one it imports import nothing else of the project, so the gate's
checking costs seconds.

Exits 0 when the fact holds or nothing it rests on moved, 1 naming what Agda
re-checked against it, and 2 when agda is absent, a run of it fails, or the
first check writes no interface for the imported module, so a crash never reads
as a pass.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import sys
import tempfile
from datetime import UTC, datetime
from pathlib import Path
from typing import NewType

from tools._common import RelPath, emit, find_executable, git_ls_files, git_toplevel, run_capture
from tools.pin_scope import PinGate, gate_runs

from aletheia.common_types import ExitStatus, Prose

# What one run of the checker printed, how many modules it checked, and the
# release it reports, which names its interface directory.
CheckerLog = NewType("CheckerLog", str)
ModuleCount = NewType("ModuleCount", int)
AgdaVersion = NewType("AgdaVersion", str)

# The module checked, and a module it imports directly, whose interface is deleted.
MODULE = RelPath("src/Aletheia/Data/Dec0/Nat.agda")
IMPORTED = RelPath("src/Aletheia/Data/Dec0.agda")

# The date every copied interface is given, before any source in a fresh copy.
_REDATED = datetime(2020, 1, 1, tzinfo=UTC).timestamp()

# The checker's line for a module it checks rather than loads.
_CHECKING = re.compile(r"^\s*Checking ", re.MULTILINE)


def rechecked(log: CheckerLog) -> ModuleCount:
    """Return how many modules one run of the checker checked rather than loaded."""
    return ModuleCount(len(_CHECKING.findall(log)))


def reuse_refusals(
    after_redating: ModuleCount, after_deleting: ModuleCount, *, written_back: bool
) -> list[Prose]:
    """Return what the two runs break of the fact."""
    refusals: list[Prose] = []
    if after_redating != 0:
        refusals.append(
            Prose(f"every interface older than its source, {after_redating} modules re-checked")
        )
    if after_deleting != 1:
        refusals.append(
            Prose(f"one imported interface deleted, {after_deleting} modules re-checked, not 1")
        )
    if not written_back:
        refusals.append(Prose(f"the check wrote no interface back for {IMPORTED}"))
    return refusals


def interface_of(source: RelPath, version: AgdaVersion) -> RelPath:
    """Return where Agda keeps the interface of a source of the project."""
    return RelPath(f"_build/{version}/agda/{source.removesuffix('.agda')}.agdai")


def _check(agda: Path, project: Path) -> CheckerLog | None:
    """Check ``MODULE`` in ``project``, returning what the checker printed, or None if it failed."""
    ran = run_capture([str(agda), "+RTS", "-M16G", "-RTS", MODULE], cwd=project)
    if ran.returncode != 0:
        emit(f"check-agda-interface-reuse: agda exited {ran.returncode}:\n{ran.stdout[-2000:]}")
        return None
    return CheckerLog(ran.stdout)


def _copy_project(repo_root: Path, project: Path) -> None:
    """Copy the tracked sources and the library file into ``project``.

    The sources are copied without their dates, so every one is dated now.
    """
    for relative in git_ls_files(repo_root, "src", "aletheia.agda-lib"):
        target = project / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        _ = shutil.copyfile(repo_root / relative, target)


def check(repo_root: Path) -> ExitStatus:
    """Show the fact in a copy of the project's sources."""
    try:
        agda = Path(find_executable("agda"))
    except RuntimeError as missing:
        emit(f"check-agda-interface-reuse: {missing}")
        return ExitStatus(2)
    version = AgdaVersion(run_capture([str(agda), "--numeric-version"], check=True).stdout.strip())
    with tempfile.TemporaryDirectory(prefix="agda-interface-reuse-") as scratch:
        project = Path(scratch)
        _copy_project(repo_root, project)
        if _check(agda, project) is None:
            return ExitStatus(2)
        imported = project / interface_of(IMPORTED, version)
        if not imported.is_file():
            emit(f"check-agda-interface-reuse: checking {MODULE} wrote no {imported.name}")
            return ExitStatus(2)
        for interface in (project / "_build").rglob("*.agdai"):
            os.utime(interface, (_REDATED, _REDATED))
        redated = _check(agda, project)
        if redated is None:
            return ExitStatus(2)
        imported.unlink()
        deleted = _check(agda, project)
        if deleted is None:
            return ExitStatus(2)
        refusals = reuse_refusals(
            rechecked(redated), rechecked(deleted), written_back=imported.is_file()
        )
    for refusal in refusals:
        emit(f"check-agda-interface-reuse: {refusal}")
    return ExitStatus(1 if refusals else 0)


def main() -> ExitStatus:
    """Check Agda's interface reuse when the branch moves the Agda release."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.AGDA_INTERFACE_REUSE, repo_root):
        return ExitStatus(0)
    return check(repo_root)


if __name__ == "__main__":
    sys.exit(main())
