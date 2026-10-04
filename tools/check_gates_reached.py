# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_gates_reached.py — every Shake check target is run by something.

A ``phony "check-*"`` target in ``Shakefile.hs`` is a gate only while
something runs it: the combined Agda-gates step of ``tools/run_ci.py``
(``AGDA_SHAKE_TARGETS``), another Shake rule that ``need``s it, or a run on
demand this file names with its reason (``ON_DEMAND``).  A target none of the
three reaches is red or green with nobody looking, and fails this check; so
does an ``ON_DEMAND`` or ``AGDA_SHAKE_TARGETS`` entry naming a target the
Shakefile no longer has.

Exit codes:
  0 — every check target is reached and every listed name exists.
  1 — a target is reached by nothing, or a list names a target that is gone.
  2 — the Shakefile could not be read or declares no check target.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import NewType

from tools._ci_steps import AGDA_SHAKE_TARGETS
from tools._common import GateName, emit

from aletheia.common_types import ExitStatus, Prose

REPO_ROOT = Path(__file__).resolve().parent.parent
SHAKEFILE = REPO_ROOT / "Shakefile.hs"

ShakeSource = NewType("ShakeSource", str)

REACHED, UNREACHED, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)

# Targets run by hand or by a probe, each with the reason nothing in CI needs it.
ON_DEMAND: dict[GateName, Prose] = {
    GateName("check-ffi-names"): Prose(
        "the build rule for Main.hs runs the same check inline on the shim's wrapper; the "
        + "target exists so a probe can hand the extractor a wrapper in another shape"
    ),
}

_PHONY = re.compile(r'\bphony\s+"(check-[a-z0-9-]+)"')
_NEED = re.compile(r"\bneed\s*\[([^\]]*)\]")
_STRING = re.compile(r'"([^"]+)"')


def check_targets(shakefile: ShakeSource) -> set[GateName]:
    """Return the ``check-*`` targets the Shakefile declares."""
    return {GateName(name) for name in _PHONY.findall(shakefile)}


def needed(shakefile: ShakeSource) -> set[GateName]:
    """Every name a Shake rule ``need``s."""
    return {GateName(name) for block in _NEED.findall(shakefile) for name in _STRING.findall(block)}


def unreached(
    shakefile: ShakeSource, ci: tuple[GateName, ...], on_demand: dict[GateName, Prose]
) -> tuple[set[GateName], set[GateName]]:
    """Targets nothing runs, and listed names the Shakefile does not declare."""
    targets = check_targets(shakefile)
    reached = set(ci) | needed(shakefile) | set(on_demand)
    listed = {name for name in set(ci) | set(on_demand) if name.startswith("check-")}
    return targets - reached, listed - targets


def run(
    shakefile_path: Path, ci: tuple[GateName, ...], on_demand: dict[GateName, Prose]
) -> ExitStatus:
    """Run the check over one Shakefile and return its exit status."""
    try:
        shakefile = ShakeSource(shakefile_path.read_text(encoding="utf-8"))
    except OSError as exc:
        sys.stderr.write(f"check-gates-reached: cannot read {shakefile_path}: {exc}\n")
        return UNREADABLE
    if not check_targets(shakefile):
        sys.stderr.write(f'check-gates-reached: no `phony "check-*"` target in {shakefile_path}\n')
        return UNREADABLE
    orphans, gone = unreached(shakefile, ci, on_demand)
    for name in sorted(orphans):
        sys.stderr.write(
            f"check-gates-reached: {name} is run by no CI step, "
            + "no rule's need and no ON_DEMAND entry\n"
        )
    for name in sorted(gone):
        sys.stderr.write(
            f"check-gates-reached: {name} is listed but the Shakefile declares no such target\n"
        )
    if orphans or gone:
        return UNREACHED
    emit(
        f"check-gates-reached: all {len(check_targets(shakefile))} check targets "
        + "are run by something"
    )
    return REACHED


def main() -> ExitStatus:
    """Fail when a Shake check target is run by nothing."""
    argparse.ArgumentParser(description=__doc__).parse_args()
    return run(SHAKEFILE, tuple(GateName(t) for t in AGDA_SHAKE_TARGETS), ON_DEMAND)


if __name__ == "__main__":
    sys.exit(main())
