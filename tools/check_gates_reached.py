# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_gates_reached.py — every Shake check target is run by something.

A ``phony "check-*"`` target of the build program (``Shakefile.hs`` and the
modules under ``shake/``) is a gate only while something runs it: the combined
Agda-gates step of ``tools/run_ci.py`` (``AGDA_SHAKE_TARGETS``), another Shake
rule that ``need``s it, or a run on demand this file names with its reason
(``ON_DEMAND``).  A target none of the three reaches is red or green with
nobody looking, and fails this check; so does an ``ON_DEMAND`` or
``AGDA_SHAKE_TARGETS`` entry naming a target no rule declares any more.

Exit codes:
  0 — every check target is reached and every listed name exists.
  1 — a target is reached by nothing, or a list names a target that is gone.
  2 — the build program could not be read or declares no check target.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from tools._ci_steps import AGDA_SHAKE_TARGETS
from tools._common import GateName, ShakeSource, emit, read_shake_program

from aletheia.common_types import ExitStatus, Prose

REPO_ROOT = Path(__file__).resolve().parent.parent

REACHED, UNREACHED, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)

# Targets run by hand or by a probe, each with the reason nothing in CI needs it.
ON_DEMAND: dict[GateName, Prose] = {
    GateName("check-ffi-names"): Prose(
        "the build rule for Main.hs runs the same check inline on the shim's wrapper; the "
        + "target exists so a probe can hand the extractor a wrapper in another shape"
    ),
}

# A declaration opens its line; a comment that spells one declares nothing.
_PHONY = re.compile(r'^\s*phony\s+"(check-[a-z0-9-]+)"', re.MULTILINE)
_NEED = re.compile(r"\bneed\s*\[([^\]]*)\]")
_STRING = re.compile(r'"([^"]+)"')


def check_targets(program: ShakeSource) -> set[GateName]:
    """Return the ``check-*`` targets the build program declares."""
    return {GateName(name) for name in _PHONY.findall(program)}


def needed(program: ShakeSource) -> set[GateName]:
    """Every name a Shake rule ``need``s."""
    return {GateName(name) for block in _NEED.findall(program) for name in _STRING.findall(block)}


def unreached(
    program: ShakeSource, ci: tuple[GateName, ...], on_demand: dict[GateName, Prose]
) -> tuple[set[GateName], set[GateName]]:
    """Targets nothing runs, and listed names no rule of the build program declares."""
    targets = check_targets(program)
    reached = set(ci) | needed(program) | set(on_demand)
    listed = {name for name in set(ci) | set(on_demand) if name.startswith("check-")}
    return targets - reached, listed - targets


def run(root: Path, ci: tuple[GateName, ...], on_demand: dict[GateName, Prose]) -> ExitStatus:
    """Run the check over the build program under ``root`` and return its exit status."""
    try:
        program = read_shake_program(root)
    except OSError as exc:
        sys.stderr.write(f"check-gates-reached: cannot read the build program: {exc}\n")
        return UNREADABLE
    if not check_targets(program):
        sys.stderr.write(f'check-gates-reached: no `phony "check-*"` target under {root}\n')
        return UNREADABLE
    orphans, gone = unreached(program, ci, on_demand)
    for name in sorted(orphans):
        sys.stderr.write(
            f"check-gates-reached: {name} is run by no CI step, "
            + "no rule's need and no ON_DEMAND entry\n"
        )
    for name in sorted(gone):
        sys.stderr.write(
            f"check-gates-reached: {name} is listed but no rule declares such a target\n"
        )
    if orphans or gone:
        return UNREACHED
    emit(
        f"check-gates-reached: all {len(check_targets(program))} check targets "
        + "are run by something"
    )
    return REACHED


def main() -> ExitStatus:
    """Fail when a Shake check target is run by nothing."""
    argparse.ArgumentParser(description=__doc__).parse_args()
    return run(REPO_ROOT, tuple(GateName(t) for t in AGDA_SHAKE_TARGETS), ON_DEMAND)


if __name__ == "__main__":
    sys.exit(main())
