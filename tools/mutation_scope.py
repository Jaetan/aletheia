# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Whether a mutation lane sweeps, asked before the lane installs a toolchain.

``tools/mutation_run.py`` scopes a pull request to the bindings whose mutation
result its diff vs ``main`` could move, and skips the rest unswept.  A CI lane
reaches that decision only after installing GHC, cabal, Agda, the standard
library, a Python venv, Go, gremlins, clang, the LLVM development libraries,
Mull and the FFI library, so it pays for a sweep it then does not run.

This module is the same decision, asked ahead of those installs.  It answers for
one binding, and it takes the answer from ``bindings_in_scope`` rather than
reading the diff again: two readings of one diff are two decisions, and the one
that disagrees would hold back an install the sweep beside it then needs.

Run as ``python -m tools.mutation_scope --binding cpp``.  The answer is written
as ``LANE_SWEEPS=1`` or ``LANE_SWEEPS=0`` to the file ``GITHUB_ENV`` names, and
to stdout where the environment names none, so a workflow step reads it as a
condition and a reader at a terminal reads it as a line.  The decision itself
goes to stderr in the runner's own wording, so a lane's log states what it
installed and why.  A binding no runner has is refused, since a lane naming one
would otherwise skip its own toolchain and fail at its sweep.
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

from tools.mutation_run import REPO_ROOT, RUNNERS, bindings_in_scope

# The variable a lane's steps read.  Their condition is `!= '0'`, never
# `== '1'`: an answer that did not arrive must install, because installing what
# a lane does not need costs minutes and skipping what it needs costs the run.
SWEEPS_VAR = "LANE_SWEEPS"


def lane_sweeps(binding: str, repo_root: Path) -> bool:
    """Report whether a lane sweeping ``binding`` is in the diff scope of this branch.

    ``bindings_in_scope`` returns ``None`` for the cases that run everything (an
    empty diff, a global path, a git error, the escape hatch), which is the
    fail-safe answer here too: the lane installs.
    """
    in_scope = bindings_in_scope(repo_root)
    return in_scope is None or binding in in_scope


def _bindings() -> list[str]:
    """Return the binding names the runner has, which are the lanes it can be asked about."""
    return [name for name, _skip_var, _runner in RUNNERS]


def main(argv: list[str] | None = None) -> int:
    """Write this lane's sweep decision where its workflow steps read it."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--binding",
        required=True,
        choices=_bindings(),
        help="the binding this lane sweeps, whatever tree or slice of it the lane carries",
    )
    args = parser.parse_args(argv)
    binding = str(args.binding)

    sweeps = lane_sweeps(binding, REPO_ROOT)
    _ = sys.stderr.write(
        f"[mutation] scope: {binding} is in the diff scope, so this lane installs its toolchain\n"
        if sweeps
        else f"[mutation] scope: no change under {binding}, so this lane installs nothing\n"
    )
    line = f"{SWEEPS_VAR}={'1' if sweeps else '0'}"
    github_env = os.environ.get("GITHUB_ENV")
    if github_env:
        with Path(github_env).open("a", encoding="utf-8") as handle:
            _ = handle.write(f"{line}\n")
    else:
        _ = sys.stdout.write(f"{line}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
