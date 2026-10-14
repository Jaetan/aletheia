# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold that the JSON library ends the program on an allocation failing as it frees a document.

The allocation-fault sweeps of the C++ tests (``cpp/tests/alloc_fault.cpp``)
never fail an allocation the JSON library makes for itself.  They must not:
the library destroys a document by flattening it onto a vector it allocates,
from a destructor, which is noexcept, so a failure there ends the program
instead of unwinding to anything a test could reach.  That is a fact about the
library's release rather than the tree, so the gate runs when the release
``cpp/CMakeLists.txt`` fetches moves, or the toolchain, the program showing the
fact or the harness it justifies (``tools/pin_scope.py``).

The program is ``cpp/tests/json_cleanup_abort.cpp``, a target of the test tree
the default build leaves out; the gate builds it in ``cpp/build``, which the C++
lane has configured, and runs it.  It exits 0 only from its terminate handler,
once a failed allocation in a document's destruction has ended it, having first
run a parse to the end with the library's own allocations spared as the sweeps
spare them.

Exits 0 when the fact holds or nothing it rests on moved, 1 when the program
shows it no longer holds, and 2 when the tree is not configured, the target does
not build, or the program ends any other way.
"""

from __future__ import annotations

import argparse
import sys
from typing import TYPE_CHECKING

from tools._common import emit, find_executable, git_toplevel, run_capture
from tools._resources import cpu_budget
from tools.pin_scope import PinGate, gate_runs

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from pathlib import Path

TARGET = "json_cleanup_abort"


def check(repo_root: Path) -> ExitStatus:
    """Build the program in the C++ test tree and run it."""
    tree = repo_root / "cpp" / "build"
    if not (tree / "CMakeCache.txt").is_file():
        emit(f"check-json-cleanup-abort: {tree} is not configured; the C++ lane configures it")
        return ExitStatus(2)
    cmake = find_executable("cmake")
    built = run_capture([cmake, "--build", str(tree), "--target", TARGET, "-j", str(cpu_budget())])
    if built.returncode != 0:
        emit(f"check-json-cleanup-abort: {TARGET} does not build:\n{built.stdout}{built.stderr}")
        return ExitStatus(2)
    ran = run_capture([str(tree / TARGET)])
    said = ran.stdout + ran.stderr
    if ran.returncode == 0:
        return ExitStatus(0)
    emit(f"check-json-cleanup-abort: {TARGET} exited {ran.returncode}: {said.strip()}")
    return ExitStatus(1 if ran.returncode == 1 else 2)


def main() -> ExitStatus:
    """Show the JSON library's cleanup fact when the branch moves what it rests on."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.JSON_CLEANUP_ABORT, repo_root):
        return ExitStatus(0)
    return check(repo_root)


if __name__ == "__main__":
    sys.exit(main())
