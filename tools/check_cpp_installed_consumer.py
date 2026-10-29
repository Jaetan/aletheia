# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the installed C++ package to what its own headers need.

After ``cmake --install``, a project of its own that finds the package with
``find_package(aletheia-cpp REQUIRED CONFIG)`` links and runs three programs,
one per surface whose symbols sit behind a dependency of the library: the
client, the YAML loader (yaml-cpp) and the Excel loader (OpenXLSX).  The
package is built in a tree of the gate's own by ``tools/private_cpp_tree.sh``,
from the sources ``cpp/build`` fetched, with the command-line tool the install
takes, and installed to a scratch prefix; the consumer under
``tools/installed_consumer_cpp/`` is configured against that prefix with
clang++-23, built, and each program run.  Each refuses a library or a document
that does not exist and exits 0 when the refusal comes back.

It builds only where the branch moves what the package installs or how the
gate builds it, and says so either way; where the diff cannot be read, or is
empty, as on a push to ``main`` or a branch with no commit yet, it builds.  It
is a step of the C++ lane of ``tools/run_ci.py``, after ``ctest``, whose
configure fetched the sources it builds from.

Run ``python -m tools.check_cpp_installed_consumer`` from the repository root.
Exit 0 = every program built and ran, 1 = a step failed, its output printed,
2 = ``cpp/build`` holds no fetched sources to build from.  Unit-tested by
``python/tests/test_check_cpp_installed_consumer.py``.
"""

from __future__ import annotations

import argparse
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple

from tools._branch_diff import branch_changes
from tools._common import CommandWord, RelPath, emit, find_executable, run_capture
from tools._resources import detect_cpus

from aletheia.common_types import ExitStatus, Prose

REPO_ROOT = Path(__file__).resolve().parent.parent
CONSUMER = REPO_ROOT / "tools" / "installed_consumer_cpp"
PROGRAMS = ("client", "yaml_loader", "excel_loader")

# The paths whose change can move the installed package or the gate's build of it.
SCOPE_PATHS = (
    "cpp/CMakeLists.txt",
    "cpp/cmake/",
    "cpp/include/",
    "tools/check_cpp_installed_consumer.py",
    "tools/installed_consumer_cpp/",
    "tools/private_cpp_tree.sh",
    "tools/_ci_steps.py",
)


class Step(NamedTuple):
    """One command of the gate, and what it does."""

    label: Prose
    argv: list[CommandWord]


def in_scope(changes: list[RelPath] | None) -> bool:
    """Whether the branch's changes reach the package; no diff to read, or an empty one, does."""
    return not changes or any(path.startswith(SCOPE_PATHS) for path in changes)


def _words(*parts: Path | CommandWord) -> list[CommandWord]:
    """Return ``parts`` as the words of a command line."""
    return [CommandWord(str(part)) for part in parts]


def steps(work: Path, cmake: CommandWord) -> list[Step]:
    """Return the gate's commands, building, installing and consuming under ``work``."""
    tree, prefix, build = work / "tree", work / "prefix", work / "consumer"
    word = CommandWord
    return [
        Step(
            Prose("build the package"),
            _words(
                REPO_ROOT / "tools" / "private_cpp_tree.sh",
                tree,
                word("aletheia-cpp"),
                word("aletheia-cli"),
            ),
        ),
        Step(
            Prose("install the package"),
            _words(cmake, word("--install"), tree, word("--prefix"), prefix),
        ),
        Step(
            Prose("configure the consumer"),
            _words(
                cmake,
                word("-S"),
                CONSUMER,
                word("-B"),
                build,
                word("-DCMAKE_CXX_COMPILER=clang++-23"),
                word(f"-DCMAKE_PREFIX_PATH={prefix}"),
            ),
        ),
        Step(
            Prose("build the consumer"),
            _words(cmake, word("--build"), build, word("--parallel"), word(str(detect_cpus()))),
        ),
        *(Step(Prose(f"run {program}"), _words(build / program)) for program in PROGRAMS),
    ]


def main() -> ExitStatus:
    """Build, install and consume the package where the branch moves it."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    if not in_scope(branch_changes(REPO_ROOT)):
        emit("check_cpp_installed_consumer: no change on the branch reaches the installed package")
        return ExitStatus(0)
    if not any((REPO_ROOT / "cpp" / "build" / "_deps").glob("*-src")):
        emit("check_cpp_installed_consumer: cpp/build has fetched no dependencies; configure it")
        return ExitStatus(2)
    cmake = CommandWord(find_executable("cmake"))
    with tempfile.TemporaryDirectory(prefix="aletheia-installed-consumer-") as scratch:
        for step in steps(Path(scratch), cmake):
            run = run_capture(step.argv, cwd=REPO_ROOT)
            if run.returncode != 0:
                emit(f"check_cpp_installed_consumer: {step.label} failed ({run.returncode}):")
                emit(run.stdout + run.stderr)
                return ExitStatus(1)
    emit(
        "check_cpp_installed_consumer: the installed package links and runs the client,"
        + " the YAML loader and the Excel loader."
    )
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())
