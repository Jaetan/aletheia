# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold what the comments of ``cpp/.clang-tidy`` say the toolchain's clang-tidy does.

A comment beside an option says what the option makes the tool do, and the
configuration is written on the strength of it.  That is a fact about the tool
rather than about the tree, so it is shown here by running the toolchain's
clang-tidy, under the tree's own configuration, over a few lines written for
the purpose, and the gate runs when the toolchain's pin or the configuration
moves (``tools/pin_scope.py``).

* ``bugprone-argument-comment.StrictMode`` asks for no argument comment: a call
  carrying none is not diagnosed, and a comment naming another parameter than
  the one it stands before is.

Exits 0 when every fact holds or nothing it rests on moved, 1 naming each that
does not, and 2 when clang-tidy-23 is absent or cannot compile the lines.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path
from typing import NewType

from tools._common import emit, find_executable, git_toplevel, run_capture
from tools.pin_scope import PinGate, gate_runs

from aletheia.common_types import ExitStatus, Prose

# What clang-tidy printed, a check's name, and a line's number in a file, from 1.
ToolOutput = NewType("ToolOutput", str)
CheckName = NewType("CheckName", str)
LineNumber = NewType("LineNumber", int)

CLANG_TIDY = "clang-tidy-23"
_ARGUMENT_COMMENT = CheckName("bugprone-argument-comment")

# A call with no argument comment, then one whose comment names the second
# parameter before the first argument.
_CALLS = """\
void f(int alpha, int beta);
void g() {
    f(1, 2);
    f(/*beta=*/1, 2);
}
"""
_UNCOMMENTED = LineNumber(3)
_MISNAMED = LineNumber(4)


def diagnosed_lines(output: ToolOutput, source: Path, check_name: CheckName) -> set[LineNumber]:
    """Return the lines of ``source`` that ``check_name`` diagnosed in clang-tidy's ``output``."""
    tag = re.escape(check_name)
    found = re.compile(
        rf"^{re.escape(str(source))}:(\d+):\d+: (?:warning|error): .*\[{tag}[,\]]", re.MULTILINE
    )
    return {LineNumber(int(match.group(1))) for match in found.finditer(output)}


def compiler_errors(output: ToolOutput) -> bool:
    """Return whether clang-tidy could not compile what it read."""
    return "[clang-diagnostic-error]" in output


def strict_mode_refusals(diagnosed: set[LineNumber]) -> list[Prose]:
    """Return what the argument-comment diagnoses break of the configuration's comment."""
    refusals: list[Prose] = []
    if _UNCOMMENTED in diagnosed:
        refusals.append(
            Prose(f"{_ARGUMENT_COMMENT}.StrictMode diagnoses a call carrying no argument comment")
        )
    if _MISNAMED not in diagnosed:
        refusals.append(
            Prose(
                f"{_ARGUMENT_COMMENT}.StrictMode passes a comment naming another parameter"
                + " than its own"
            )
        )
    return refusals


def check(repo_root: Path) -> ExitStatus:
    """Run the toolchain's clang-tidy over the facts' lines and check what it diagnosed."""
    try:
        clang_tidy = find_executable(CLANG_TIDY)
    except RuntimeError as missing:
        emit(f"check-clang-tidy-facts: {missing}")
        return ExitStatus(2)
    with tempfile.TemporaryDirectory(prefix="clang-tidy-facts-") as scratch:
        source = Path(scratch) / "calls.cpp"
        _ = source.write_text(_CALLS, encoding="utf-8")
        ran = run_capture(
            [
                clang_tidy,
                "--quiet",
                f"--config-file={repo_root / 'cpp' / '.clang-tidy'}",
                f"-checks=-*,{_ARGUMENT_COMMENT}",
                str(source),
                "--",
                "-std=c++23",
            ]
        )
        output = ToolOutput(ran.stdout + ran.stderr)
        if compiler_errors(output):
            emit(f"check-clang-tidy-facts: {CLANG_TIDY} could not compile the lines:\n{output}")
            return ExitStatus(2)
        refusals = strict_mode_refusals(diagnosed_lines(output, source, _ARGUMENT_COMMENT))
    for refusal in refusals:
        emit(f"check-clang-tidy-facts: {refusal}")
    return ExitStatus(1 if refusals else 0)


def main() -> ExitStatus:
    """Check the clang-tidy facts when the branch moves what they rest on."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.CLANG_TIDY_FACTS, repo_root):
        return ExitStatus(0)
    return check(repo_root)


if __name__ == "__main__":
    sys.exit(main())
