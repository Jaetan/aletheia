# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Whether the pin a tool fact rests on moved on this branch.

Some gates hold a fact about a tool rather than about the tree: that Agda reuses
an interface whatever its date, what clang-tidy diagnoses under an option, how
the JSON library frees a document.  Such a fact moves only when the tool does,
and the tree says when, since each of these tools is pinned to one release on a
line of its own.  So the gate runs on a branch whose diff moves that line, the
configuration or harness the fact is about, the gate itself or this module, and
costs nothing on any other branch.  It also runs wherever the diff cannot be
read (``tools/_branch_diff.py``), as every gate scoped by the branch does: on an
empty diff, which is a push to ``main`` and the backstop run, on a git error,
and under ``ALETHEIA_PIN_GATES_RUN=1``.

A pin that floats, a floor or a range, cannot scope a gate, since the release it
admits changes on an install no diff shows.  A gate on such a tool runs on every
run instead and has no entry here.
"""

from __future__ import annotations

import os
import re
import sys
from enum import StrEnum
from typing import TYPE_CHECKING, NamedTuple, NewType

from tools._branch_diff import GitDiffOption, branch_changes, branch_diff
from tools._common import RelPath

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping
    from pathlib import Path

    from tools._branch_diff import DiffText

# Set to 1, every pin gate runs whatever the branch moved.
RUN_ALL_ENV = "ALETHEIA_PIN_GATES_RUN"

# A regular expression picking a pin's line out of the lines a file's diff changes.
PinLine = NewType("PinLine", str)


class PinGate(StrEnum):
    """A gate holding a fact about an exactly pinned tool, by the name its log line gives."""

    AGDA_INTERFACE_REUSE = "agda-interface-reuse"
    CLANG_TIDY_FACTS = "clang-tidy-facts"
    JSON_CLEANUP_ABORT = "json-cleanup-abort"


class PinScope(NamedTuple):
    """What a fact rests on: a change under ``path``, or a changed line ``pin_line`` matches."""

    path: RelPath
    pin_line: PinLine | None = None


# The clang toolchain every C++ fact is compiled or read with: one row per
# upstream version, which an install of another upstream version is refused by.
_CLANG_TOOLCHAIN = PinScope(RelPath("cpp/toolchain/check_upstream.sh"))

# What every pin gate rests on: how the branch is read and how a gate is scoped.
_SCOPING = (PinScope(RelPath("tools/_branch_diff.py")), PinScope(RelPath("tools/pin_scope.py")))

PIN_SCOPES: Mapping[PinGate, tuple[PinScope, ...]] = {
    # The Agda release every workflow installs, `cabal install "Agda-${AGDA_VERSION}"`.
    PinGate.AGDA_INTERFACE_REUSE: (
        PinScope(RelPath(".github/workflows/"), PinLine(r"^\s*AGDA_VERSION:")),
        PinScope(RelPath("tools/check_agda_interface_reuse.py")),
    ),
    # The clang-tidy of the toolchain, and the configuration whose comments state the facts.
    PinGate.CLANG_TIDY_FACTS: (
        _CLANG_TOOLCHAIN,
        PinScope(RelPath("cpp/.clang-tidy")),
        PinScope(RelPath("tools/check_clang_tidy_facts.py")),
    ),
    # The JSON library's release, the program showing the fact, and the harness it justifies.
    PinGate.JSON_CLEANUP_ABORT: (
        PinScope(RelPath("cpp/CMakeLists.txt"), PinLine(r"nlohmann/json/")),
        _CLANG_TOOLCHAIN,
        PinScope(RelPath("cpp/tests/json_cleanup_abort.cpp")),
        PinScope(RelPath("cpp/tests/alloc_fault.cpp")),
        PinScope(RelPath("tools/check_json_cleanup_abort.py")),
    ),
}


def changed_lines(diff: DiffText) -> Iterator[Prose]:
    """Yield every line a zero-context diff adds or removes, without its sign.

    A line is read as content only inside a hunk, so a removed line that itself
    starts with ``--`` is not mistaken for a file header.
    """
    in_hunk = False
    for line in diff.splitlines():
        if line.startswith("diff --git "):
            in_hunk = False
        elif line.startswith("@@"):
            in_hunk = True
        elif in_hunk and line[:1] in {"+", "-"}:
            yield Prose(line[1:])


def _scope_moved(scope: PinScope, changed: list[RelPath], repo_root: Path) -> Prose | None:
    """Return what the branch moved of ``scope``, or None where it moved nothing of it."""
    touched = tuple(path for path in changed if path.startswith(scope.path))
    if not touched:
        return None
    if scope.pin_line is None:
        return Prose(f"the branch changes {', '.join(touched)}")
    diff = branch_diff(repo_root, GitDiffOption("-U0"), GitDiffOption("--no-color"), paths=touched)
    if diff is None:
        return Prose(f"git cannot give the lines the branch changed in {', '.join(touched)}")
    moved = [line for line in changed_lines(diff) if re.search(scope.pin_line, line)]
    if not moved:
        return None
    return Prose(f"the branch moves {moved[0].strip()!r} in {', '.join(touched)}")


def pin_change(gate: PinGate, repo_root: Path) -> Prose | None:
    """Return why ``gate`` runs on this branch, or None where nothing it rests on moved."""
    if os.environ.get(RUN_ALL_ENV) == "1":
        return Prose(f"{RUN_ALL_ENV}=1")
    changed = branch_changes(repo_root)
    if changed is None:
        return Prose("git cannot give the branch's diff against main")
    if not changed:
        return Prose("the branch changes nothing against main, which is the backstop run")
    for scope in (*PIN_SCOPES[gate], *_SCOPING):
        moved = _scope_moved(scope, changed, repo_root)
        if moved is not None:
            return moved
    return None


def gate_runs(gate: PinGate, repo_root: Path) -> bool:
    """Say on stderr whether ``gate`` runs on this branch and why, and return whether it does."""
    reason = pin_change(gate, repo_root)
    if reason is None:
        rests_on = ", ".join(scope.path for scope in PIN_SCOPES[gate])
        _ = sys.stderr.write(
            f"[pin] {gate}: the branch moves nothing it rests on ({rests_on}), so it does not run\n"
        )
        return False
    _ = sys.stderr.write(f"[pin] {gate}: runs, since {reason}\n")
    return True
