# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Go standard names exactly the fuzz targets the binding defines, and nothing schedules a run.

AGENTS/go.md cites its fuzz targets as backticked ``Fuzz...`` names; the binding
defines them as ``func Fuzz...`` in go/aletheia/fuzz_test.go. Each name on one side
and not the other is a finding against the file that is wrong about it, in name order.
The standard says fuzzing is a command someone types, so a tracked workflow or tool
that passes a fuzz duration or selects a fuzz target contradicts it and is named; a
byte that is not UTF-8 does not stop a file's read, and a file the work tree cannot
give is named as unread. A standard that names no target, a target file that defines
none, or a tree that does not track or cannot give either file, has matched nothing,
which is a finding rather than a pass.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._common import RelPath
from tools.docs_arms import Unread, missing, read_tracked

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

STANDARD = RelPath("AGENTS/go.md")
TARGETS = RelPath("go/aletheia/fuzz_test.go")
# The trees a fuzz run would be scheduled from: every tracked file under each is read.
SCHEDULING_TREES = (".github/workflows/", "tools/")

_NAMED = re.compile(r"`(Fuzz[A-Za-z]+)`")
_DEFINED = re.compile(r"^func (Fuzz[A-Za-z]+)", re.MULTILINE)
# A fuzz duration, or the target flag not run into a longer word, whether its value follows
# after "=", after a space or as the next list element; each is assembled so this module
# does not match itself when it is read as one of the tools.
_INVOKES_FUZZ = re.compile(
    re.escape("fuzz" + "time") + "|" + re.escape("-" + "fuzz") + "(?![A-Za-z0-9_-])"
)
_STANDARD_UNCHECKED = Prose("its fuzz targets are unchecked")
_TARGETS_UNCHECKED = Prose(f"the targets {STANDARD} names are unchecked")
_SCHEDULE_UNCHECKED = Prose("whether it invokes a fuzz run is unchecked")
_INVOKES = Prose(f"invokes a fuzz run, while {STANDARD} says fuzzing is a command one types")


def _target_findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Compare the names the standard cites with the targets the binding defines."""
    out: list[Prose] = []
    if STANDARD not in documents:
        out.append(missing(STANDARD, tracked, _STANDARD_UNCHECKED))
    if TARGETS not in tracked:
        out.append(missing(TARGETS, tracked, _TARGETS_UNCHECKED))
    if out:
        return out
    source = read_tracked(root, TARGETS, _TARGETS_UNCHECKED)
    if isinstance(source, Unread):
        return [source.finding]
    named = set(_NAMED.findall(documents[STANDARD]))
    defined = set(_DEFINED.findall(source))
    if not named:
        out.append(Prose(f"{STANDARD}: names no backticked Fuzz target, so nothing was compared"))
    if not defined:
        out.append(Prose(f"{TARGETS}: defines no Fuzz target, so nothing was compared"))
    out.extend(
        Prose(f"{STANDARD}: names fuzz target `{name}`, which {TARGETS} does not define")
        for name in sorted(named - defined)
    )
    out.extend(
        Prose(f"{TARGETS}: defines fuzz target `{name}`, which {STANDARD} does not name")
        for name in sorted(defined - named)
    )
    return out


def _schedule_findings(root: Path, tracked: Sequence[RelPath]) -> list[Prose]:
    """Name every tracked workflow or tool that invokes a fuzz run, or that cannot be read."""
    out: list[Prose] = []
    for rel in tracked:
        if not rel.startswith(SCHEDULING_TREES):
            continue
        text = read_tracked(root, rel, _SCHEDULE_UNCHECKED)
        if isinstance(text, Unread):
            out.append(text.finding)
        elif _INVOKES_FUZZ.search(text):
            out.append(Prose(f"{rel}: {_INVOKES}"))
    return out


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return the arm's findings over the tree at ``root``.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        One line per defect, each opening with the repo-relative path of the file concerned.

    """
    return _target_findings(root, tracked, documents) + _schedule_findings(root, tracked)
