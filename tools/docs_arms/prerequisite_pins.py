# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The toolchain pins the building guide's prerequisites state are the tree's own.

Four pins are held, each where the guide spells it, its fences included, to
the file that pins it:

* the standard-library tag ``git checkout v<tag>`` checks out, to the
  ``STDLIB_VERSION`` the full-CI workflow clones (``aletheia.agda-lib``
  depends on the library's name, which a point release keeps);
* the ``cmake version <floor>`` a check prints, to the ``VERSION`` of
  ``cpp/CMakeLists.txt``'s ``cmake_minimum_required``;
* the ``go version go<floor>`` a check prints, to the major and minor version
  of ``go/go.mod``'s ``go`` directive;
* the ``requires-python = ">=<floor>"`` the guide quotes, to the one
  ``python/pyproject.toml`` states.

Every stated value that differs from its file's is a finding, as is a pin the
guide no longer states, and a file untracked, unread or no longer pinning,
since each leaves the stated pin with nothing to hold.  The Clang version is
left to the claim that the supported Clang is one version everywhere.

The Go binding has one floor, ``go/go.mod``'s: the ``Requires Go <floor>+`` the
distribution guide states is held to its major and minor version the same way,
and the ``go`` directive of every other tracked ``go.mod`` and ``go.work`` to
its whole version, so a module or the workspace declaring another version, or
none, is a finding naming the file.  These come after the four pins, the
distribution guide first, then the files in path order, and are left out when
``go/go.mod`` itself gives no version, which the Go pin already reports.
"""

from __future__ import annotations

import re
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath
from tools.docs_arms import BUILDING_GUIDE, Unread, missing, read_tracked

from aletheia.common_types import PositiveInt, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

# A version as a pin spells it, digits with dots between.
Version = NewType("Version", str)

STDLIB_WORKFLOW = RelPath(".github/workflows/pr-full-ci.yml")
CMAKE = RelPath("cpp/CMakeLists.txt")
GO_MOD = RelPath("go/go.mod")
PYPROJECT = RelPath("python/pyproject.toml")
DISTRIBUTION_GUIDE = RelPath("docs/development/DISTRIBUTION.md")
# The files whose ``go`` directive Go reads: a module's and a workspace's.
GO_DIRECTIVE_FILES = frozenset({"go.mod", "go.work"})

_STDLIB_STATED = re.compile(r"git checkout v(\d+(?:\.\d+)*)")
_STDLIB_PINNED = re.compile(r"STDLIB_VERSION: 'v(\d+(?:\.\d+)*)'")
_CMAKE_STATED = re.compile(r"cmake version (\d+(?:\.\d+)*)")
_CMAKE_PINNED = re.compile(r"cmake_minimum_required\(VERSION (\d+(?:\.\d+)*)")
_GO_STATED = re.compile(r"go version go(\d+\.\d+)")
_GO_PINNED = re.compile(r"^go (\d+\.\d+)", re.MULTILINE)
_GO_REQUIRED = re.compile(r"Requires Go (\d+\.\d+)\+")
# A ``go`` directive's whole version, as the file spells it.
_GO_DIRECTIVE = re.compile(r"^go[ \t]+(\S+)", re.MULTILINE)
_PYTHON = re.compile(r'requires-python = ">=(\d+(?:\.\d+)*)"')


def _numbers(version: Version) -> tuple[PositiveInt, ...]:
    """Return ``version``'s numbers, so versions compare as numbers rather than as text."""
    return tuple(int(part) for part in version.split("."))


def _held(
    name: Prose,
    stated: set[Version],
    source: RelPath,
    pinned: Version | None,
    guide: RelPath = BUILDING_GUIDE,
) -> list[Prose]:
    """Return the findings of one pin: each value ``guide`` states differing from ``pinned``."""
    if pinned is None:
        return [Prose(f"{source}: pins no {name} version, so the guide's is unchecked")]
    if not stated:
        return [Prose(f"{guide}: no longer states the {name} pin {source} holds")]
    return [
        Prose(f"{guide}: states the {name} pin {value}, where {source} pins {pinned}")
        for value in sorted(stated - {pinned}, key=_numbers)
    ]


def _one_go_floor(
    root: Path,
    tracked: Sequence[RelPath],
    documents: Mapping[RelPath, Prose],
    go_mod: Prose,
) -> list[Prose]:
    """Hold the distribution guide's Go floor and every other ``go`` directive to ``go_mod``'s."""
    floor = _GO_PINNED.search(go_mod)
    whole = _GO_DIRECTIVE.search(go_mod)
    if floor is None or whole is None:
        return []
    out: list[Prose] = []
    if DISTRIBUTION_GUIDE in documents:
        distribution = documents[DISTRIBUTION_GUIDE]
        stated = {Version(match[1]) for match in _GO_REQUIRED.finditer(distribution)}
        out.extend(_held(Prose("Go"), stated, GO_MOD, Version(floor[1]), DISTRIBUTION_GUIDE))
    else:
        out.append(missing(DISTRIBUTION_GUIDE, tracked, Prose("the Go pin it states is unchecked")))
    for rel in sorted(tracked):
        if rel == GO_MOD or PurePosixPath(rel).name not in GO_DIRECTIVE_FILES:
            continue
        text = read_tracked(root, rel, Prose("its go directive is unchecked"))
        if isinstance(text, Unread):
            out.append(text.finding)
            continue
        found = _GO_DIRECTIVE.search(text)
        if found is None:
            out.append(Prose(f"{rel}: declares no go version, where {GO_MOD} declares {whole[1]}"))
        elif found[1] != whole[1]:
            out.append(Prose(f"{rel}: declares go {found[1]}, where {GO_MOD} declares {whole[1]}"))
    return out


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per pin the guide states that its file does not hold.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings of the standard library, CMake, Go and Python pins in that
        order, each pin's differing values in version order; for a pin, its
        file untracked or unread instead; alone, the guide untracked or unread.
        Then the findings of the Go binding's one floor: the distribution
        guide's, then each other ``go.mod`` and ``go.work`` in path order.

    """
    if BUILDING_GUIDE not in documents:
        return [missing(BUILDING_GUIDE, tracked, Prose("the pins it states are unchecked"))]
    guide = documents[BUILDING_GUIDE]
    out: list[Prose] = []
    go_mod: Prose | None = None
    for name, stated, source, pinned in (
        (Prose("standard-library"), _STDLIB_STATED, STDLIB_WORKFLOW, _STDLIB_PINNED),
        (Prose("CMake"), _CMAKE_STATED, CMAKE, _CMAKE_PINNED),
        (Prose("Go"), _GO_STATED, GO_MOD, _GO_PINNED),
        (Prose("Python"), _PYTHON, PYPROJECT, _PYTHON),
    ):
        if source not in tracked:
            out.append(
                missing(source, tracked, Prose(f"the {name} pin the guide states is unchecked"))
            )
            continue
        text = read_tracked(root, source, Prose(f"the {name} pin the guide states is unchecked"))
        if isinstance(text, Unread):
            out.append(text.finding)
            continue
        if source == GO_MOD:
            go_mod = text
        found = pinned.search(text)
        values = {Version(match[1]) for match in stated.finditer(guide)}
        out.extend(_held(name, values, source, Version(found[1]) if found else None))
    if go_mod is not None:
        out.extend(_one_go_floor(root, tracked, documents, go_mod))
    return out
