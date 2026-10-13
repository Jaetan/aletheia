# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The toolchain pins the building guide's prerequisites state are the tree's own.

Four pins are held, each where the guide spells it, its fences included, to
the file that pins it:

* the standard-library tag ``git checkout v<tag>`` checks out, to the
  ``standard-library-<tag>`` that ``aletheia.agda-lib`` depends on;
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
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath
from tools.docs_arms import BUILDING_GUIDE, Unread, missing, read_tracked

from aletheia.common_types import PositiveInt, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

# A version as a pin spells it, digits with dots between.
Version = NewType("Version", str)

AGDA_LIB = RelPath("aletheia.agda-lib")
CMAKE = RelPath("cpp/CMakeLists.txt")
GO_MOD = RelPath("go/go.mod")
PYPROJECT = RelPath("python/pyproject.toml")

_STDLIB_STATED = re.compile(r"git checkout v(\d+(?:\.\d+)*)")
_STDLIB_PINNED = re.compile(r"standard-library-(\d+(?:\.\d+)*)")
_CMAKE_STATED = re.compile(r"cmake version (\d+(?:\.\d+)*)")
_CMAKE_PINNED = re.compile(r"cmake_minimum_required\(VERSION (\d+(?:\.\d+)*)")
_GO_STATED = re.compile(r"go version go(\d+\.\d+)")
_GO_PINNED = re.compile(r"^go (\d+\.\d+)", re.MULTILINE)
_PYTHON = re.compile(r'requires-python = ">=(\d+(?:\.\d+)*)"')


def _numbers(version: Version) -> tuple[PositiveInt, ...]:
    """Return ``version``'s numbers, so versions compare as numbers rather than as text."""
    return tuple(int(part) for part in version.split("."))


def _held(
    name: Prose, stated: set[Version], source: RelPath, pinned: Version | None
) -> list[Prose]:
    """Return the findings of one pin: each stated value differing from ``source``'s ``pinned``."""
    if pinned is None:
        return [Prose(f"{source}: pins no {name} version, so the guide's is unchecked")]
    if not stated:
        return [Prose(f"{BUILDING_GUIDE}: no longer states the {name} pin {source} holds")]
    return [
        Prose(f"{BUILDING_GUIDE}: states the {name} pin {value}, where {source} pins {pinned}")
        for value in sorted(stated - {pinned}, key=_numbers)
    ]


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

    """
    if BUILDING_GUIDE not in documents:
        return [missing(BUILDING_GUIDE, tracked, Prose("the pins it states are unchecked"))]
    guide = documents[BUILDING_GUIDE]
    out: list[Prose] = []
    for name, stated, source, pinned in (
        (Prose("standard-library"), _STDLIB_STATED, AGDA_LIB, _STDLIB_PINNED),
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
        found = pinned.search(text)
        values = {Version(match[1]) for match in stated.finditer(guide)}
        out.extend(_held(name, values, source, Version(found[1]) if found else None))
    return out
