# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The documentation gate's arm over the toolchain pins the building guide states.

A guide stating the standard-library tag, CMake, Go and Python floors its files
pin is clean, whether a pin sits in a fence or in prose, and Go is held at its
major and minor version only.  A stated value its file does not pin is one
finding per value, in version order; a pin the guide no longer states, a file
pinning nothing, and a pin file untracked or unread are each one finding, and
the four pins' findings come standard library, CMake, Go, Python.  The guide
untracked or unread is the arm's only finding.
"""

from __future__ import annotations

from types import MappingProxyType
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.prerequisite_pins import Version, findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Collection, Mapping
    from pathlib import Path

_GUIDE = RelPath("docs/development/BUILDING.md")
_AGDA_LIB = RelPath("aletheia.agda-lib")
_CMAKE = RelPath("cpp/CMakeLists.txt")
_GO_MOD = RelPath("go/go.mod")
_PYPROJECT = RelPath("python/pyproject.toml")

_GUIDE_TEXT = Prose("""# Building

## Prerequisites

Agda's standard library, at the tag the library file depends on:

```sh
git clone https://github.com/agda/agda-stdlib ~/.agda/agda-stdlib
cd ~/.agda/agda-stdlib && git checkout v2.4
```

CMake at its floor or later:

```console
$ cmake --version
cmake version 3.25
```

Go at its floor or later:

```console
$ go version
go version go1.24 linux/amd64
```

Python at the floor the manifest states, `requires-python = ">=3.14"`.
""")

# Read-only, so a test's edit is a copy and no other test sees it.
_FILES: Mapping[RelPath, Prose] = MappingProxyType(
    {
        _GUIDE: _GUIDE_TEXT,
        _AGDA_LIB: Prose("name: aletheia\ninclude: src\ndepend: standard-library-2.4\n"),
        _CMAKE: Prose("cmake_minimum_required(VERSION 3.25)\nproject(aletheia CXX)\n"),
        _GO_MOD: Prose("module github.com/example/aletheia\n\ngo 1.24.0\n"),
        _PYPROJECT: Prose('[project]\nname = "aletheia"\nrequires-python = ">=3.14"\n'),
    }
)

_SOURCES = [
    pytest.param(_AGDA_LIB, Prose("standard-library"), id="stdlib"),
    pytest.param(_CMAKE, Prose("CMake"), id="cmake"),
    pytest.param(_GO_MOD, Prose("Go"), id="go"),
    pytest.param(_PYPROJECT, Prose("Python"), id="python"),
]


def _swapped(
    files: Mapping[RelPath, Prose], rel: RelPath, old: Prose, new: Prose
) -> dict[RelPath, Prose]:
    """Return ``files`` with the one ``old`` in ``rel``'s text replaced by ``new``."""
    text = files[rel]
    assert text.count(old) == 1, f"{old!r} is not spelled once in {rel}"
    return {**files, rel: Prose(text.replace(old, new))}


def _with_guide_tail(tail: Prose) -> dict[RelPath, Prose]:
    """Return the planted files with ``tail`` appended to the guide."""
    return {**_FILES, _GUIDE: Prose(f"{_GUIDE_TEXT}\n{tail}")}


def _without(rel: RelPath) -> dict[RelPath, Prose]:
    """Return the planted files less ``rel``."""
    return {path: text for path, text in _FILES.items() if path != rel}


def _run(
    tmp_path: Path,
    files: Mapping[RelPath, Prose] = _FILES,
    *,
    untracked: Collection[RelPath] = (),
    absent: Collection[RelPath] = (),
) -> list[Prose]:
    """Plant ``files`` in a fresh tree and run the arm over it, the tracked paths as named."""
    root = plant(tmp_path / "repo", files)
    return run_planted(findings, root, untracked=untracked, absent=absent)


def _differs(name: Prose, stated: Version, source: RelPath, pinned: Version) -> Prose:
    """Return the finding for the guide stating ``stated`` where ``source`` pins ``pinned``."""
    return Prose(f"{_GUIDE}: states the {name} pin {stated}, where {source} pins {pinned}")


def test_a_guide_stating_every_pin_its_files_hold_is_clean(tmp_path: Path) -> None:
    """Each pin the guide states, in a fence or in prose, is the one its file pins."""
    assert _run(tmp_path) == list[Prose]()


@pytest.mark.parametrize(
    ("old", "new", "finding"),
    [
        pytest.param(
            Prose("git checkout v2.4"),
            Prose("git checkout v2.3"),
            _differs(Prose("standard-library"), Version("2.3"), _AGDA_LIB, Version("2.4")),
            id="stdlib",
        ),
        pytest.param(
            Prose("cmake version 3.25"),
            Prose("cmake version 3.20"),
            _differs(Prose("CMake"), Version("3.20"), _CMAKE, Version("3.25")),
            id="cmake",
        ),
        pytest.param(
            Prose("go version go1.24"),
            Prose("go version go1.22"),
            _differs(Prose("Go"), Version("1.22"), _GO_MOD, Version("1.24")),
            id="go",
        ),
        pytest.param(
            Prose('requires-python = ">=3.14"'),
            Prose('requires-python = ">=3.12"'),
            _differs(Prose("Python"), Version("3.12"), _PYPROJECT, Version("3.14")),
            id="python",
        ),
    ],
)
def test_a_guide_stating_a_value_its_file_does_not_pin_is_a_finding(
    tmp_path: Path, old: Prose, new: Prose, finding: Prose
) -> None:
    """A stated value differing from the file's is one finding naming both values and the file."""
    assert _run(tmp_path, _swapped(_FILES, _GUIDE, old, new)) == [finding]


@pytest.mark.parametrize(
    ("source", "old", "new", "finding"),
    [
        pytest.param(
            _AGDA_LIB,
            Prose("standard-library-2.4"),
            Prose("standard-library-2.5"),
            _differs(Prose("standard-library"), Version("2.4"), _AGDA_LIB, Version("2.5")),
            id="stdlib",
        ),
        pytest.param(
            _CMAKE,
            Prose("VERSION 3.25"),
            Prose("VERSION 3.28"),
            _differs(Prose("CMake"), Version("3.25"), _CMAKE, Version("3.28")),
            id="cmake",
        ),
        pytest.param(
            _GO_MOD,
            Prose("go 1.24.0"),
            Prose("go 1.25.0"),
            _differs(Prose("Go"), Version("1.24"), _GO_MOD, Version("1.25")),
            id="go",
        ),
        pytest.param(
            _PYPROJECT,
            Prose('">=3.14"'),
            Prose('">=3.15"'),
            _differs(Prose("Python"), Version("3.14"), _PYPROJECT, Version("3.15")),
            id="python",
        ),
    ],
)
def test_a_file_moving_its_pin_leaves_the_guides_value_a_finding(
    tmp_path: Path, source: RelPath, old: Prose, new: Prose, finding: Prose
) -> None:
    """A pin its file moves past the value the guide states is one finding."""
    assert _run(tmp_path, _swapped(_FILES, source, old, new)) == [finding]


def test_a_pin_stated_with_two_values_is_one_finding_for_the_differing_one(
    tmp_path: Path,
) -> None:
    """The guide stating CMake as the file's floor and as another value reports the other only."""
    files = _with_guide_tail(Prose("On the CI image:\n\n```console\ncmake version 3.28\n```\n"))
    assert _run(tmp_path, files) == [
        _differs(Prose("CMake"), Version("3.28"), _CMAKE, Version("3.25"))
    ]


def test_a_differing_value_stated_twice_is_one_finding(tmp_path: Path) -> None:
    """One wrong value the guide spells in two places is reported once."""
    files = _with_guide_tail(Prose("Twice: `cmake version 3.28`, then `cmake version 3.28`.\n"))
    assert _run(tmp_path, files) == [
        _differs(Prose("CMake"), Version("3.28"), _CMAKE, Version("3.25"))
    ]


def test_differing_values_come_in_order_not_in_the_guides(tmp_path: Path) -> None:
    """Two wrong values the guide states higher first are reported lower first."""
    files = _with_guide_tail(Prose("Also `cmake version 3.28` and `cmake version 3.26`.\n"))
    assert _run(tmp_path, files) == [
        _differs(Prose("CMake"), Version("3.26"), _CMAKE, Version("3.25")),
        _differs(Prose("CMake"), Version("3.28"), _CMAKE, Version("3.25")),
    ]


def test_differing_values_come_in_version_order_past_a_one_digit_minor(tmp_path: Path) -> None:
    """Wrong values 3.10 and 3.9 are reported 3.9 first, the order versions take."""
    files = _with_guide_tail(Prose("Also `cmake version 3.10` and `cmake version 3.9`.\n"))
    assert _run(tmp_path, files) == [
        _differs(Prose("CMake"), Version("3.9"), _CMAKE, Version("3.25")),
        _differs(Prose("CMake"), Version("3.10"), _CMAKE, Version("3.25")),
    ]


@pytest.mark.parametrize(
    ("rel", "old", "new"),
    [
        pytest.param(_GO_MOD, Prose("go 1.24.0"), Prose("go 1.24.7"), id="file-patch"),
        pytest.param(_GO_MOD, Prose("go 1.24.0"), Prose("go 1.24"), id="file-no-patch"),
        pytest.param(
            _GUIDE, Prose("go version go1.24 "), Prose("go version go1.24.3 "), id="guide-patch"
        ),
    ],
)
def test_the_go_patch_version_is_not_held(
    tmp_path: Path, rel: RelPath, old: Prose, new: Prose
) -> None:
    """Go is held at its major and minor version, so go 1.24.7 still matches go1.24."""
    assert _run(tmp_path, _swapped(_FILES, rel, old, new)) == list[Prose]()


@pytest.mark.parametrize(
    ("old", "source", "name"),
    [
        pytest.param(Prose("git checkout v2.4"), _AGDA_LIB, Prose("standard-library"), id="stdlib"),
        pytest.param(Prose("cmake version 3.25"), _CMAKE, Prose("CMake"), id="cmake"),
        pytest.param(Prose("go version go1.24"), _GO_MOD, Prose("Go"), id="go"),
        pytest.param(
            Prose('`requires-python = ">=3.14"`'), _PYPROJECT, Prose("Python"), id="python"
        ),
    ],
)
def test_a_pin_the_guide_no_longer_states_is_a_finding(
    tmp_path: Path, old: Prose, source: RelPath, name: Prose
) -> None:
    """A pin its file holds and the guide no longer spells is reported against the guide."""
    assert _run(tmp_path, _swapped(_FILES, _GUIDE, old, Prose(""))) == [
        Prose(f"docs/development/BUILDING.md: no longer states the {name} pin {source} holds")
    ]


@pytest.mark.parametrize(
    ("source", "text", "name"),
    [
        pytest.param(
            _AGDA_LIB,
            Prose("name: aletheia\ninclude: src\n"),
            Prose("standard-library"),
            id="stdlib",
        ),
        pytest.param(_CMAKE, Prose("project(aletheia CXX)\n"), Prose("CMake"), id="cmake"),
        pytest.param(_GO_MOD, Prose("module github.com/example/aletheia\n"), Prose("Go"), id="go"),
        pytest.param(
            _GO_MOD,
            Prose("module github.com/example/aletheia\n\n// go 1.24.0\n"),
            Prose("Go"),
            id="go-directive-not-at-line-start",
        ),
        pytest.param(
            _PYPROJECT, Prose('[project]\nname = "aletheia"\n'), Prose("Python"), id="python"
        ),
    ],
)
def test_a_file_that_pins_nothing_is_a_finding(
    tmp_path: Path, source: RelPath, text: Prose, name: Prose
) -> None:
    """A pin file spelling no pin leaves the guide's value unchecked, which is reported."""
    assert _run(tmp_path, {**_FILES, source: text}) == [
        Prose(f"{source}: pins no {name} version, so the guide's is unchecked")
    ]


def test_a_file_pinning_nothing_outranks_a_pin_the_guide_no_longer_states(
    tmp_path: Path,
) -> None:
    """With neither the file nor the guide spelling the CMake pin, only the file is reported."""
    files = _swapped(
        {**_FILES, _CMAKE: Prose("project(aletheia CXX)\n")},
        _GUIDE,
        Prose("cmake version 3.25"),
        Prose(""),
    )
    assert _run(tmp_path, files) == [
        Prose("cpp/CMakeLists.txt: pins no CMake version, so the guide's is unchecked")
    ]


@pytest.mark.parametrize(("source", "name"), _SOURCES)
def test_an_untracked_pin_file_is_a_finding(tmp_path: Path, source: RelPath, name: Prose) -> None:
    """A pin file git does not track holds nothing in a checkout, so the stated pin is unchecked."""
    assert _run(tmp_path, untracked={source}) == [
        Prose(f"{source}: not tracked, so the {name} pin the guide states is unchecked")
    ]


@pytest.mark.parametrize(("source", "name"), _SOURCES)
def test_a_tracked_pin_file_the_work_tree_lacks_is_a_finding(
    tmp_path: Path, source: RelPath, name: Prose
) -> None:
    """A pin file git tracks and the work tree lacks is unread, so the stated pin is unchecked."""
    assert _run(tmp_path, _without(source), absent={source}) == [
        Prose(f"{source}: could not be read, so the {name} pin the guide states is unchecked")
    ]


def test_an_untracked_guide_is_the_only_finding(tmp_path: Path) -> None:
    """A guide git does not track is reported alone, its pins left unread."""
    files = _swapped(_FILES, _CMAKE, Prose("VERSION 3.25"), Prose("VERSION 3.28"))
    assert _run(tmp_path, files, untracked={_GUIDE}) == [
        Prose("docs/development/BUILDING.md: not tracked, so the pins it states are unchecked")
    ]


def test_a_tracked_guide_the_work_tree_lacks_is_the_only_finding(tmp_path: Path) -> None:
    """A guide git tracks and the work tree lacks is reported by the gate's read and the arm."""
    assert _run(tmp_path, _without(_GUIDE), absent={_GUIDE}) == [
        Prose("docs/development/BUILDING.md: could not be read, so what it says is unchecked"),
        Prose(
            "docs/development/BUILDING.md: could not be read, so the pins it states are unchecked"
        ),
    ]


def test_the_four_pins_findings_come_stdlib_cmake_go_python(tmp_path: Path) -> None:
    """Every pin differing gives its finding in the order standard library, CMake, Go, Python."""
    files = _swapped(_FILES, _PYPROJECT, Prose('">=3.14"'), Prose('">=3.15"'))
    files = _swapped(files, _GO_MOD, Prose("go 1.24.0"), Prose("go 1.25.0"))
    files = _swapped(files, _CMAKE, Prose("VERSION 3.25"), Prose("VERSION 3.28"))
    files = _swapped(files, _AGDA_LIB, Prose("standard-library-2.4"), Prose("standard-library-2.5"))
    assert _run(tmp_path, files) == [
        _differs(Prose("standard-library"), Version("2.4"), _AGDA_LIB, Version("2.5")),
        _differs(Prose("CMake"), Version("3.25"), _CMAKE, Version("3.28")),
        _differs(Prose("Go"), Version("1.24"), _GO_MOD, Version("1.25")),
        _differs(Prose("Python"), Version("3.14"), _PYPROJECT, Version("3.15")),
    ]


def test_each_pins_finding_keeps_its_place_whatever_its_kind(tmp_path: Path) -> None:
    """An unread, unpinned, unstated and differing pin are reported in the pins' order."""
    files = _swapped(_without(_AGDA_LIB), _PYPROJECT, Prose('">=3.14"'), Prose('">=3.15"'))
    files = _swapped(files, _GUIDE, Prose("go version go1.24"), Prose(""))
    files = {**files, _CMAKE: Prose("project(aletheia CXX)\n")}
    unchecked = Prose("the standard-library pin the guide states is unchecked")
    assert _run(tmp_path, files, absent={_AGDA_LIB}) == [
        Prose(f"aletheia.agda-lib: could not be read, so {unchecked}"),
        Prose("cpp/CMakeLists.txt: pins no CMake version, so the guide's is unchecked"),
        Prose("docs/development/BUILDING.md: no longer states the Go pin go/go.mod holds"),
        _differs(Prose("Python"), Version("3.14"), _PYPROJECT, Version("3.15")),
    ]
