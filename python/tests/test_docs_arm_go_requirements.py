# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The documentation gate's arm holding the command line's requirements to the Excel module's.

A command line requiring each module the Excel module requires, at that version
or later, indirect requirements included, is clean.  A module it requires below
that version, or not at all, is one finding, in the Excel module's order.
Versions order by Semantic Versioning precedence: a pre-release below its
release, numeric identifiers by value and below words, a pseudo-version by its
time, build metadata aside.  A version either file spells that is no Go module
version is a finding instead, and a file untracked, unread or carrying a require
its reader refuses is a finding instead again.
"""

from __future__ import annotations

import itertools
from types import MappingProxyType
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools._manifests import GoModule, GoVersion
from tools.docs_arms.go_requirements import findings, precedence

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Collection, Mapping
    from pathlib import Path

_EXCEL = RelPath("go/excel/go.mod")
_CLI = RelPath("go/cmd/aletheia/go.mod")

_REQUIRES = Prose("""require (
\tgithub.com/example/aletheia/go/v5 v5.0.0-20261120132838-2150dabcfa97
\tgithub.com/example/excelize/v2 v2.11.1
)

require golang.org/x/text v0.43.0 // indirect
""")

# Read-only, so a test's edit is a copy and no other test sees it.
_FILES: Mapping[RelPath, Prose] = MappingProxyType(
    {
        _EXCEL: Prose(f"module github.com/example/aletheia/go/excel\n\ngo 1.26.0\n\n{_REQUIRES}"),
        _CLI: Prose(
            f"module github.com/example/aletheia/go/cmd/aletheia\n\ngo 1.26.0\n\n{_REQUIRES}"
        ),
    }
)


def _swapped(
    rel: RelPath, old: Prose, new: Prose, files: Mapping[RelPath, Prose] = _FILES
) -> dict[RelPath, Prose]:
    """Return ``files`` with the one ``old`` in ``rel``'s text replaced by ``new``."""
    text = files[rel]
    assert text.count(old) == 1, f"{old!r} is not spelled once in {rel}"
    return {**files, rel: Prose(text.replace(old, new))}


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


def _below(module: GoModule, held: GoVersion, wanted: GoVersion) -> Prose:
    """Return the finding for the command line requiring ``module`` at ``held`` below ``wanted``."""
    return Prose(f"{_CLI}: requires {module} at {held}, below the {wanted} {_EXCEL} requires")


_EXCELIZE = GoModule("github.com/example/excelize/v2")
_TEXT = GoModule("golang.org/x/text")
_CORE = GoModule("github.com/example/aletheia/go/v5")


def test_a_command_line_requiring_what_the_excel_module_does_is_clean(tmp_path: Path) -> None:
    """The same requires, direct and indirect, leave nothing to report."""
    assert _run(tmp_path) == list[Prose]()


@pytest.mark.parametrize(
    ("old", "new"),
    [
        pytest.param(
            Prose("excelize/v2 v2.11.1"), Prose("excelize/v2 v2.12.0"), id="later-release"
        ),
        pytest.param(
            Prose("2150dabcfa97"),
            Prose("2150dabcfa97\n\tgithub.com/example/extra v1.0.0"),
            id="more-modules",
        ),
        pytest.param(
            Prose("v5.0.0-20261120132838-2150dabcfa97"),
            Prose("v5.0.0-20261122142104-8f6cc9b376fa"),
            id="later-pseudo-version",
        ),
    ],
)
def test_a_command_line_requiring_later_or_more_is_clean(
    tmp_path: Path, old: Prose, new: Prose
) -> None:
    """A later version, or a module the Excel module does not require, is no finding."""
    assert _run(tmp_path, _swapped(_CLI, old, new)) == list[Prose]()


@pytest.mark.parametrize(
    ("old", "new", "finding"),
    [
        pytest.param(
            Prose("excelize/v2 v2.11.1"),
            Prose("excelize/v2 v2.10.1"),
            _below(_EXCELIZE, GoVersion("v2.10.1"), GoVersion("v2.11.1")),
            id="earlier-release",
        ),
        pytest.param(
            Prose("text v0.43.0"),
            Prose("text v0.34.0"),
            _below(_TEXT, GoVersion("v0.34.0"), GoVersion("v0.43.0")),
            id="indirect",
        ),
        pytest.param(
            Prose("v5.0.0-20261120132838-2150dabcfa97"),
            Prose("v5.0.0-20261120132700-0000000000aa"),
            _below(
                _CORE,
                GoVersion("v5.0.0-20261120132700-0000000000aa"),
                GoVersion("v5.0.0-20261120132838-2150dabcfa97"),
            ),
            id="earlier-pseudo-version",
        ),
        pytest.param(
            Prose("excelize/v2 v2.11.1"),
            Prose("excelize/v2 v2.11.1-rc.1"),
            _below(_EXCELIZE, GoVersion("v2.11.1-rc.1"), GoVersion("v2.11.1")),
            id="pre-release-of-it",
        ),
        pytest.param(
            Prose("excelize/v2 v2.11.1"),
            Prose("excelize/v2 v2.9.10"),
            _below(_EXCELIZE, GoVersion("v2.9.10"), GoVersion("v2.11.1")),
            id="two-digit-minor-by-value",
        ),
    ],
)
def test_a_command_line_requiring_an_earlier_version_is_a_finding(
    tmp_path: Path, old: Prose, new: Prose, finding: Prose
) -> None:
    """A module required below the Excel module's version is one finding naming both."""
    assert _run(tmp_path, _swapped(_CLI, old, new)) == [finding]


def test_a_module_the_command_line_does_not_require_is_a_finding(tmp_path: Path) -> None:
    """A module the Excel module requires and the command line does not is one finding."""
    files = _swapped(_CLI, Prose("require golang.org/x/text v0.43.0 // indirect\n"), Prose(""))
    assert _run(tmp_path, files) == [
        Prose(f"{_CLI}: requires no golang.org/x/text, which {_EXCEL} requires at v0.43.0")
    ]


def test_findings_come_in_the_excel_modules_order(tmp_path: Path) -> None:
    """Two modules behind are reported in the order the Excel module requires them."""
    files = _swapped(_CLI, Prose("text v0.43.0"), Prose("text v0.34.0"))
    files = _swapped(_CLI, Prose("excelize/v2 v2.11.1"), Prose("excelize/v2 v2.10.1"), files)
    assert _run(tmp_path, files) == [
        _below(_EXCELIZE, GoVersion("v2.10.1"), GoVersion("v2.11.1")),
        _below(_TEXT, GoVersion("v0.34.0"), GoVersion("v0.43.0")),
    ]


@pytest.mark.parametrize(
    "ordered",
    [
        pytest.param(
            [
                GoVersion("v1.0.0-alpha"),
                GoVersion("v1.0.0-alpha.1"),
                GoVersion("v1.0.0-alpha.beta"),
                GoVersion("v1.0.0-beta"),
                GoVersion("v1.0.0-beta.2"),
                GoVersion("v1.0.0-beta.11"),
                GoVersion("v1.0.0-rc.1"),
                GoVersion("v1.0.0"),
            ],
            id="the-specifications-example",
        ),
        pytest.param(
            [GoVersion("v1.9.0"), GoVersion("v1.10.0"), GoVersion("v2.0.0")],
            id="release-numbers-by-value",
        ),
        pytest.param(
            [
                GoVersion("v1.0.0-1"),
                GoVersion("v1.0.0-2"),
                GoVersion("v1.0.0-10"),
                GoVersion("v1.0.0-a"),
            ],
            id="numbers-below-words",
        ),
        pytest.param(
            [
                GoVersion("v0.0.0-20261120132838-2150dabcfa97"),
                GoVersion("v0.0.0-20261122142104-8f6cc9b376fa"),
                GoVersion("v0.0.1"),
            ],
            id="pseudo-versions-by-time-below-the-release",
        ),
    ],
)
def test_precedence_orders_versions_as_semantic_versioning_does(ordered: list[GoVersion]) -> None:
    """Each list is in ascending precedence, every neighbour strictly below the next."""
    places = [place for version in ordered if (place := precedence(version)) is not None]
    assert len(places) == len(ordered)
    assert all(a < b for a, b in itertools.pairwise(places))


def test_build_metadata_takes_no_part_in_precedence() -> None:
    """``+incompatible`` leaves a version's place where its release is."""
    assert precedence(GoVersion("v2.0.0+incompatible")) == precedence(GoVersion("v2.0.0"))


@pytest.mark.parametrize(
    "version",
    [
        pytest.param(GoVersion("2.11.1"), id="no-v"),
        pytest.param(GoVersion("v2.11"), id="no-patch"),
        pytest.param(GoVersion("v02.11.1"), id="leading-zero"),
        pytest.param(GoVersion("v2.11.1-"), id="empty-pre-release"),
        pytest.param(GoVersion("v1.1\u0661.0"), id="non-ascii-digit"),
    ],
)
def test_a_version_go_would_not_spell_has_no_precedence(version: GoVersion) -> None:
    """A version outside vMAJOR.MINOR.PATCH with its optional parts has no place."""
    assert precedence(version) is None


def test_a_version_either_file_spells_unreadably_is_a_finding_instead(tmp_path: Path) -> None:
    """A version precedence cannot order is reported in place of the comparison."""
    files = _swapped(_EXCEL, Prose("text v0.43.0"), Prose("text v0.43"))
    assert _run(tmp_path, files) == [
        Prose(f"{_EXCEL}: requires golang.org/x/text at v0.43, no Go module version")
    ]


@pytest.mark.parametrize("rel", [_EXCEL, _CLI])
def test_an_untracked_go_mod_is_a_finding(tmp_path: Path, rel: RelPath) -> None:
    """A go.mod git does not track holds nothing in a checkout, so the claim is unchecked."""
    assert _run(tmp_path, untracked={rel}) == [
        Prose(f"{rel}: not tracked, so the command line's requirements are unchecked")
    ]


@pytest.mark.parametrize("rel", [_EXCEL, _CLI])
def test_a_tracked_go_mod_the_work_tree_lacks_is_a_finding(tmp_path: Path, rel: RelPath) -> None:
    """A go.mod git tracks and the work tree lacks is unread, so the claim is unchecked."""
    files = {path: text for path, text in _FILES.items() if path != rel}
    assert _run(tmp_path, files, absent={rel}) == [
        Prose(f"{rel}: could not be read, so the command line's requirements are unchecked")
    ]


def test_a_require_the_reader_refuses_is_a_finding(tmp_path: Path) -> None:
    """A require line the manifest reader cannot read is reported as the reader words it."""
    files = _swapped(_CLI, Prose("text v0.43.0 // indirect"), Prose("text // indirect"))
    found = _run(tmp_path, files)
    assert len(found) == 1
    assert found[0].startswith(_CLI)
