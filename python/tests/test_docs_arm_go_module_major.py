# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The documentation gate's arm holding the core Go module's path to the release's major.

A cabal version of major two or more owes the path ``go/go.mod`` declares the
suffix ``/v<major>``: another suffix, or none, is a finding naming the path, the
version and the major, and a suffix Go refuses (a leading zero, a ``/v5`` before
the path's last element) counts as none. A major below two owes a path without
one. A runbook no longer tagging or pushing ``go/vX.Y.Z`` on a line of its own
is a finding each; so is each of the runbook, ``go/go.mod`` and the cabal file
untracked or absent from the work tree, a ``go.mod`` declaring no module path,
and a cabal file stating no version of numbers alone, each leaving the path's
major unchecked. The cabal field is read as Cabal reads it, in any case.
"""

from __future__ import annotations

from types import MappingProxyType
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools._manifests import GoModule
from tools.docs_arms.go_module_major import CabalVersion, findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Collection, Mapping
    from pathlib import Path

_RUNBOOK = RelPath("docs/development/RELEASE.md")
_GO_MOD = RelPath("go/go.mod")
_CABAL = RelPath("haskell-shim/aletheia.cabal")
_UNCHECKED = "the major the Go module's path carries is unchecked"
_TAG_FINDING = Prose(
    "docs/development/RELEASE.md: no longer tags the Go module (git tag -s go/vX.Y.Z), "
    + f"so {_UNCHECKED}"
)
_PUSH_FINDING = Prose(
    "docs/development/RELEASE.md: no longer pushes the Go module "
    + f"(git push origin ... go/vX.Y.Z), so {_UNCHECKED}"
)

# Read-only, so a test's edit is a copy and no other test sees it.
_FILES: Mapping[RelPath, Prose] = MappingProxyType(
    {
        _RUNBOOK: Prose(
            "# Releasing\n\n~~~bash\ngit tag -s vX.Y.Z -m x\ngit tag -s go/vX.Y.Z -m y\n"
            + "git push origin vX.Y.Z go/vX.Y.Z\n~~~\n"
        ),
        _GO_MOD: Prose("module github.com/example/aletheia/go/v5\n\ngo 1.24.0\n"),
        _CABAL: Prose(
            "cabal-version: 3.0\nname:               aletheia\nversion:            5.0.0.0\n"
        ),
    }
)


def _with(rel: RelPath, text: Prose) -> dict[RelPath, Prose]:
    """Return the planted files with ``rel`` holding ``text``."""
    return {**_FILES, rel: text}


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


def _module(path: GoModule) -> Prose:
    """Return a go.mod declaring the module ``path``."""
    return Prose(f"module {path}\n\ngo 1.24.0\n")


def _cabal(version: CabalVersion) -> Prose:
    """Return a cabal file stating ``version``."""
    return Prose(f"cabal-version: 3.0\nname: aletheia\nversion: {version}\n")


def test_a_path_carrying_the_releases_major_is_clean(tmp_path: Path) -> None:
    """A path ending /v5 under a cabal version of major 5 is what the Go tag serves."""
    assert _run(tmp_path) == list[Prose]()


def test_a_release_moving_the_major_past_the_path_is_a_finding(tmp_path: Path) -> None:
    """A cabal version raised to major 6 leaves a path ending /v5 a finding naming both."""
    assert _run(tmp_path, _with(_CABAL, _cabal(CabalVersion("6.0.0.0")))) == [
        Prose(
            "go/go.mod: the module path github.com/example/aletheia/go/v5 ends /v5, where "
            + "haskell-shim/aletheia.cabal's version 6.0.0.0 is a release of major 6: Go "
            + "fetches the tag go/v6.x.y only for a path ending /v6"
        )
    ]


def test_a_path_moved_with_the_release_is_clean(tmp_path: Path) -> None:
    """The path ending /v6 beside a cabal version of major 6 is clean again."""
    files = _with(_CABAL, _cabal(CabalVersion("6.0.0.0"))) | {
        _GO_MOD: _module(GoModule("github.com/example/aletheia/go/v6"))
    }
    assert _run(tmp_path, files) == list[Prose]()


def test_a_major_of_two_or_more_without_a_suffix_is_a_finding(tmp_path: Path) -> None:
    """A path with no /vN under a major of 2 is a finding; Go refuses it any tag past v1."""
    files = _with(_CABAL, _cabal(CabalVersion("2.1.0.0"))) | {
        _GO_MOD: _module(GoModule("github.com/example/aletheia/go"))
    }
    assert _run(tmp_path, files) == [
        Prose(
            "go/go.mod: the module path github.com/example/aletheia/go carries no major suffix "
            + "Go accepts, where haskell-shim/aletheia.cabal's version 2.1.0.0 is a release of "
            + "major 2: Go fetches the tag go/v2.x.y only for a path ending /v2"
        )
    ]


@pytest.mark.parametrize("version", [CabalVersion("0.3.0.0"), CabalVersion("1.2.0.0")])
def test_a_major_below_two_owes_a_path_without_a_suffix(
    tmp_path: Path, version: CabalVersion
) -> None:
    """Below major 2 the path has no /vN: one without is clean, one with it a finding."""
    plain = _with(_CABAL, _cabal(version)) | {
        _GO_MOD: _module(GoModule("github.com/example/aletheia/go"))
    }
    assert _run(tmp_path / "plain", plain) == list[Prose]()
    major = version.split(".", 1)[0]
    assert _run(tmp_path / "suffixed", _with(_CABAL, _cabal(version))) == [
        Prose(
            "go/go.mod: the module path github.com/example/aletheia/go/v5 ends /v5, where "
            + f"haskell-shim/aletheia.cabal's version {version} is a release of major {major}: "
            + f"Go fetches the tag go/v{major}.x.y only for a path without a major suffix"
        )
    ]


def test_a_major_of_two_digits_is_read_whole(tmp_path: Path) -> None:
    """Major 12 owes /v12, so /v1 does not pass for it."""
    files = _with(_CABAL, _cabal(CabalVersion("12.0.0.0")))
    v12 = files | {_GO_MOD: _module(GoModule("example.com/m/v12"))}
    v1 = files | {_GO_MOD: _module(GoModule("example.com/m/v1"))}
    assert _run(tmp_path / "v12", v12) == list[Prose]()
    assert len(_run(tmp_path / "v1", v1)) == 1


def test_a_runbook_no_longer_tagging_the_go_module_is_a_finding(tmp_path: Path) -> None:
    """Without the go/vX.Y.Z tag the path's major holds nothing, so the runbook is a finding."""
    files = _with(
        _RUNBOOK, Prose("~~~bash\ngit tag -s vX.Y.Z -m x\ngit push origin vX.Y.Z go/vX.Y.Z\n~~~\n")
    )
    assert _run(tmp_path, files) == [_TAG_FINDING]


def test_a_runbook_no_longer_pushing_the_go_tag_is_a_finding(tmp_path: Path) -> None:
    """A go/vX.Y.Z tag left unpushed never reaches GitHub, so the runbook is a finding."""
    files = _with(
        _RUNBOOK, Prose("~~~bash\ngit tag -s go/vX.Y.Z -m y\ngit push origin vX.Y.Z\n~~~\n")
    )
    assert _run(tmp_path, files) == [_PUSH_FINDING]


def test_the_tag_named_in_prose_alone_holds_nothing(tmp_path: Path) -> None:
    """A sentence naming the commands is no step: only a line opening on each one counts."""
    prose = Prose("Never run git tag -s go/vX.Y.Z by hand, nor git push origin vX.Y.Z go/vX.Y.Z.\n")
    assert _run(tmp_path, _with(_RUNBOOK, prose)) == [_TAG_FINDING, _PUSH_FINDING]


@pytest.mark.parametrize("rel", [_RUNBOOK, _GO_MOD, _CABAL])
def test_an_untracked_file_is_a_finding(tmp_path: Path, rel: RelPath) -> None:
    """A file git does not track holds nothing in a checkout, so the major is unchecked."""
    assert _run(tmp_path, untracked={rel}) == [Prose(f"{rel}: not tracked, so {_UNCHECKED}")]


@pytest.mark.parametrize("rel", [_GO_MOD, _CABAL])
def test_a_tracked_file_the_work_tree_lacks_is_a_finding(tmp_path: Path, rel: RelPath) -> None:
    """A manifest git tracks and the work tree lacks is unread, so the major is unchecked."""
    assert _run(tmp_path, _without(rel), absent={rel}) == [
        Prose(f"{rel}: could not be read, so {_UNCHECKED}")
    ]


def test_a_tracked_runbook_the_work_tree_lacks_is_reported_by_the_read_and_the_arm(
    tmp_path: Path,
) -> None:
    """The runbook absent is the gate's unread finding, then the arm's; the path is still read."""
    files = _without(_RUNBOOK) | {_CABAL: _cabal(CabalVersion("6.0.0.0"))}
    found = _run(tmp_path, files, absent={_RUNBOOK})
    assert found[:2] == [
        Prose("docs/development/RELEASE.md: could not be read, so what it says is unchecked"),
        Prose(f"docs/development/RELEASE.md: could not be read, so {_UNCHECKED}"),
    ]
    assert len(found) == 3
    assert found[2].startswith("go/go.mod: the module path")


@pytest.mark.parametrize(
    "path",
    [GoModule("example.com/m/v05"), GoModule("example.com/v5/m"), GoModule("example.com/mv5")],
)
def test_a_suffix_go_refuses_counts_as_none(tmp_path: Path, path: GoModule) -> None:
    """A leading zero, a /v5 before the last element or a v5 without its slash is no suffix."""
    assert _run(tmp_path, _with(_GO_MOD, _module(path))) == [
        Prose(
            f"go/go.mod: the module path {path} carries no major suffix Go accepts, where "
            + "haskell-shim/aletheia.cabal's version 5.0.0.0 is a release of major 5: Go "
            + "fetches the tag go/v5.x.y only for a path ending /v5"
        )
    ]


@pytest.mark.parametrize(
    "line", [Prose("Version: 5.0.0.0"), Prose("version : 5.0.0.0"), Prose("VERSION:\t5.0.0.0")]
)
def test_the_version_field_is_read_as_cabal_reads_it(tmp_path: Path, line: Prose) -> None:
    """Cabal's field names are case-insensitive and allow a blank before the colon."""
    cabal = Prose(f"cabal-version: 3.0\nname: aletheia\n{line}\n")
    assert _run(tmp_path, _with(_CABAL, cabal)) == list[Prose]()


def test_a_version_with_a_suffix_states_no_version(tmp_path: Path) -> None:
    """A version carrying more than numbers is no release version, so the major is unchecked."""
    found = _run(tmp_path, _with(_CABAL, _cabal(CabalVersion("5.0.0.0-rc1"))))
    assert found == [Prose(f"haskell-shim/aletheia.cabal: states no version, so {_UNCHECKED}")]


def test_a_runbook_finding_comes_before_a_manifest_one(tmp_path: Path) -> None:
    """A runbook without the tag and a go.mod without a module are two findings, in order."""
    files = _with(_RUNBOOK, Prose("# Releasing\n")) | {_GO_MOD: Prose("go 1.24.0\n")}
    assert _run(tmp_path, files) == [
        _TAG_FINDING,
        _PUSH_FINDING,
        Prose(f"go/go.mod: declares 0 module directive(s), not one module path, so {_UNCHECKED}"),
    ]


def test_a_go_mod_declaring_no_module_is_a_finding(tmp_path: Path) -> None:
    """A go.mod with no module directive has no path to hold, which the finding says."""
    assert _run(tmp_path, _with(_GO_MOD, Prose("go 1.24.0\n"))) == [
        Prose(f"go/go.mod: declares 0 module directive(s), not one module path, so {_UNCHECKED}")
    ]


def test_a_cabal_file_stating_no_version_is_a_finding(tmp_path: Path) -> None:
    """A cabal file without a version line names no release, so the major is unchecked."""
    found = _run(tmp_path, _with(_CABAL, Prose("cabal-version: 3.0\nname: aletheia\n")))
    assert found == [Prose(f"haskell-shim/aletheia.cabal: states no version, so {_UNCHECKED}")]


_CORE = "github.com/example/aletheia/go/v5"
_WORK = RelPath("go/go.work")
_EXCEL_MOD = RelPath("go/excel/go.mod")
_TOOL_MOD = RelPath("go/cmd/tool/go.mod")
_WORKSPACE: Mapping[RelPath, Prose] = MappingProxyType(
    {
        **_FILES,
        _WORK: Prose("go 1.24.0\n\nuse (\n\t.\n\t./excel\n\t./cmd/tool\n)\n"),
        _EXCEL_MOD: _module(GoModule("github.com/example/aletheia/go/excel")),
        _TOOL_MOD: _module(GoModule("github.com/example/aletheia/go/cmd/tool")),
    }
)


def test_a_spelling_at_the_modules_major_is_clean(tmp_path: Path) -> None:
    """A file importing the core at the major its go.mod declares, ending a sentence, is clean."""
    files = _with(RelPath("README.md"), Prose(f"Import {_CORE}/aletheia, or {_CORE}.\n"))
    assert _run(tmp_path, files) == list[Prose]()


def test_a_spelling_at_another_major_is_a_finding(tmp_path: Path) -> None:
    """A spelling the major move missed names the file, the spelling and the module's path."""
    files = _with(
        RelPath("README.md"), Prose("go get github.com/example/aletheia/go/v4/aletheia\n")
    )
    assert _run(tmp_path, files) == [
        Prose(
            "README.md: spells github.com/example/aletheia/go/v4, where the module's path is "
            + _CORE
        )
    ]


def test_the_history_and_the_checksums_keep_their_majors(tmp_path: Path) -> None:
    """CHANGELOG.md, .archive/ and a go.sum record the past or a hash, never a path now."""
    old = Prose("github.com/example/aletheia/go/v4 v4.0.0 h1:x=\n")
    files = {
        **_FILES,
        RelPath("CHANGELOG.md"): old,
        RelPath(".archive/round.md"): old,
        RelPath("go/excel/go.sum"): old,
    }
    assert _run(tmp_path, files) == list[Prose]()


def test_each_workspace_module_is_held_to_its_own_path(tmp_path: Path) -> None:
    """The longest module path owns a spelling: Excel at a major it lacks is a finding.

    The command's path and a file name beside the core's path are no spelling of
    the core.
    """
    text = Prose(
        "github.com/example/aletheia/go/excel/v5 and github.com/example/aletheia/go/cmd/tool"
        + " and github.com/example/aletheia/go.mod\n"
    )
    files = {**_WORKSPACE, RelPath("docs/GO.md"): text}
    assert _run(tmp_path, files) == [
        Prose(
            "docs/GO.md: spells github.com/example/aletheia/go/excel/v5, where the module's path"
            + " is github.com/example/aletheia/go/excel"
        )
    ]


def test_a_workspace_module_it_cannot_read_leaves_the_spellings_unchecked(tmp_path: Path) -> None:
    """go.work using a module whose go.mod is not tracked leaves every spelling unchecked."""
    files = {path: text for path, text in _WORKSPACE.items() if path != _EXCEL_MOD}
    assert _run(tmp_path, files) == [
        Prose(
            "go/excel/go.mod: not tracked, so the spellings of the Go modules' paths are unchecked"
        )
    ]
