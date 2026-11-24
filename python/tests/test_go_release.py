# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests of tools/go_release.py: the Go modules' release, hashed from the tree before any tag.

The unit tests read workspaces from texts.  The others drive git and go over a
toy repository of three modules laid out as the repository's are, a core at
``go/``, a loader at ``go/excel`` requiring it and a command at ``go/cmd/tool``
requiring both, offline: go's proxy is off, and git is pointed at a directory
that does not exist for any fetch of the toy's repository a test did not serve.
"""

from __future__ import annotations

import shutil
from typing import TYPE_CHECKING

import pytest
from _git_repo import commit, git

from tools import go_release
from tools._common import EnvName, RelPath
from tools._manifests import GoModule, GoVersion
from tools.commit_subjects import ReleaseVersion
from tools.go_release import (
    CannotCheckError,
    CommitId,
    Fetched,
    FileText,
    Hashes,
    Major,
    ModuleHash,
    RefLine,
    Revision,
    TagName,
    check,
    check_commit,
    check_publishable,
    check_published,
    check_tags,
    commit_of,
    dependency_order,
    differences,
    github_environment,
    move_major,
    pinned_requirements,
    read_release,
    recorded,
    rehearsal_findings,
    released,
    tree_repository,
    with_major,
    without_major,
    write,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping
    from pathlib import Path

TOY = "github.com/example/toy"
CORE, EXCEL = GoModule(f"{TOY}/go/v2"), GoModule(f"{TOY}/go/excel")
# The loader once a release of major 2 has moved it.
EXCEL_2 = GoModule(f"{TOY}/go/excel/v2")
TOOL = GoModule(f"{TOY}/go/cmd/tool")
PSEUDO = "v2.0.0-20000101000000-000000000000"
EXCEL_PSEUDO = "v0.0.0-20000101000000-000000000000"
RELEASE_TAGS = (TagName("v2.0.0"), TagName("go/v2.0.0"), TagName("go/excel/v2.0.0"))
RELEASE = ReleaseVersion("2.0.0")
_NO_OBJECT = "0" * 40
_CANNOT_PARSE = 2
# Why a test here starts processes: its claim is what git and go answer over a repository.
_DRIVES_GIT_AND_GO = "the release tool is git and go computing hashes and builds"


def _reader(files: Mapping[RelPath, FileText]) -> go_release.Reader:
    """Read a repo-relative path from ``files``, None where it holds none."""

    def read(rel: RelPath) -> FileText | None:
        return files.get(rel)

    return read


def _toy_files(version: ReleaseVersion = RELEASE) -> dict[RelPath, FileText]:
    """Return the toy repository's files before a release: its requirements pseudo-versions."""
    texts = {
        "haskell-shim/aletheia.cabal": f"name: toy\nversion: {version}.0\n",
        "go/go.work": "go 1.26.0\n\nuse (\n\t.\n\t./excel\n\t./cmd/tool\n)\n",
        "go/go.mod": f"module {CORE}\n\ngo 1.26.0\n",
        "go/core.go": "package toy\n\n// Answer is the core's answer.\nconst Answer = 42\n",
        "go/excel/go.mod": f"module {EXCEL}\n\ngo 1.26.0\n\nrequire {CORE} {PSEUDO}\n",
        "go/excel/excel.go": (
            f'package excel\n\nimport toy "{CORE}"\n\n// Doubled doubles it.\n'
            "const Doubled = toy.Answer * 2\n"
        ),
        "go/cmd/tool/go.mod": (
            f"module {TOOL}\n\ngo 1.26.0\n\nrequire (\n\t{EXCEL} {EXCEL_PSEUDO}\n"
            f"\t{CORE} {PSEUDO} // indirect\n)\n"
        ),
        "go/cmd/tool/main.go": (
            f'package main\n\nimport (\n\t"fmt"\n\n\ttoy "{CORE}"\n\t"{EXCEL}"\n)\n\n'
            "func main() { fmt.Println(toy.Answer, excel.Doubled) }\n"
        ),
        "README.md": f"Import {CORE} and {EXCEL}; run {TOOL}. The core is {CORE}.\n",
        "CHANGELOG.md": f"The core was {CORE}.\n",
    }
    return {RelPath(rel): FileText(text) for rel, text in texts.items()}


def _toy(root: Path, files: Mapping[RelPath, FileText]) -> Path:
    """Write ``files`` under ``root`` and commit them; return the root."""
    for rel, text in files.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text(text, encoding="utf-8")
    _ = git(root, "init", "-q")
    _ = commit(root, "the toy")
    return root


# The tagger an annotated tag records: a machine with no global identity (CI) refuses
# a tag without one.
_AS_TAGGER = (
    "-c",
    "user.name=Test",
    "-c",
    "user.email=test@example.com",
    "-c",
    "tag.gpgsign=false",
)


def _tag(root: Path, *names: TagName) -> None:
    """Tag HEAD with each of ``names``, annotated, unsigned, under a local identity."""
    for name in names:
        _ = git(root, *_AS_TAGGER, "tag", "-f", "-a", "-m", name, name)


def _ref_lines(root: Path, *names: TagName) -> list[RefLine]:
    """Return the lines a pre-push hook reads for pushing each tag of ``names`` anew."""
    return [
        RefLine(f"refs/tags/{name} {_object(root, name)} refs/tags/{name} {_NO_OBJECT}")
        for name in names
    ]


def _object(root: Path, revision: TagName) -> CommitId:
    """Return the object ``revision`` names, a tag object for an annotated tag."""
    return CommitId(git(root, "rev-parse", revision).strip())


def _replace(root: Path, rel: RelPath, text: FileText) -> None:
    """Write ``text`` over the toy's file ``rel``."""
    _ = (root / rel).write_text(text, encoding="utf-8")


def _only(found: list[Prose]) -> Prose:
    """Return the one finding of ``found``, failing the test on none or several."""
    assert len(found) == 1, found
    return found[0]


def _skip_without_go() -> None:
    """Skip loudly where no go is on the search path: every check here drives go."""
    if shutil.which("go") is None:
        pytest.skip("go toolchain not found on PATH: the release tool drives go; install Go")


@pytest.fixture(name="offline")
def fixture_offline(monkeypatch: pytest.MonkeyPatch) -> None:
    """Keep go and git off the network: no proxy, the toy's repository unreachable."""
    _skip_without_go()
    for name, value in {
        "GOPROXY": "off",
        "GOFLAGS": "",
        "GOTOOLCHAIN": "local",
        "GIT_CONFIG_COUNT": "1",
        "GIT_CONFIG_KEY_0": "url.file:///nonexistent/toy.insteadOf",
        "GIT_CONFIG_VALUE_0": f"https://{TOY}",
    }.items():
        monkeypatch.setenv(name, value)


@pytest.fixture(scope="module", name="prepared")
def fixture_prepared(tmp_path_factory: pytest.TempPathFactory) -> Iterator[Path]:
    """Return the toy after ``write``, committed and tagged as release 2.0.0 tags it."""
    _skip_without_go()
    with pytest.MonkeyPatch.context() as patch:
        for name, value in {"GOPROXY": "off", "GOFLAGS": "", "GOTOOLCHAIN": "local"}.items():
            patch.setenv(name, value)
        root = _toy(tmp_path_factory.mktemp("prepared"), _toy_files())
        assert move_major(root) == 0
        assert write(root) == 0
        _ = commit(root, "prepare 2.0.0")
        _tag(root, *RELEASE_TAGS)
        yield root


def _copy(prepared: Path, dest: Path) -> Path:
    """Return a copy of the prepared toy, repository included, for a test that changes it."""
    _ = shutil.copytree(prepared, dest, symlinks=True)
    return dest


def test_a_major_is_spelled_as_go_spells_it() -> None:
    """From 2 on a major is the path's /vN suffix, below 2 no suffix; a move replaces the old."""
    assert with_major(CORE, Major(3)) == f"{TOY}/go/v3"
    assert with_major(EXCEL, Major(2)) == f"{TOY}/go/excel/v2"
    assert with_major(CORE, Major(1)) == f"{TOY}/go"
    assert without_major(GoModule(f"{TOY}/go/excel/v12")) == EXCEL


def test_the_released_modules_are_those_another_module_requires() -> None:
    """The core and the loader are released; the command nothing requires is not."""
    release = read_release(_reader(_toy_files()))
    assert release.repository == TOY
    assert release.tag_version == "v2.0.0"
    assert [m.directory for m in released(release)] == ["go", "go/excel"]
    assert [m.directory for m in dependency_order(release)] == ["go", "go/excel", "go/cmd/tool"]


def test_a_workspace_it_cannot_read_is_no_verdict() -> None:
    """A module path off its directory, or a cabal file stating no version, cannot be checked."""
    files = _toy_files()
    files[RelPath("go/excel/go.mod")] = FileText(f"module {TOY}/elsewhere\n\ngo 1.26.0\n")
    with pytest.raises(CannotCheckError, match="does not end in go/excel"):
        _ = read_release(_reader(files))
    files = _toy_files()
    files[RelPath("haskell-shim/aletheia.cabal")] = FileText("name: toy\nversion: 2.0\n")
    with pytest.raises(CannotCheckError, match="states no version"):
        _ = read_release(_reader(files))


def test_every_requirement_on_a_released_module_is_pinned_to_the_release() -> None:
    """Block and one-line entries move to the version, an old major to the path; nothing else."""
    files = _toy_files()
    shipped = released(read_release(_reader(files)))
    tool = files[RelPath("go/cmd/tool/go.mod")].replace(f"{CORE} ", f"{TOY}/go ")
    pinned = pinned_requirements(FileText(tool), shipped, GoVersion("v2.0.0"))
    assert pinned == (
        f"module {TOOL}\n\ngo 1.26.0\n\nrequire (\n\t{EXCEL} v2.0.0\n"
        f"\t{CORE} v2.0.0 // indirect\n)\n"
    )
    one_line = files[RelPath("go/excel/go.mod")]
    assert pinned_requirements(one_line, shipped, GoVersion("v2.0.0")).endswith(
        f"require {CORE} v2.0.0\n"
    )


def test_a_go_sum_differing_from_the_tree_is_named() -> None:
    """Each requiring go.sum's two lines are read; one differing is named, an equal one is not."""
    files = _toy_files()
    files[RelPath("go/excel/go.mod")] = FileText(
        f"module {EXCEL}\n\ngo 1.26.0\n\nrequire {CORE} v2.0.0\n"
    )
    files[RelPath("go/excel/go.sum")] = FileText(
        f"{CORE} v2.0.0 h1:zip=\n{CORE} v2.0.0/go.mod h1:mod=\n"
    )
    release = read_release(_reader(files))
    records = recorded(_reader(files), release, CORE)
    tree = Hashes(ModuleHash("h1:zip="), ModuleHash("h1:mod="))
    assert records == {RelPath("go/excel/go.sum"): tree}
    version = GoVersion("v2.0.0")
    assert differences(tree, records, CORE, version) == []
    (finding,) = differences(Hashes(ModuleHash("h1:other="), tree.mod), records, CORE, version)
    assert finding.startswith("go/excel/go.sum records")
    assert "h1:other=" in finding
    assert differences(Prose("unreachable"), records, CORE, version) == ["unreachable"]


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_move_major_moves_every_spelling_but_the_history_and_the_command(tmp_path: Path) -> None:
    """The core and loader move to the cabal major; CHANGELOG and the unreleased command stay."""
    files = _toy_files(ReleaseVersion("3.0.0"))
    files[RelPath("MOVED.md")] = FileText(f"Already {TOY}/go/excel/v3.\n")
    root = _toy(tmp_path, files)
    assert move_major(root) == 0
    assert (root / "MOVED.md").read_text(encoding="utf-8") == f"Already {TOY}/go/excel/v3.\n"
    readme = (root / "README.md").read_text(encoding="utf-8")
    assert readme == (
        f"Import {TOY}/go/v3 and {TOY}/go/excel/v3; run {TOOL}. The core is {TOY}/go/v3.\n"
    )
    assert (root / "go/go.mod").read_text(encoding="utf-8").startswith(f"module {TOY}/go/v3\n")
    assert (root / "CHANGELOG.md").read_text(encoding="utf-8") == f"The core was {CORE}.\n"
    assert move_major(root) == 0
    assert (root / "README.md").read_text(encoding="utf-8") == readme


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_write_refuses_a_released_module_off_the_release_major(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A major release moves the paths first: write names the module and the command."""
    root = _toy(tmp_path, _toy_files())
    assert write(root) == 1
    assert f"{EXCEL} carries no major 2, the release's: run" in capsys.readouterr().out
    assert (root / "go/excel/go.mod").read_text(encoding="utf-8").endswith(f"{CORE} {PSEUDO}\n")


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_write_records_what_the_tags_publish_and_a_second_write_changes_nothing(
    prepared: Path, tmp_path: Path
) -> None:
    """Each requirement names the release, each go.sum its lines, go.work its replaces."""
    root = _copy(prepared, tmp_path / "toy")
    excel = (root / "go/excel/go.mod").read_text(encoding="utf-8")
    assert excel.endswith(f"require {CORE} v2.0.0\n")
    work = (root / "go/go.work").read_text(encoding="utf-8")
    assert f"replace {CORE} v2.0.0 => ./\n" in work
    assert f"replace {EXCEL_2} v2.0.0 => ./excel\n" in work
    sums = (root / "go/cmd/tool/go.sum").read_text(encoding="utf-8")
    assert f"{CORE} v2.0.0 h1:" in sums
    assert f"{EXCEL_2} v2.0.0/go.mod h1:" in sums
    written = ("go/go.work", "go/excel/go.sum", "go/cmd/tool/go.sum", "go/cmd/tool/go.mod")
    before = {rel: (root / rel).read_bytes() for rel in written}
    assert write(root) == 0
    assert {rel: (root / rel).read_bytes() for rel in written} == before


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_the_tagged_commit_holds_its_hashes_and_its_tags_pass(prepared: Path) -> None:
    """The release commit hashes as recorded, and pushing its three tags is allowed."""
    head = commit_of(prepared, Revision("v2.0.0"))
    assert not check_commit(prepared, head, RELEASE)
    assert not check_tags(prepared, _ref_lines(prepared, *RELEASE_TAGS))


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_tags_off_the_release_are_refused(prepared: Path, tmp_path: Path) -> None:
    """A go/ tag on the unreleased command, a malformed one, and one version on two commits."""
    root = _copy(prepared, tmp_path / "toy")
    command, candidate = TagName("go/cmd/tool/v2.0.0"), TagName("go/v2.0.0-rc1")
    _tag(root, command, candidate)
    found = _only(check_tags(root, _ref_lines(root, command)))
    assert "go/cmd/tool is no released module" in found
    found = _only(check_tags(root, _ref_lines(root, candidate)))
    assert "is no <directory>/vX.Y.Z" in found
    _replace(root, RelPath("README.md"), FileText("moved on\n"))
    head = commit(root, "after")
    _tag(root, TagName("go/v2.0.0"))
    found = _only(check_tags(root, _ref_lines(root, TagName("v2.0.0"), TagName("go/v2.0.0"))))
    assert "release 2.0.0's tags name 2 commits" in found
    branch = RefLine(f"refs/heads/main {head} refs/heads/main {_NO_OBJECT}")
    deletion = RefLine(f"(delete) {_NO_OBJECT} refs/tags/go/v2.0.0 {head}")
    assert not check_tags(root, [branch, deletion])


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_a_commit_recording_no_release_version_is_refused(tmp_path: Path) -> None:
    """Before write, no go.sum records what a tag would publish: the commit check names each."""
    root = _toy(tmp_path, _toy_files())
    found = check_commit(root, commit_of(root, Revision("HEAD")), None)
    assert len(found) == len((CORE, EXCEL))
    assert all("no go.sum records what its tag publishes" in line for line in found)


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_check_serves_the_prepared_versions_and_builds(
    prepared: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The tree hashes as recorded, so both versions are served and every module builds."""
    assert check(prepared) == 0
    out = capsys.readouterr().out
    assert f"{CORE}@v2.0.0 served from the tree" in out
    assert f"{EXCEL_2}@v2.0.0 served from the tree" in out


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_a_core_changed_after_its_hashes_turns_every_check_red(
    prepared: Path, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The sweep falls back to GitHub and fails; the changed commit fails its check too."""
    root = _copy(prepared, tmp_path / "toy")
    _replace(root, RelPath("go/core.go"), FileText("package toy\n\nconst Answer = 43\n"))
    assert check(root) == 1
    out = capsys.readouterr().out
    assert "not served from the tree: go/excel/go.sum records" in out
    assert "run `python -m tools.go_release write`" in out
    found = check_commit(root, CommitId(commit(root, "changed")), None)
    named = {line.split(" records ")[0] for line in found}
    assert named == {"go/excel/go.sum", "go/cmd/tool/go.sum"}


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_after_the_release_a_moved_core_resolves_the_published_tag(
    prepared: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Main moves on after the tag: the core comes from the published tag, Excel from the tree.

    GitHub is a scratch repository holding the release's tags.  The build cache
    takes only the served versions' download entries: a clone of the tree's
    repository left in it, keyed by GitHub's URL, would hand cmd/go the moved
    core under the published tag.
    """
    tree_repository(prepared, tmp_path / "github", RELEASE_TAGS[1:])
    monkeypatch.setenv("GIT_CONFIG_COUNT", "2")
    monkeypatch.setenv("GIT_CONFIG_KEY_0", f"url.file://{tmp_path / 'github'}.insteadOf")
    monkeypatch.setenv("GIT_CONFIG_KEY_1", "protocol.file.allow")
    monkeypatch.setenv("GIT_CONFIG_VALUE_1", "always")
    root = _copy(prepared, tmp_path / "toy")
    _replace(root, RelPath("go/core.go"), FileText("package toy\n\nconst Answer = 45\n"))
    assert check(root) == 0


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_the_published_modules_are_held_to_the_tags_lines(
    prepared: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """What GitHub serves at the release is compared with the tag's lines, and a change named.

    The stand-in GitHub first holds the release's tags where the release made
    them, then on a commit whose core moved after the hashes were recorded.
    """
    _github_through(monkeypatch, prepared)
    assert not check_published(prepared, RELEASE)
    moved = _copy(prepared, tmp_path / "moved")
    _replace(moved, RelPath("go/core.go"), FileText("package toy\n\nconst Answer = 44\n"))
    _ = commit(moved, "moved")
    _tag(moved, *RELEASE_TAGS[1:])
    _github_through(monkeypatch, moved)
    found = check_published(prepared, RELEASE)
    assert found
    assert all(f"{CORE}@v2.0.0" in line for line in found)


def test_check_published_refuses_a_version_that_is_none() -> None:
    """The command line takes X.Y.Z and nothing else."""
    with pytest.raises(SystemExit) as stopped:
        _ = go_release.main([go_release.W("check-published"), go_release.W("v2.0")])
    assert stopped.value.code == _CANNOT_PARSE


def _github_through(monkeypatch: pytest.MonkeyPatch, github: Path) -> None:
    """Make every fetch from the toy's GitHub reach ``github``, a repository standing in for it."""
    monkeypatch.setenv("GIT_CONFIG_COUNT", "2")
    monkeypatch.setenv("GIT_CONFIG_KEY_0", f"url.file://{github}.insteadOf")
    monkeypatch.setenv("GIT_CONFIG_KEY_1", "protocol.file.allow")
    monkeypatch.setenv("GIT_CONFIG_VALUE_1", "always")


def test_github_s_answer_for_a_commit_is_held_to_its_own_hashes() -> None:
    """Equal hashes pass; a differing pair is named; a fetch that failed is its own finding."""
    local = Hashes(ModuleHash("h1:zip="), ModuleHash("h1:mod="))
    pseudo = GoVersion("v2.0.0-20000101000000-000000000000")
    assert not rehearsal_findings(CORE, Fetched(pseudo, local), local)
    other = Fetched(pseudo, Hashes(ModuleHash("h1:other="), local.mod))
    found = _only(rehearsal_findings(CORE, other, local))
    assert found.startswith(f"GitHub serves {CORE}@{pseudo} as h1:other=")
    assert rehearsal_findings(CORE, Prose("unreachable"), local) == ["unreachable"]
    assert rehearsal_findings(CORE, Fetched(pseudo, local), Prose("no tree")) == ["no tree"]


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_the_dry_run_rehearses_a_prepared_commit_end_to_end(
    prepared: Path,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """Before the tag: the commit holds its hashes, and GitHub serves it as hashed.

    No tag exists yet, here or on the stand-in GitHub, so go names the commit by
    a pseudo-version of the release's major.
    """
    root = _copy(prepared, tmp_path / "toy")
    for tag in RELEASE_TAGS:
        _ = git(root, "tag", "-d", tag)
    _github_through(monkeypatch, root)
    assert not check_publishable(root, commit_of(root, Revision("HEAD")))
    out = capsys.readouterr().out
    assert f"GitHub serves {CORE}@v2.0.0-" in out
    assert f"GitHub serves {EXCEL_2}@v2.0.0-" in out


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_the_dry_run_names_a_commit_moved_after_its_hashes(
    prepared: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A prepared commit whose core moved after write fails the dry run as it would the tag."""
    root = _copy(prepared, tmp_path / "toy")
    _replace(root, RelPath("go/core.go"), FileText("package toy\n\nconst Answer = 46\n"))
    moved = CommitId(commit(root, "moved"))
    _github_through(monkeypatch, root)
    named = {line.split(" records ")[0] for line in check_publishable(root, moved)}
    assert named == {"go/excel/go.sum", "go/cmd/tool/go.sum"}


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_the_dry_run_of_a_commit_preparing_nothing_rehearses_the_route_alone(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A commit recording no release version is no finding: the dry run says so and fetches it."""
    root = _toy(tmp_path, _toy_files())
    _github_through(monkeypatch, root)
    assert not check_publishable(root, commit_of(root, Revision("HEAD")))
    assert "prepares no release of the Go modules" in capsys.readouterr().out


@pytest.mark.process(_DRIVES_GIT_AND_GO)
@pytest.mark.usefixtures("offline")
def test_the_dry_run_of_a_commit_the_route_cannot_serve_is_a_finding(
    prepared: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A commit GitHub does not hold is no release: each module's fetch is named."""
    elsewhere = _toy(tmp_path / "elsewhere", _toy_files())
    _github_through(monkeypatch, elsewhere)
    found = check_publishable(prepared, commit_of(prepared, Revision("v2.0.0")))
    assert len(found) == len((CORE, EXCEL_2))
    assert all(line.startswith("go mod download ") for line in found)


def test_no_fetch_of_the_repository_leaves_for_a_proxy(tmp_path: Path) -> None:
    """GitHub's environment names the repository private and gives go no proxy at all.

    A module proxy or checksum database would log the repository's paths and
    commits outside it, so neither is ever on the route.
    """
    release = read_release(_reader(_toy_files()))
    env = github_environment(tmp_path, release)
    assert env[EnvName("GOPRIVATE")] == TOY
    assert env[EnvName("GOPROXY")] == "off"
    assert env[EnvName("GOMODCACHE")] == str(tmp_path)
