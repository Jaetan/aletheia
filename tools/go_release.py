# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Release the Go modules: move their majors, record their hashes, hold every tag to them.

A module of the Go workspace that another of its modules requires is released
with the repository: its path carries the release's major (``/vN`` from 2 on),
and the release tags it ``<directory>/vX.Y.Z`` beside ``vX.Y.Z``, the directory
being the module's (``go``, ``go/excel``).  The release's version is the one
``haskell-shim/aletheia.cabal`` states as ``X.Y.Z.0``.

Go records a module only by the hash of its contents, the ``h1:`` lines of each
requiring module's ``go.sum``, and Go's public checksum database keeps the first
hash it sees for a version, so every hash is computed from the tree before
any tag exists, by cmd/go itself: the tree is committed to a scratch repository
and tagged there, and cmd/go fetches it through git's ``insteadOf`` into a
module cache of its own, never the user's.  A cache that fetched from the
scratch repository is never built in, since cmd/go keys its clone by GitHub's
URL and reads that clone's tags before the remote's: a build cache receives the
served versions' download entries alone.

Commands:

* ``move-major``: every tracked spelling of a released module's path moves to
  the release's major; ``CHANGELOG.md``, ``.archive/``, each ``go.sum`` and
  ``go/go.work`` are left to their own rules.
* ``write``: every requirement on a released module names the release's
  version, ``go/go.work`` replaces that version by the tree, and each module
  requiring a released one is tidied against the tree served at that version,
  required modules first.  A second run changes nothing.
* ``check``: each module builds outside the workspace as a consumer resolves
  it.  A requirement at the release's version is served from the tree where the
  tree's hashes equal every ``go.sum`` line recording them, and otherwise
  resolves from GitHub, which holds it once the release is tagged.
* ``check-commit REV``: the commit holds, for each released module at the
  version its cabal file states, the hashes every requiring ``go.sum`` records.
* ``check-tags``: reads the ref lines git hands a pre-push hook on stdin.  The
  release tags of one version name one commit, each ``go/`` tag a released
  module's directory, and that commit passes ``check-commit`` at that version.
* ``check-published X.Y.Z``: the released modules at ``vX.Y.Z``, fetched from
  GitHub, carry the hashes the tagged commit records.
* ``check-publishable REV``: the release's dry run, before any tag exists.
  The commit holds its recorded hashes where it prepares a release, and
  GitHub serves each released module at the commit itself, a pseudo-version,
  with the hashes go computes from the commit's own objects: the route
  ``check-published`` takes once tagged.

Every fetch of this repository's modules goes to GitHub directly
(``GOPRIVATE`` names the repository, and ``GOPROXY`` is off), or to a scratch
repository: none passes through a module proxy or a checksum database, which
would log the repository's paths and commits outside it.

Exit codes: 0 every hash and build holds; 1 a finding, each named; 2 cannot
check (git or go absent, a manifest unread, a revision unknown).
"""

from __future__ import annotations

import argparse
import json
import os
import posixpath
import re
import shutil
import sys
import tempfile
from graphlib import TopologicalSorter
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType, NotRequired, TypedDict, cast

from tools._common import (
    CommandWord,
    EnvName,
    EnvValue,
    HelpText,
    RelPath,
    emit,
    find_executable,
    git_clean_env,
)
from tools._common import run_capture as _run
from tools._manifests import (
    GoModule,
    GoRequire,
    GoVersion,
    ManifestError,
    ManifestText,
    go_module,
    go_requires,
    go_uses,
)
from tools._progress import reporting
from tools.commit_subjects import VERSION_PATTERN, ReleaseVersion

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
GO_WORK = RelPath("go/go.work")
CABAL = RelPath("haskell-shim/aletheia.cabal")
# The files the major move leaves alone: history, hashes, and the workspace's
# replaces, which ``write`` rewrites.
_UNMOVED = re.compile(r"^(?:CHANGELOG\.md|\.archive/.*|.*go\.sum|go/go\.work)$")

# A module's hash as go.sum records it, ``h1:`` and a base64 SHA-256.
ModuleHash = NewType("ModuleHash", str)
# A git revision as a user names it, and the commit id it resolves to.
Revision = NewType("Revision", str)
CommitId = NewType("CommitId", str)
# The import path of the repository's root, ``github.com/<owner>/<name>``.
RepositoryPath = NewType("RepositoryPath", str)
# A tag name; a tracked file's text; what a command printed on one stream; a ref line.
TagName = NewType("TagName", str)
FileText = NewType("FileText", str)
Output = NewType("Output", str)
RefLine = NewType("RefLine", str)
# A module path as the module cache spells it, and a major version.
EscapedPath = NewType("EscapedPath", str)
Major = NewType("Major", int)

type Reader = Callable[[RelPath], FileText | None]
type Environment = Mapping[EnvName, EnvValue]

W = CommandWord
_CABAL_VERSION = re.compile(
    rf"^version[ \t]*:\s*({VERSION_PATTERN})\.0[ \t]*$", re.MULTILINE | re.IGNORECASE
)
_MAJOR_SUFFIX = re.compile(r"/v([1-9][0-9]*)$")
_RELEASE_TAG = re.compile(rf"^(?:(?P<directory>go(?:/[^/]+)*)/)?v(?P<version>{VERSION_PATTERN})$")
# What makes a module path's spelling go on: a character a path element holds, or a
# dot before one; a dot before anything else ends a sentence, not the path.
_PATH_GOES_ON = r"[A-Za-z0-9_~\-]|\.[A-Za-z0-9_~\-]"
_FIRST_SUFFIXED = Major(2)
_SUM_FIELDS = 3
_REF_FIELDS = 4
_NO_OBJECT = re.compile(r"^0+$")
# What git commits and tags under in a scratch repository: none of the user's identity,
# signing or hooks.
_SCRATCH_GIT = (
    *(W("-c"), W("user.name=go-release"), W("-c"), W("user.email=go-release@invalid")),
    *(W("-c"), W("commit.gpgsign=false"), W("-c"), W("tag.gpgsign=false")),
    *(W("-c"), W("core.hooksPath=/dev/null"), W("-c"), W("init.defaultBranch=main")),
)


class CannotCheckError(Exception):
    """Something the check reads is absent or unreadable, so nothing is decided."""


class Ran(NamedTuple):
    """A command's exit status and its two streams."""

    status: ExitStatus
    out: Output
    err: Output


class Module(NamedTuple):
    """A module of the workspace: its path, its directory from the root, its requirements."""

    path: GoModule
    directory: RelPath
    requires: list[GoRequire]


class Hashes(NamedTuple):
    """A module version's two go.sum hashes: of its zip, and of its go.mod."""

    zip: ModuleHash | None
    mod: ModuleHash | None


class Release(NamedTuple):
    """The workspace as one revision holds it, and the release version it states."""

    version: ReleaseVersion
    modules: list[Module]
    repository: RepositoryPath

    @property
    def tag_version(self) -> GoVersion:
        """Return the version Go names the release by, ``vX.Y.Z``."""
        return GoVersion(f"v{self.version}")


class GoTag(NamedTuple):
    """A go/ tag being pushed, and the module directory it names."""

    name: TagName
    directory: RelPath


class Fetched(NamedTuple):
    """A module version go fetched: the version it resolved to, and its hashes."""

    version: GoVersion
    hashes: Hashes


class _Downloaded(TypedDict):
    """What ``go mod download -json`` prints of one module version."""

    Version: NotRequired[GoVersion]
    Sum: NotRequired[ModuleHash]
    GoModSum: NotRequired[ModuleHash]
    Error: NotRequired[Prose]


class _ModuleVersion(TypedDict):
    """A module and, where the replace names one, its version, as ``go work edit -json`` prints."""

    Path: GoModule
    Version: NotRequired[GoVersion]


class _Replace(TypedDict):
    """One replace of ``go work edit -json``: what it replaces."""

    Old: _ModuleVersion


class _Workspace(TypedDict):
    """The part of ``go work edit -json`` read here: the replaces."""

    Replace: NotRequired[list[_Replace] | None]


def _command(
    tool: CommandWord, cwd: Path, words: Iterable[CommandWord], env: Environment | None
) -> Ran:
    """Run ``tool`` in ``cwd``, raising CannotCheckError where it is not on the search path."""
    try:
        program = find_executable(tool)
    except RuntimeError as error:
        raise CannotCheckError(str(error)) from error
    ran = _run([program, *words], cwd=cwd, env=env)
    return Ran(ExitStatus(ran.returncode), Output(ran.stdout), Output(ran.stderr))


def _git(cwd: Path, *words: CommandWord, checked: bool = True) -> Ran:
    """Run git in ``cwd``, raising CannotCheckError when ``checked`` and it fails."""
    ran = _command(W("git"), cwd, words, _environment())
    if checked and ran.status != 0:
        message = f"git {' '.join(words[:3])} failed: {ran.err.strip()}"
        raise CannotCheckError(message)
    return ran


def _go(cwd: Path, *words: CommandWord, env: Environment) -> Ran:
    """Run go in ``cwd`` under ``env``, the whole environment."""
    return _command(W("go"), cwd, words, env)


def _go_checked(cwd: Path, *words: CommandWord, env: Environment) -> Ran:
    """Run go as ``_go`` does, raising CannotCheckError when it fails."""
    ran = _go(cwd, *words, env=env)
    if ran.status != 0:
        message = f"go {' '.join(words[:3])} in {cwd} failed: {ran.err.strip()}"
        raise CannotCheckError(message)
    return ran


def _environment(**overrides: EnvValue) -> dict[EnvName, EnvValue]:
    """Return this process's environment, less what a git hook exports, with ``overrides`` set.

    A pre-push hook runs under git's ``GIT_DIR`` and its siblings, which would
    point every git this module starts, cmd/go's own included, at the
    repository being pushed rather than the scratch one.
    """
    base = {EnvName(name): EnvValue(value) for name, value in git_clean_env().items()}
    return base | {EnvName(name): value for name, value in overrides.items()}


def _go_env(name: EnvName) -> EnvValue:
    """Return what ``go env`` gives the variable ``name``."""
    return EnvValue(_go_checked(REPO_ROOT, W("env"), W(name), env=_environment()).out.strip())


def worktree_reader(root: Path) -> Reader:
    """Read a repo-relative file from the work tree, None where it is absent."""

    def read(rel: RelPath) -> FileText | None:
        path = root / rel
        return FileText(path.read_text(encoding="utf-8")) if path.is_file() else None

    return read


def commit_reader(root: Path, commit: CommitId) -> Reader:
    """Read a repo-relative file as ``commit`` holds it, None where it holds none."""

    def read(rel: RelPath) -> FileText | None:
        shown = _git(root, W("show"), W(f"{commit}:{rel}"), checked=False)
        return FileText(shown.out) if shown.status == 0 else None

    return read


def commit_of(root: Path, revision: Revision) -> CommitId:
    """Return the commit ``revision`` names, an annotated tag peeled to its commit."""
    peeled = W(f"{revision}^{{commit}}")
    ran = _git(root, W("rev-parse"), W("--verify"), W("--quiet"), peeled, checked=False)
    if ran.status != 0:
        message = f"{revision} names no commit"
        raise CannotCheckError(message)
    return CommitId(ran.out.strip())


def without_major(path: GoModule) -> GoModule:
    """Return ``path`` without its major suffix, ``/vN``."""
    return GoModule(_MAJOR_SUFFIX.sub("", path))


def with_major(path: GoModule, major: Major) -> GoModule:
    """Return ``path`` carrying ``major`` as Go spells it: ``/vN`` from 2 on, nothing below."""
    base = without_major(path)
    return GoModule(f"{base}/v{major}" if major >= _FIRST_SUFFIXED else base)


def read_release(read: Reader) -> Release:
    """Read the workspace's modules and the cabal version, raising CannotCheckError if unread."""
    work, cabal = read(GO_WORK), read(CABAL)
    if work is None or cabal is None:
        message = f"{GO_WORK if work is None else CABAL} is unreadable"
        raise CannotCheckError(message)
    stated = _CABAL_VERSION.search(cabal)
    if stated is None:
        message = f"{CABAL} states no version X.Y.Z.0"
        raise CannotCheckError(message)
    modules: list[Module] = []
    try:
        for use in go_uses(ManifestText(work), Prose(GO_WORK)):
            directory = RelPath(posixpath.normpath(posixpath.join("go", use)))
            manifest = RelPath(f"{directory}/go.mod")
            text = read(manifest)
            if text is None:
                message = f"{manifest} is unreadable"
                raise CannotCheckError(message)
            context = Prose(manifest)
            path = go_module(ManifestText(text), context)
            modules.append(Module(path, directory, go_requires(ManifestText(text), context)))
    except ManifestError as error:
        raise CannotCheckError(str(error)) from error
    return Release(ReleaseVersion(stated[1]), modules, _repository(modules))


def _repository(modules: Sequence[Module]) -> RepositoryPath:
    """Return the import path of the repository's root, which every module path extends."""
    roots: set[RepositoryPath] = set()
    for module in modules:
        base = _MAJOR_SUFFIX.sub("", module.path)
        if not base.endswith(f"/{module.directory}"):
            message = f"the module path {module.path} does not end in {module.directory}"
            raise CannotCheckError(message)
        roots.add(RepositoryPath(base.removesuffix(f"/{module.directory}")))
    if len(roots) != 1:
        message = f"the workspace's modules name {len(roots)} repositories, not one"
        raise CannotCheckError(message)
    return roots.pop()


def released(release: Release) -> list[Module]:
    """Return the modules another module of the workspace requires, whatever their major."""
    required = {
        without_major(requirement.module)
        for module in release.modules
        for requirement in module.requires
    }
    return [module for module in release.modules if without_major(module.path) in required]


def dependency_order(release: Release) -> list[Module]:
    """Return the workspace's modules, each after every module of the workspace it requires."""
    by_base = {without_major(module.path): module for module in release.modules}
    graph = {
        module.directory: {
            by_base[without_major(r.module)].directory
            for r in module.requires
            if without_major(r.module) in by_base
        }
        for module in release.modules
    }
    by_directory = {module.directory: module for module in release.modules}
    return [by_directory[directory] for directory in TopologicalSorter(graph).static_order()]


def tag_for(module: Module, version: GoVersion) -> TagName:
    """Return the tag Go fetches ``module`` at ``version`` by: its directory, then the version."""
    return TagName(f"{module.directory}/{version}")


def escaped(path: GoModule) -> EscapedPath:
    """Return ``path`` as the module cache spells it: each capital as ``!`` and its lower case."""
    return EscapedPath(re.sub(r"[A-Z]", lambda capital: "!" + capital[0].lower(), path))


def recorded(read: Reader, release: Release, path: GoModule) -> dict[RelPath, Hashes]:
    """Return, by go.sum, the hashes each module requiring ``path`` at the release records."""
    version = release.tag_version
    found: dict[RelPath, Hashes] = {}
    for module in release.modules:
        if not any(r.module == path and r.version == version for r in module.requires):
            continue
        sums = RelPath(f"{module.directory}/go.sum")
        rows = [line.split() for line in (read(sums) or "").splitlines()]
        rows = [row for row in rows if len(row) == _SUM_FIELDS and row[0] == path]
        zips = [row[2] for row in rows if row[1] == version]
        mods = [row[2] for row in rows if row[1] == f"{version}/go.mod"]
        found[sums] = Hashes(
            ModuleHash(zips[0]) if len(zips) == 1 else None,
            ModuleHash(mods[0]) if len(mods) == 1 else None,
        )
    return found


def differences(
    found: Hashes | Prose, records: Mapping[RelPath, Hashes], path: GoModule, version: GoVersion
) -> list[Prose]:
    """Return each go.sum whose hashes of ``path`` differ from ``found``, or why none was found."""
    if not isinstance(found, Hashes):
        return [found]
    return [
        Prose(
            f"{sums} records {path}@{version} as {hashes.zip or 'nothing'} (go.mod "
            + f"{hashes.mod or 'nothing'}), where it hashes to {found.zip} (go.mod {found.mod})"
        )
        for sums, hashes in records.items()
        if hashes != found
    ]


def tree_repository(root: Path, dest: Path, tags: Iterable[TagName]) -> None:
    """Commit the work tree's go/ and root files to a new repository and tag it.

    The files are those the next commit of the work tree holds: tracked, or
    untracked and not ignored, as a go.sum ``write`` creates is until it is
    committed; a tracked file the work tree deleted is left out.
    """
    words = (W("ls-files"), W("-z"), W("--cached"), W("--others"), W("--exclude-standard"))
    listed = _git(root, *words, W("--"), W("go"), W(":(glob)*")).out
    for rel in dict.fromkeys(filter(None, listed.split("\0"))):
        source, target = root / rel, dest / rel
        if not source.is_symlink() and not source.is_file():
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        if source.is_symlink():
            target.symlink_to(source.readlink())
        else:
            _ = shutil.copyfile(source, target)
    _ = _git(dest, *_SCRATCH_GIT, W("init"), W("--quiet"))
    _ = _git(dest, *_SCRATCH_GIT, W("add"), W("--all"), W("--force"))
    _ = _git(dest, *_SCRATCH_GIT, W("commit"), W("--quiet"), W("--message"), W("the tree"))
    for tag in tags:
        _ = _git(dest, *_SCRATCH_GIT, W("tag"), W(tag))


def commit_repository(root: Path, dest: Path, commit: CommitId, tags: Iterable[TagName]) -> None:
    """Make a bare repository reading the root's objects, with ``tags`` naming ``commit``."""
    common = _git(root, W("rev-parse"), W("--path-format=absolute"), W("--git-common-dir")).out
    _ = _git(root, W("init"), W("--quiet"), W("--bare"), W(str(dest)))
    alternates = dest / "objects" / "info" / "alternates"
    _ = alternates.write_text(f"{common.strip()}/objects\n", encoding="utf-8")
    for tag in tags:
        _ = _git(dest, W("update-ref"), W(f"refs/tags/{tag}"), W(commit))


def served_environment(
    repository: Path, cache: Path, release: Release, *, proxy: EnvValue, flags: EnvValue
) -> dict[EnvName, EnvValue]:
    """Return go's environment fetching this repository from ``repository`` into ``cache``."""
    return _environment(
        GOWORK=EnvValue("off"),
        GOFLAGS=flags,
        GOPRIVATE=EnvValue(release.repository),
        GOMODCACHE=EnvValue(str(cache)),
        GOPROXY=proxy,
        GIT_TERMINAL_PROMPT=EnvValue("0"),
        GIT_CONFIG_COUNT=EnvValue("2"),
        GIT_CONFIG_KEY_0=EnvValue(f"url.file://{repository}.insteadOf"),
        GIT_CONFIG_VALUE_0=EnvValue(f"https://{release.repository}"),
        GIT_CONFIG_KEY_1=EnvValue("protocol.file.allow"),
        GIT_CONFIG_VALUE_1=EnvValue("always"),
    )


def fetch(cwd: Path, path: GoModule, query: GoVersion, env: Environment) -> Fetched | Prose:
    """Return the version and hashes go resolves ``path`` at ``query`` to, or why it could not."""
    ran = _go(cwd, W("mod"), W("download"), W("-json"), W(f"{path}@{query}"), env=env)
    try:
        answer = cast("_Downloaded", json.loads(ran.out))
    except json.JSONDecodeError:
        return Prose(f"go mod download {path}@{query}: {ran.err.strip()}")
    if "Error" in answer or "Version" not in answer or "Sum" not in answer:
        return Prose(f"go mod download {path}@{query}: {answer.get('Error', ran.err.strip())}")
    if "GoModSum" not in answer:
        return Prose(f"go mod download {path}@{query}: {answer.get('Error', ran.err.strip())}")
    return Fetched(answer["Version"], Hashes(answer["Sum"], answer["GoModSum"]))


def download(cwd: Path, path: GoModule, version: GoVersion, env: Environment) -> Hashes | Prose:
    """Return the hashes go computes fetching ``path`` at ``version``, or why it could not."""
    fetched = fetch(cwd, path, version, env)
    return fetched.hashes if isinstance(fetched, Fetched) else fetched


def served_hashes(
    repository: Path, cache: Path, release: Release, path: GoModule
) -> Hashes | Prose:
    """Return the hashes of ``path`` at the release's version, fetched from ``repository``."""
    env = served_environment(
        repository, cache, release, proxy=EnvValue("off"), flags=EnvValue("-modcacherw")
    )
    cache.mkdir(parents=True, exist_ok=True)
    return download(cache, path, release.tag_version, env)


def copy_download(source: Path, dest: Path, path: GoModule, version: GoVersion) -> None:
    """Copy one version's download entries, and nothing of the clone that fetched them."""
    relative = Path("cache", "download", escaped(path), "@v")
    (dest / relative).mkdir(parents=True, exist_ok=True)
    for suffix in (".info", ".mod", ".zip", ".ziphash"):
        name = f"{version}{suffix}"
        _ = shutil.copyfile(source / relative / name, dest / relative / name)


def _proxy_over_cache() -> EnvValue:
    """Return go's proxy list with the user's module cache read first, as a file proxy."""
    cache, proxy = _go_env(EnvName("GOMODCACHE")), _go_env(EnvName("GOPROXY"))
    return EnvValue(f"file://{cache}/cache/download,{proxy}")


def check(root: Path) -> ExitStatus:
    """Build every module outside the workspace, serving the release's versions the tree holds."""
    read = worktree_reader(root)
    release = read_release(read)
    prepared = [module for module in released(release) if recorded(read, release, module.path)]
    unserved: list[Prose] = []
    with tempfile.TemporaryDirectory(prefix="aletheia-go-release-") as name:
        scratch = Path(name)
        env = _environment(GOWORK=EnvValue("off"), GOPRIVATE=EnvValue(release.repository))
        if prepared:
            unserved = _serve(root, read, release, prepared, scratch)
            env |= {
                EnvName("GOMODCACHE"): EnvValue(str(scratch / "build")),
                EnvName("GOFLAGS"): EnvValue("-modcacherw"),
                EnvName("GOPROXY"): _proxy_over_cache(),
            }
        failed = [module for module in release.modules if not _builds(root, module, env)]
    for line in unserved:
        emit(f"go_release: not served from the tree: {line}")
    if not failed:
        emit("go_release: every module builds outside the workspace, as a consumer resolves it")
        return ExitStatus(0)
    if unserved:
        emit(
            "go_release: a requirement at the release's version resolves from GitHub where the"
            + " tree no longer hashes as its go.sum lines record: run `python -m tools.go_release"
            + " write` to record the tree, or tag the release whose hashes they are"
        )
    return ExitStatus(1)


def _serve(
    root: Path, read: Reader, release: Release, prepared: Sequence[Module], scratch: Path
) -> list[Prose]:
    """Fill ``scratch/build`` with each prepared module the tree hashes as recorded.

    Returns:
        Why each other prepared module is not served: the hashes that differ.

    """
    version = release.tag_version
    repository = scratch / "tree"
    tree_repository(root, repository, [tag_for(m, version) for m in released(release)])
    unserved: list[Prose] = []
    for index, module in enumerate(prepared):
        hashing = scratch / f"hash-{index}"
        found = served_hashes(repository, hashing, release, module.path)
        differ = differences(found, recorded(read, release, module.path), module.path, version)
        if differ:
            unserved.extend(differ)
            continue
        copy_download(hashing, scratch / "build", module.path, version)
        emit(f"go_release: {module.path}@{version} served from the tree, as its tag will be")
    return unserved


def _builds(root: Path, module: Module, env: Environment) -> bool:
    """Say whether ``module`` builds under ``env`` with its go.mod and go.sum as they are."""
    words = (W("build"), W("-mod=readonly"), W("-o"), W(os.devnull), W("./..."))
    ran = _go(root / module.directory, *words, env=env)
    if ran.status != 0:
        tail = " | ".join((ran.out + ran.err).strip().splitlines()[-3:])
        emit(f"go_release: {module.directory} does not build outside the workspace: {tail}")
    return ran.status == 0


def write(root: Path) -> ExitStatus:
    """Point every requirement on a released module at the release, and record its hashes."""
    read = worktree_reader(root)
    release = read_release(read)
    version = release.tag_version
    shipped = {without_major(module.path): module for module in released(release)}
    major = Major(int(release.version.split(".")[0]))
    unmoved = [m.path for m in shipped.values() if with_major(m.path, major) != m.path]
    if unmoved:
        emit(
            f"go_release: {', '.join(unmoved)} carries no major {major}, the release's: run"
            + " `python -m tools.go_release move-major` first"
        )
        return ExitStatus(1)
    for module in release.modules:
        manifest = root / module.directory / "go.mod"
        text = FileText(manifest.read_text(encoding="utf-8"))
        pinned = pinned_requirements(text, list(shipped.values()), version)
        if pinned != text:
            _ = manifest.write_text(pinned, encoding="utf-8")
    _replace_in_workspace(root, list(shipped.values()), version, _environment())
    _tidy_in_order(root, read_release(read))
    return ExitStatus(0)


def _tidy_in_order(root: Path, release: Release) -> None:
    """Tidy each module requiring a released one against the tree, required modules first.

    The tree is exported again for each, since a module's zip holds its go.sum
    and the one tidied before it may have written that go.sum.
    """
    version = release.tag_version
    shipped = {without_major(module.path) for module in released(release)}
    tags = [tag_for(module, version) for module in released(release)]
    proxy = _proxy_over_cache()
    for module in dependency_order(release):
        if not any(without_major(r.module) in shipped for r in module.requires):
            continue
        with tempfile.TemporaryDirectory(prefix="aletheia-go-release-") as name:
            scratch = Path(name)
            tree_repository(root, scratch / "tree", tags)
            flags = EnvValue("-mod=mod -modcacherw")
            env = served_environment(
                scratch / "tree", scratch / "cache", release, proxy=proxy, flags=flags
            )
            _ = _go_checked(root / module.directory, W("mod"), W("tidy"), env=env)
        emit(f"go_release: {module.directory} requires the release's modules at {version}")


def pinned_requirements(text: FileText, shipped: Sequence[Module], version: GoVersion) -> FileText:
    """Return the go.mod ``text`` requiring every released module at ``version``, by its path.

    The entries are rewritten as text: after a major move a requirement's old
    version is no version of its new path, and go refuses to parse the file.  A
    requirement spelled at another major of a released module moves to its path.
    """
    for module in shipped:
        base = re.escape(without_major(module.path))
        entry = re.compile(
            rf"^([ \t]*(?:require[ \t]+)?){base}(?:/v[0-9]+)?([ \t]+)v\S+", re.MULTILINE
        )
        text = FileText(
            entry.sub(lambda found, path=module.path: f"{found[1]}{path}{found[2]}{version}", text)
        )
    return text


def _replace_in_workspace(
    root: Path, shipped: Sequence[Module], version: GoVersion, env: Environment
) -> None:
    """Make go.work replace each released module at ``version`` by its directory, and no other."""
    work = W(str(root / GO_WORK))
    answer = _go_checked(root / "go", W("work"), W("edit"), W("-json"), work, env=env)
    bases = {without_major(module.path) for module in shipped}
    edits: list[CommandWord] = []
    for replace in cast("_Workspace", json.loads(answer.out)).get("Replace") or []:
        old = replace["Old"]
        if without_major(old["Path"]) in bases:
            at = f"@{old['Version']}" if "Version" in old else ""
            edits.append(W(f"-dropreplace={old['Path']}{at}"))
    for module in shipped:
        relative = posixpath.relpath(module.directory, "go")
        directory = "./" if relative == "." else f"./{relative}"
        edits.append(W(f"-replace={module.path}@{version}={directory}"))
    _ = _go_checked(root / "go", W("work"), W("edit"), *edits, work, env=env)


def move_major(root: Path) -> ExitStatus:
    """Move every tracked spelling of each released module's path to the release's major."""
    release = read_release(worktree_reader(root))
    major = Major(int(release.version.split(".")[0]))
    paths = [module.path for module in release.modules]
    moving = [
        (module.path, with_major(module.path, major))
        for module in released(release)
        if with_major(module.path, major) != module.path
    ]
    moves = [
        (re.compile(re.escape(old) + f"(?!{'|'.join(_stops(old, paths))})"), new)
        for old, new in moving
    ]
    for old, new in moving:
        emit(f"go_release: {old} moves to {new}")
    if not moves:
        emit(f"go_release: every released module's path already carries major {major}")
        return ExitStatus(0)
    changed = 0
    for rel in filter(None, _git(root, W("ls-files"), W("-z")).out.split("\0")):
        path = root / rel
        if _UNMOVED.match(rel) or path.is_symlink() or not path.is_file():
            continue
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            continue
        moved = text
        for pattern, new in moves:
            moved = pattern.sub(lambda _spelled, new=new: new, moved)
        if moved != text:
            _ = path.write_bytes(moved.encode("utf-8"))
            changed += 1
    emit(f"go_release: {changed} tracked files moved")
    return ExitStatus(0)


def _stops(old: GoModule, paths: Iterable[GoModule]) -> list[Prose]:
    """Return what, after a spelling of ``old``, makes it another path than the module's own."""
    inner = [path.removeprefix(old) for path in paths if path.startswith(f"{old}/")]
    return [
        Prose(_PATH_GOES_ON),
        Prose(r"/v[0-9]"),
        *(Prose(re.escape(rest) + f"(?!{_PATH_GOES_ON})") for rest in inner),
    ]


def check_commit(root: Path, commit: CommitId, expected: ReleaseVersion | None) -> list[Prose]:
    """Return how ``commit`` falls short of holding every released module's recorded hashes."""
    read = commit_reader(root, commit)
    release = read_release(read)
    version = release.tag_version
    found: list[Prose] = []
    if expected is not None and release.version != expected:
        found.append(Prose(f"{commit:.12} prepares {release.version}, not {expected}"))
    shipped = released(release)
    with tempfile.TemporaryDirectory(prefix="aletheia-go-release-") as name:
        scratch = Path(name)
        repository = scratch / "repository.git"
        commit_repository(root, repository, commit, [tag_for(m, version) for m in shipped])
        for index, module in enumerate(shipped):
            records = recorded(read, release, module.path)
            if not records:
                found.append(
                    Prose(
                        f"{commit:.12}: no module requires {module.path} at {version}, so no"
                        + " go.sum records what its tag publishes: run `python -m tools.go_release"
                        + " write`"
                    )
                )
                continue
            hashes = served_hashes(repository, scratch / f"hash-{index}", release, module.path)
            found.extend(differences(hashes, records, module.path, version))
    return found


def check_tags(root: Path, lines: Iterable[RefLine]) -> list[Prose]:
    """Return how the release tags git is pushing fall short, read from its pre-push ref lines."""
    commits: dict[ReleaseVersion, set[CommitId]] = {}
    go_tags: dict[ReleaseVersion, list[GoTag]] = {}
    found: list[Prose] = []
    for line in lines:
        fields = line.split()
        if len(fields) != _REF_FIELDS or _NO_OBJECT.match(fields[1]):
            continue
        if not fields[2].startswith("refs/tags/"):
            continue
        name = fields[2].removeprefix("refs/tags/")
        matched = _RELEASE_TAG.match(name)
        if matched is None:
            if name.startswith("go/"):
                found.append(Prose(f"{name}: a go/ tag that is no <directory>/vX.Y.Z"))
            continue
        version = ReleaseVersion(matched["version"])
        commits.setdefault(version, set()).add(commit_of(root, Revision(fields[1])))
        if matched["directory"] is not None:
            go_tags.setdefault(version, []).append(
                GoTag(TagName(name), RelPath(matched["directory"]))
            )
    for version, named in sorted(commits.items()):
        if len(named) != 1:
            listed = ", ".join(sorted(f"{commit:.12}" for commit in named))
            found.append(Prose(f"release {version}'s tags name {len(named)} commits: {listed}"))
            continue
        commit = next(iter(named))
        shipped = {m.directory for m in released(read_release(commit_reader(root, commit)))}
        found.extend(
            Prose(f"{tag.name}: {tag.directory} is no released module at {commit:.12}")
            for tag in go_tags.get(version, [])
            if tag.directory not in shipped
        )
        found.extend(check_commit(root, commit, version))
    return found


def github_environment(cache: Path, release: Release) -> dict[EnvName, EnvValue]:
    """Return go's environment fetching this repository from GitHub alone, into ``cache``.

    ``GOPRIVATE`` sends the repository's modules straight to its git host and
    keeps them out of the checksum database; ``GOPROXY=off`` leaves go no proxy
    for anything else.
    """
    return _environment(
        GOWORK=EnvValue("off"),
        GOFLAGS=EnvValue("-modcacherw"),
        GOMODCACHE=EnvValue(str(cache)),
        GOPRIVATE=EnvValue(release.repository),
        GOPROXY=EnvValue("off"),
    )


def check_published(root: Path, version: ReleaseVersion) -> list[Prose]:
    """Return how the released modules GitHub serves at ``version`` differ from the tag's."""
    commit = commit_of(root, Revision(f"v{version}"))
    read = commit_reader(root, commit)
    release = read_release(read)
    found: list[Prose] = []
    if release.version != version:
        found.append(Prose(f"v{version} names {commit:.12}, which prepares {release.version}"))
    with tempfile.TemporaryDirectory(prefix="aletheia-go-release-") as name:
        cache = Path(name)
        env = github_environment(cache, release)
        for module in released(release):
            records = recorded(read, release, module.path)
            if not records:
                found.append(Prose(f"v{version}: no go.sum records {module.path}"))
                continue
            hashes = download(cache, module.path, release.tag_version, env)
            found.extend(differences(hashes, records, module.path, release.tag_version))
    return found


def _is_version(version: ReleaseVersion) -> bool:
    """Say whether ``version`` is a release version, ``X.Y.Z``."""
    return re.fullmatch(VERSION_PATTERN, version) is not None


def _report(found: Sequence[Prose], what: Prose) -> ExitStatus:
    """Print each finding, or that ``what`` holds; return the matching status."""
    for line in found:
        emit(f"go_release: {line}")
    if found:
        return ExitStatus(1)
    emit(f"go_release: {what}")
    return ExitStatus(0)


def rehearsal_findings(
    path: GoModule, github: Fetched | Prose, local: Hashes | Prose
) -> list[Prose]:
    """Return how GitHub's answer for a commit differs from the commit's own hashes."""
    if not isinstance(github, Fetched):
        return [github]
    if not isinstance(local, Hashes):
        return [local]
    if github.hashes == local:
        return []
    return [
        Prose(
            f"GitHub serves {path}@{github.version} as {github.hashes.zip} (go.mod "
            + f"{github.hashes.mod}), where the commit's objects hash to {local.zip} (go.mod "
            + f"{local.mod})"
        )
    ]


def rehearsal_repository(root: Path, dest: Path, commit: CommitId) -> None:
    """Make a bare repository reading the root's objects, a branch on ``commit``, the root's tags.

    The tags are there because go names a commit after a tag by a
    pseudo-version based on that tag, and resolves it only where the tag is.
    """
    commit_repository(root, dest, commit, [])
    _ = _git(dest, W("update-ref"), W("refs/heads/rehearsed"), W(commit))
    tags = _git(root, W("for-each-ref"), W("--format=%(objectname) %(refname)"), W("refs/tags"))
    for line in tags.out.splitlines():
        target, ref = line.split(" ", 1)
        _ = _git(dest, W("update-ref"), W(ref), W(target))


class Rehearsal(NamedTuple):
    """Where a commit is rehearsed: the scratch directory, the repository reading its objects."""

    scratch: Path
    repository: Path
    release: Release
    commit: CommitId
    github: Environment


def _rehearse(at: Rehearsal, path: GoModule, cache: Path) -> list[Prose]:
    """Fetch ``path`` at the commit from GitHub and from the commit's own objects."""
    served = fetch(at.scratch, path, GoVersion(at.commit), at.github)
    local: Hashes | Prose = Prose("GitHub gave no version to compare")
    if isinstance(served, Fetched):
        cache.mkdir()
        env = served_environment(
            at.repository, cache, at.release, proxy=EnvValue("off"), flags=EnvValue("-modcacherw")
        )
        local = download(cache, path, served.version, env)
    found = rehearsal_findings(path, served, local)
    if not found and isinstance(served, Fetched):
        emit(f"go_release: GitHub serves {path}@{served.version} as hashed")
    return found


def check_publishable(root: Path, commit: CommitId) -> list[Prose]:
    """Return how ``commit`` falls short of what the tag-time checks will ask, before any tag."""
    read = commit_reader(root, commit)
    release = read_release(read)
    shipped = released(release)
    found: list[Prose] = []
    if any(recorded(read, release, module.path) for module in shipped):
        found.extend(check_commit(root, commit, None))
    else:
        emit(
            f"go_release: {commit:.12} prepares no release of the Go modules, so no hash it records"
        )
    with tempfile.TemporaryDirectory(prefix="aletheia-go-release-") as name:
        scratch = Path(name)
        github = github_environment(scratch / "github", release)
        repository = scratch / "repository.git"
        rehearsal_repository(root, repository, commit)
        at = Rehearsal(scratch, repository, release, commit, github)
        for index, module in enumerate(shipped):
            found.extend(_rehearse(at, module.path, scratch / f"local-{index}"))
    return found


def _check_commit(root: Path, revision: Revision) -> ExitStatus:
    """Report ``check_commit`` on the commit ``revision`` names."""
    commit = commit_of(root, revision)
    held = Prose(f"{commit:.12} holds every released module's recorded hashes")
    return _report(check_commit(root, commit, None), held)


def main(argv: list[CommandWord] | None = None) -> ExitStatus:
    """Run the command ``argv`` names."""
    parser = argparse.ArgumentParser(description=HelpText(__doc__ or ""))
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("move-major", "write", "check", "check-tags"):
        _ = commands.add_parser(name)
    _ = commands.add_parser("check-commit").add_argument("revision", type=Revision)
    _ = commands.add_parser("check-publishable").add_argument("revision", type=Revision)
    _ = commands.add_parser("check-published").add_argument("version", type=ReleaseVersion)
    arguments = parser.parse_args(argv)
    if arguments.command == "check-published" and not _is_version(arguments.version):
        parser.error(f"not a release version X.Y.Z: {arguments.version!r}")
    root = REPO_ROOT
    actions: dict[CommandWord, Callable[[], ExitStatus]] = {
        W("move-major"): lambda: move_major(root),
        W("write"): lambda: write(root),
        W("check"): lambda: check(root),
        W("check-commit"): lambda: _check_commit(root, cast("Revision", arguments.revision)),
        W("check-publishable"): lambda: _report(
            check_publishable(root, commit_of(root, cast("Revision", arguments.revision))),
            Prose("the commit holds what the tag-time checks will ask"),
        ),
        W("check-tags"): lambda: _report(
            check_tags(root, [RefLine(line) for line in sys.stdin.read().splitlines()]),
            Prose("every release tag pushed holds its recorded hashes"),
        ),
        W("check-published"): lambda: _report(
            check_published(root, cast("ReleaseVersion", arguments.version)),
            Prose("the published modules hash as the tag records"),
        ),
    }
    try:
        return actions[cast("CommandWord", arguments.command)]()
    except CannotCheckError as error:
        emit(f"go_release: cannot check: {error}")
        return ExitStatus(2)


if __name__ == "__main__":
    sys.exit(reporting(main, Prose("go-release")))
