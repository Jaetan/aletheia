# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Go workspace as tools/go_release.py reads it, and the fetches its checks make.

A revision's workspace is read from ``go/go.work`` and each module's go.mod,
its release version from ``haskell-shim/aletheia.cabal``.  cmd/go fetches a
module from a scratch repository of the tree or of a commit, or from GitHub
directly, each into a module cache of its own; git and go run with a git
hook's variables removed.  Raises CannotCheckError where a tool or a file the
checks read is absent.
"""

from __future__ import annotations

import json
import posixpath
import re
import shutil
from graphlib import TopologicalSorter
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType, NotRequired, TypedDict, cast

from tools._common import (
    CommandWord,
    EnvName,
    EnvValue,
    RelPath,
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
from tools.commit_subjects import VERSION_PATTERN, ReleaseVersion

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
GO_WORK = RelPath("go/go.work")
CABAL = RelPath("haskell-shim/aletheia.cabal")

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
# A remote, by the name or URL git push hands a pre-push hook.
RemoteName = NewType("RemoteName", str)
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
_FIRST_SUFFIXED = Major(2)
_SUM_FIELDS = 3
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


def run_git(cwd: Path, *words: CommandWord, checked: bool = True) -> Ran:
    """Run git in ``cwd``, raising CannotCheckError when ``checked`` and it fails."""
    ran = _command(W("git"), cwd, words, clean_environment())
    if checked and ran.status != 0:
        message = f"git {' '.join(words[:3])} failed: {ran.err.strip()}"
        raise CannotCheckError(message)
    return ran


def run_go(cwd: Path, *words: CommandWord, env: Environment) -> Ran:
    """Run go in ``cwd`` under ``env``, the whole environment."""
    return _command(W("go"), cwd, words, env)


def run_go_checked(cwd: Path, *words: CommandWord, env: Environment) -> Ran:
    """Run go as ``run_go`` does, raising CannotCheckError when it fails."""
    ran = run_go(cwd, *words, env=env)
    if ran.status != 0:
        message = f"go {' '.join(words[:3])} in {cwd} failed: {ran.err.strip()}"
        raise CannotCheckError(message)
    return ran


def clean_environment(**overrides: EnvValue) -> dict[EnvName, EnvValue]:
    """Return this process's environment, less what a git hook exports, with ``overrides`` set.

    A pre-push hook runs under git's ``GIT_DIR`` and its siblings, which would
    point every git this module starts, cmd/go's own included, at the
    repository being pushed rather than the scratch one.
    """
    base = {EnvName(name): EnvValue(value) for name, value in git_clean_env().items()}
    return base | {EnvName(name): value for name, value in overrides.items()}


def go_env(name: EnvName) -> EnvValue:
    """Return what ``go env`` gives the variable ``name``."""
    return EnvValue(
        run_go_checked(REPO_ROOT, W("env"), W(name), env=clean_environment()).out.strip()
    )


def worktree_reader(root: Path) -> Reader:
    """Read a repo-relative file from the work tree, None where it is absent."""

    def read(rel: RelPath) -> FileText | None:
        path = root / rel
        return FileText(path.read_text(encoding="utf-8")) if path.is_file() else None

    return read


def commit_reader(root: Path, commit: CommitId) -> Reader:
    """Read a repo-relative file as ``commit`` holds it, None where it holds none."""

    def read(rel: RelPath) -> FileText | None:
        shown = run_git(root, W("show"), W(f"{commit}:{rel}"), checked=False)
        return FileText(shown.out) if shown.status == 0 else None

    return read


def remote_tags(root: Path, remote: RemoteName) -> dict[TagName, CommitId]:
    """Return the commit each tag on ``remote`` names, an annotated tag peeled to its commit."""
    listed = run_git(root, W("ls-remote"), W("--tags"), W(remote)).out
    named: dict[TagName, CommitId] = {}
    peeled: dict[TagName, CommitId] = {}
    for line in listed.splitlines():
        sha, _, ref = line.partition("\t")
        name = ref.removeprefix("refs/tags/")
        if name.endswith("^{}"):
            peeled[TagName(name.removesuffix("^{}"))] = CommitId(sha)
        else:
            named[TagName(name)] = CommitId(sha)
    return named | peeled


def commit_of(root: Path, revision: Revision) -> CommitId:
    """Return the commit ``revision`` names, an annotated tag peeled to its commit."""
    peeled = W(f"{revision}^{{commit}}")
    ran = run_git(root, W("rev-parse"), W("--verify"), W("--quiet"), peeled, checked=False)
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
    """Return the modules a release tags: every module of the workspace."""
    return list(release.modules)


def required(release: Release) -> list[Module]:
    """Return the modules another module of the workspace requires: each go.sum records theirs."""
    wanted = {
        without_major(requirement.module)
        for module in release.modules
        for requirement in module.requires
    }
    return [module for module in release.modules if without_major(module.path) in wanted]


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
    listed = run_git(root, *words, W("--"), W("go"), W(":(glob)*")).out
    for rel in dict.fromkeys(filter(None, listed.split("\0"))):
        source, target = root / rel, dest / rel
        if not source.is_symlink() and not source.is_file():
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        if source.is_symlink():
            target.symlink_to(source.readlink())
        else:
            _ = shutil.copyfile(source, target)
    _ = run_git(dest, *_SCRATCH_GIT, W("init"), W("--quiet"))
    _ = run_git(dest, *_SCRATCH_GIT, W("add"), W("--all"), W("--force"))
    _ = run_git(dest, *_SCRATCH_GIT, W("commit"), W("--quiet"), W("--message"), W("the tree"))
    for tag in tags:
        _ = run_git(dest, *_SCRATCH_GIT, W("tag"), W(tag))


def commit_repository(root: Path, dest: Path, commit: CommitId, tags: Iterable[TagName]) -> None:
    """Make a bare repository reading the root's objects, with ``tags`` naming ``commit``."""
    common = run_git(root, W("rev-parse"), W("--path-format=absolute"), W("--git-common-dir")).out
    _ = run_git(root, W("init"), W("--quiet"), W("--bare"), W(str(dest)))
    alternates = dest / "objects" / "info" / "alternates"
    _ = alternates.write_text(f"{common.strip()}/objects\n", encoding="utf-8")
    for tag in tags:
        _ = run_git(dest, W("update-ref"), W(f"refs/tags/{tag}"), W(commit))


def served_environment(
    repository: Path, cache: Path, release: Release, *, proxy: EnvValue, flags: EnvValue
) -> dict[EnvName, EnvValue]:
    """Return go's environment fetching this repository from ``repository`` into ``cache``."""
    return clean_environment(
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
    ran = run_go(cwd, W("mod"), W("download"), W("-json"), W(f"{path}@{query}"), env=env)
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


def proxy_over_cache() -> EnvValue:
    """Return go's proxy list with the user's module cache read first, as a file proxy."""
    cache, proxy = go_env(EnvName("GOMODCACHE")), go_env(EnvName("GOPROXY"))
    return EnvValue(f"file://{cache}/cache/download,{proxy}")


def offline_proxy(first: Path) -> EnvValue:
    """Return go's proxies as the module cache ``first``, then the user's, and no other."""
    user = go_env(EnvName("GOMODCACHE"))
    return EnvValue(f"file://{first}/cache/download,file://{user}/cache/download,off")


def github_environment(cache: Path, release: Release) -> dict[EnvName, EnvValue]:
    """Return go's environment fetching this repository from GitHub alone, into ``cache``.

    ``GOPRIVATE`` sends the repository's modules straight to its git host and
    keeps them out of the checksum database; ``GOPROXY=off`` leaves go no proxy
    for anything else.
    """
    return clean_environment(
        GOWORK=EnvValue("off"),
        GOFLAGS=EnvValue("-modcacherw"),
        GOMODCACHE=EnvValue(str(cache)),
        GOPRIVATE=EnvValue(release.repository),
        GOPROXY=EnvValue("off"),
    )
