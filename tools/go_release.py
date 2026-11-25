# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Release the Go modules: move their majors, record their hashes, hold every tag to them.

Every module of the Go workspace is released with the repository: its path
carries the release's major (``/vN`` from 2 on), and the release tags it
``<directory>/vX.Y.Z`` beside ``vX.Y.Z``, the directory being the module's
(``go``, ``go/excel``, ``go/cmd/aletheia``).  The release's version is the one
``haskell-shim/aletheia.cabal`` states as ``X.Y.Z.0``.

Go records a module only by the hash of its contents, the ``h1:`` lines of each
requiring module's ``go.sum``, and Go's public checksum database keeps the first
hash it sees for a version, so the hash of every module another requires is
computed from the tree before any tag exists, by cmd/go itself; a command, which
no module requires and no go.sum records, is installed from the tree instead,
and its published copy held to the tagged commit's own objects.  The tree is
committed to a scratch repository and tagged there, and cmd/go fetches it
through git's ``insteadOf`` into a module cache of its own, never the user's.
cmd/go keys its clone by GitHub's URL and reads that clone's tags before the
remote's, so a cache that fetched from the scratch repository never resolves
anything from GitHub: the build cache, where a version the tree does not serve
resolves from GitHub, receives the served versions' download entries alone.

Commands:

* ``move-major``: every tracked spelling of a released module's path moves to
  the release's major; ``CHANGELOG.md``, ``.archive/``, each ``go.sum`` and
  ``go/go.work`` are left to their own rules.
* ``write``: every requirement on a module of the workspace names the
  release's version, ``go/go.work`` replaces that version by the tree, and each
  module requiring another is tidied against the tree served at that version,
  required modules first.  A second run changes nothing.
* ``check``: each module builds outside the workspace as a consumer resolves
  it.  A requirement at the release's version is served from the tree where the
  tree's hashes equal every ``go.sum`` line recording them, and otherwise
  resolves from GitHub, which holds it once the release is tagged.  Once every
  such requirement is served, ``go install`` takes each command at the release's
  version from the tree, as a consumer's install does.
* ``check-commit REV``: the commit holds, for each required module at the
  version its cabal file states, the hashes every requiring ``go.sum`` records,
  and go fetches each command at its tag.
* ``check-tags REMOTE``: reads the ref lines git hands a pre-push hook on
  stdin.  A release goes out in two pushes, since GitHub creates no event for
  tags when more than three are pushed at once: every released module's
  ``go/`` tag together, then ``vX.Y.Z`` alone, once REMOTE holds every ``go/``
  tag on its commit.  The tags of one version name one commit, each ``go/`` tag
  a released module's directory, and that commit passes ``check-commit``.
* ``check-published X.Y.Z``: the released modules at ``vX.Y.Z``, fetched from
  GitHub, carry the hashes the tagged commit records, a command the hashes of
  the tagged commit's own objects.  The commit is the one the release's tags
  here name, its ``go/`` tags' before ``vX.Y.Z`` exists.
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
import sys
import tempfile
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NotRequired, TypedDict, cast

from tools._common import (
    CommandWord,
    EnvName,
    EnvValue,
    HelpText,
    RelPath,
    emit,
)
from tools._go_modules import (
    GO_WORK,
    REPO_ROOT,
    CannotCheckError,
    CommitId,
    Environment,
    Fetched,
    FileText,
    Hashes,
    Major,
    Module,
    Reader,
    RefLine,
    Release,
    RemoteName,
    Revision,
    TagName,
    W,
    clean_environment,
    commit_of,
    commit_reader,
    commit_repository,
    copy_download,
    dependency_order,
    differences,
    download,
    fetch,
    github_environment,
    proxy_over_cache,
    read_release,
    recorded,
    released,
    remote_tags,
    required,
    run_git,
    run_go,
    run_go_checked,
    served_environment,
    served_hashes,
    tag_for,
    tree_repository,
    with_major,
    without_major,
    worktree_reader,
)
from tools._manifests import (
    GoModule,
    GoVersion,
)
from tools._progress import reporting
from tools.commit_subjects import VERSION_PATTERN, ReleaseVersion

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Sequence

# The files the major move leaves alone: history, hashes, and the workspace's
# replaces, which ``write`` rewrites.
_UNMOVED = re.compile(r"^(?:CHANGELOG\.md|\.archive/.*|.*go\.sum|go/go\.work)$")

_RELEASE_TAG = re.compile(rf"^(?:(?P<directory>go(?:/[^/]+)*)/)?v(?P<version>{VERSION_PATTERN})$")
# What makes a module path's spelling go on: a character a path element holds, or a
# dot before one; a dot before anything else ends a sentence, not the path.
_PATH_GOES_ON = r"[A-Za-z0-9_~\-]|\.[A-Za-z0-9_~\-]"
_REF_FIELDS = 4
_NO_OBJECT = re.compile(r"^0+$")


class _Pushed(NamedTuple):
    """A release tag being pushed: its name, the module directory a go/ tag names, its commit."""

    name: TagName
    directory: RelPath | None
    commit: CommitId


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


def check(root: Path) -> ExitStatus:
    """Build every module outside the workspace, serving the release's versions the tree holds."""
    read = worktree_reader(root)
    release = read_release(read)
    prepared = [module for module in required(release) if recorded(read, release, module.path)]
    unserved: list[Prose] = []
    with tempfile.TemporaryDirectory(prefix="aletheia-go-release-") as name:
        scratch = Path(name)
        env = clean_environment(GOWORK=EnvValue("off"), GOPRIVATE=EnvValue(release.repository))
        if prepared:
            unserved = _serve(root, read, release, prepared, scratch)
            env |= {
                EnvName("GOMODCACHE"): EnvValue(str(scratch / "build")),
                EnvName("GOFLAGS"): EnvValue("-modcacherw"),
                EnvName("GOPROXY"): proxy_over_cache(),
            }
        failed = [module for module in release.modules if not _builds(root, module, env)]
        if prepared and not unserved:
            failed += [m for m in _commands(release) if not _installs(root, release, m, scratch)]
    for line in unserved:
        emit(f"go_release: not served from the tree: {line}")
    if not failed:
        emit("go_release: every module builds outside the workspace, as a consumer resolves it")
        if prepared and not unserved:
            emit("go_release: each command installs at the release's version, as a consumer's does")
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


def _commands(release: Release) -> list[Module]:
    """Return the released modules no module requires: commands, installed rather than required."""
    hashed = {module.directory for module in required(release)}
    return [module for module in released(release) if module.directory not in hashed]


def _installs(root: Path, release: Release, module: Module, scratch: Path) -> bool:
    """Say whether ``go install`` takes ``module`` at the release's version from the tree.

    go fetches the workspace's modules from the scratch repository of the tree,
    which holds the release's tags, into a module cache of its own, as a
    consumer's install fetches them from GitHub once the tags exist.  That route
    reads the command's own go.mod, refuses a replace directive and names the
    binary after the path less its major, none of which a build in the
    command's directory exercises.  It verifies what it fetches against a
    checksum database, never the command's go.sum, so it runs with ``GOSUMDB``
    off: no lookup leaves the machine.
    """
    version = release.tag_version
    name = posixpath.basename(module.directory)
    binaries = scratch / "bin"
    flags = EnvValue("-modcacherw")
    env = served_environment(
        scratch / "tree",
        scratch / f"install-{name}",
        release,
        proxy=proxy_over_cache(),
        flags=flags,
    )
    target = W(f"{module.path}@{version}")
    env |= {EnvName("GOBIN"): EnvValue(str(binaries)), EnvName("GOSUMDB"): EnvValue("off")}
    ran = run_go(root, W("install"), target, env=env)
    if ran.status == 0 and (binaries / name).is_file():
        emit(f"go_release: go install {target} installs the command {name}")
        return True
    why = " | ".join((ran.out + ran.err).strip().splitlines()[-3:]) or f"no {name} installed"
    emit(f"go_release: go install {target} does not install the command {name}: {why}")
    return False


def _builds(root: Path, module: Module, env: Environment) -> bool:
    """Say whether ``module`` builds under ``env`` with its go.mod and go.sum as they are."""
    words = (W("build"), W("-mod=readonly"), W("-o"), W(os.devnull), W("./..."))
    ran = run_go(root / module.directory, *words, env=env)
    if ran.status != 0:
        tail = " | ".join((ran.out + ran.err).strip().splitlines()[-3:])
        emit(f"go_release: {module.directory} does not build outside the workspace: {tail}")
    return ran.status == 0


def write(root: Path) -> ExitStatus:
    """Point every requirement on a module of the workspace at the release; record its hashes."""
    read = worktree_reader(root)
    release = read_release(read)
    version = release.tag_version
    shipped = {without_major(module.path): module for module in required(release)}
    major = Major(int(release.version.split(".")[0]))
    unmoved = [m.path for m in released(release) if with_major(m.path, major) != m.path]
    if unmoved:
        verb = "carries" if len(unmoved) == 1 else "carry"
        emit(
            f"go_release: {', '.join(unmoved)} {verb} no major {major}, the release's: run"
            + " `python -m tools.go_release move-major` first"
        )
        return ExitStatus(1)
    for module in release.modules:
        manifest = root / module.directory / "go.mod"
        text = FileText(manifest.read_text(encoding="utf-8"))
        pinned = pinned_requirements(text, list(shipped.values()), version)
        if pinned != text:
            _ = manifest.write_text(pinned, encoding="utf-8")
    _replace_in_workspace(root, list(shipped.values()), version, clean_environment())
    _tidy_in_order(root, read_release(read))
    return ExitStatus(0)


def _tidy_in_order(root: Path, release: Release) -> None:
    """Tidy each module requiring another of the workspace against the tree, required first.

    The tree is exported again for each, since a module's zip holds its go.sum
    and the one tidied before it may have written that go.sum.
    """
    version = release.tag_version
    shipped = {without_major(module.path) for module in required(release)}
    tags = [tag_for(module, version) for module in released(release)]
    proxy = proxy_over_cache()
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
            _ = run_go_checked(root / module.directory, W("mod"), W("tidy"), env=env)
        emit(f"go_release: {module.directory} requires the release's modules at {version}")


def pinned_requirements(text: FileText, shipped: Sequence[Module], version: GoVersion) -> FileText:
    """Return the go.mod ``text`` requiring each module of ``shipped`` at ``version``, by path.

    The entries are rewritten as text: after a major move a requirement's old
    version is no version of its new path, and go refuses to parse the file.  A
    requirement spelled at another major of such a module moves to its path.
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
    """Make go.work replace each module of ``shipped`` at ``version`` by its directory, no other."""
    work = W(str(root / GO_WORK))
    answer = run_go_checked(root / "go", W("work"), W("edit"), W("-json"), work, env=env)
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
    _ = run_go_checked(root / "go", W("work"), W("edit"), *edits, work, env=env)


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
    for rel in filter(None, run_git(root, W("ls-files"), W("-z")).out.split("\0")):
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


class _AtCommit(NamedTuple):
    """A commit, read and served from a bare repository holding the release's tags on it."""

    commit: CommitId
    read: Reader
    release: Release
    repository: Path
    scratch: Path


def _at_commit(root: Path, commit: CommitId, scratch: Path) -> _AtCommit:
    """Return ``commit`` served from ``scratch``, every released module's tag naming it."""
    read = commit_reader(root, commit)
    release = read_release(read)
    repository = scratch / "repository.git"
    tags = [tag_for(module, release.tag_version) for module in released(release)]
    commit_repository(root, repository, commit, tags)
    return _AtCommit(commit, read, release, repository, scratch)


def _cache_of(at: _AtCommit, purpose: Prose, module: Module) -> Path:
    """Return a module cache of its own for fetching ``module`` for ``purpose``."""
    return at.scratch / f"{purpose}-{module.directory.replace('/', '-')}"


def check_commit(root: Path, commit: CommitId, expected: ReleaseVersion | None) -> list[Prose]:
    """Return how ``commit`` falls short of its recorded hashes, or of serving a command at its tag.

    A module another requires is held to the hashes each requiring go.sum
    records; a command, which no go.sum records, is fetched at its tag, which go
    refuses where the command's path lacks the release's major.
    """
    with tempfile.TemporaryDirectory(prefix="aletheia-go-release-") as name:
        at = _at_commit(root, commit, Path(name))
        found: list[Prose] = []
        if expected is not None and at.release.version != expected:
            found.append(Prose(f"{commit:.12} prepares {at.release.version}, not {expected}"))
        hashed = {module.directory for module in required(at.release)}
        for module in released(at.release):
            found.extend(_commit_findings(at, module, hashed))
    return found


def _commit_findings(at: _AtCommit, module: Module, hashed: set[RelPath]) -> list[Prose]:
    """Return how ``module`` at the commit differs from its records, or why go cannot fetch it."""
    version = at.release.tag_version
    cache = _cache_of(at, Prose("hash"), module)
    if module.directory not in hashed:
        fetched = served_hashes(at.repository, cache, at.release, module.path)
        return [] if isinstance(fetched, Hashes) else [fetched]
    records = recorded(at.read, at.release, module.path)
    if not records:
        return [
            Prose(
                f"{at.commit:.12}: no module requires {module.path} at {version}, so no go.sum"
                + " records what its tag publishes: run `python -m tools.go_release write`"
            )
        ]
    hashes = served_hashes(at.repository, cache, at.release, module.path)
    return differences(hashes, records, module.path, version)


def check_tags(root: Path, lines: Iterable[RefLine], remote: RemoteName) -> list[Prose]:
    """Return how the release tags git is pushing to ``remote`` fall short, from its ref lines.

    A release goes out in two pushes: every go/ tag of its version together,
    then ``vX.Y.Z`` alone once ``remote`` holds them all on its commit, since
    GitHub creates no event for tags when more than three are pushed at once
    and ``vX.Y.Z`` is the one the release workflow runs on.
    """
    pushed, others, found = _read_pushed(root, lines)
    for version, tags in sorted(pushed.items()):
        named = {tag.commit for tag in tags}
        if len(named) != 1:
            listed = ", ".join(sorted(f"{commit:.12}" for commit in named))
            found.append(Prose(f"release {version}'s tags name {len(named)} commits: {listed}"))
            continue
        alone = sum(len(tags) for tags in pushed.values()) + len(others) == 1
        found.extend(_push_findings(root, tags, remote, alone=alone))
        found.extend(check_commit(root, next(iter(named)), version))
    return found


class _PushedTags(NamedTuple):
    """What one push sends: its release tags by version, its other tags, each malformed go/ tag."""

    release: dict[ReleaseVersion, list[_Pushed]]
    others: list[TagName]
    found: list[Prose]


def _read_pushed(root: Path, lines: Iterable[RefLine]) -> _PushedTags:
    """Return the tags a push sends, read from the ref lines git hands a pre-push hook."""
    pushed: dict[ReleaseVersion, list[_Pushed]] = {}
    others: list[TagName] = []
    found: list[Prose] = []
    for line in lines:
        fields = line.split()
        if len(fields) != _REF_FIELDS or _NO_OBJECT.match(fields[1]):
            continue
        if not fields[2].startswith("refs/tags/"):
            continue
        spelled = fields[2].removeprefix("refs/tags/")
        name = TagName(spelled)
        matched = _RELEASE_TAG.match(spelled)
        if matched is None:
            others.append(name)
            if spelled.startswith("go/"):
                found.append(Prose(f"{name}: a go/ tag that is no <directory>/vX.Y.Z"))
            continue
        directory = RelPath(matched["directory"]) if matched["directory"] is not None else None
        tag = _Pushed(name, directory, commit_of(root, Revision(fields[1])))
        pushed.setdefault(ReleaseVersion(matched["version"]), []).append(tag)
    return _PushedTags(pushed, others, found)


def _push_findings(
    root: Path, tags: Sequence[_Pushed], remote: RemoteName, *, alone: bool
) -> list[Prose]:
    """Return how one version's pushed tags, all naming one commit, break the two pushes' order."""
    commit = tags[0].commit
    release = read_release(commit_reader(root, commit))
    modules = released(release)
    shipped = {module.directory for module in modules}
    directories = {tag.directory for tag in tags if tag.directory is not None}
    found = [
        Prose(f"{tag.name}: {tag.directory} is no released module at {commit:.12}")
        for tag in tags
        if tag.directory is not None and tag.directory not in shipped
    ]
    wanted = [tag_for(module, release.tag_version) for module in modules]
    if any(tag.directory is None for tag in tags):
        if not alone:
            found.append(Prose(f"{release.tag_version} goes alone, after the release's go/ tags"))
        held = remote_tags(root, remote)
        found.extend(
            Prose(f"{release.tag_version} is pushed before {tag} is on {remote} at {commit:.12}")
            for tag in wanted
            if held.get(tag) != commit
        )
    elif directories:
        left = [
            tag
            for tag, module in zip(wanted, modules, strict=True)
            if module.directory not in directories
        ]
        if left:
            found.append(
                Prose(
                    f"release {release.version}'s go/ tags go together: this push leaves out"
                    + f" {', '.join(left)}"
                )
            )
    return found


def check_published(root: Path, version: ReleaseVersion) -> list[Prose]:
    """Return how the released modules GitHub serves at ``version`` differ from the tag's.

    A module another requires is held to the tag's go.sum lines; a command, which
    no go.sum records, to the hashes of the tagged commit's own objects.
    """
    commit = _release_commit(root, version)
    with tempfile.TemporaryDirectory(prefix="aletheia-go-release-") as name:
        at = _at_commit(root, commit, Path(name))
        found: list[Prose] = []
        if at.release.version != version:
            found.append(
                Prose(f"v{version} names {commit:.12}, which prepares {at.release.version}")
            )
        env = github_environment(at.scratch / "github", at.release)
        hashed = {module.directory for module in required(at.release)}
        for module in released(at.release):
            found.extend(_published_findings(at, module, hashed, env))
    return found


def _release_commit(root: Path, version: ReleaseVersion) -> CommitId:
    """Return the commit the release's tags here name: ``vX.Y.Z``, or its go/ tags before it."""
    listed = run_git(root, W("tag"), W("--list"), W(f"v{version}"), W(f"go/*v{version}")).out
    named = {commit_of(root, Revision(n)) for n in listed.split() if _RELEASE_TAG.match(n)}
    if len(named) != 1:
        message = f"release {version}'s tags here name {len(named)} commits, not one"
        raise CannotCheckError(message)
    return named.pop()


def _published_findings(
    at: _AtCommit, module: Module, hashed: set[RelPath], env: Environment
) -> list[Prose]:
    """Return how GitHub's ``module`` at the tag differs from its records or the commit's own."""
    version = at.release.tag_version
    if module.directory not in hashed:
        github = fetch(at.scratch, module.path, version, env)
        local = served_hashes(
            at.repository, _cache_of(at, Prose("local"), module), at.release, module.path
        )
        return rehearsal_findings(module.path, github, local)
    records = recorded(at.read, at.release, module.path)
    if not records:
        return [Prose(f"{version}: no go.sum records {module.path}")]
    hashes = download(at.scratch, module.path, version, env)
    return differences(hashes, records, module.path, version)


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
    _ = run_git(dest, W("update-ref"), W("refs/heads/rehearsed"), W(commit))
    tags = run_git(root, W("for-each-ref"), W("--format=%(objectname) %(refname)"), W("refs/tags"))
    for line in tags.out.splitlines():
        target, ref = line.split(" ", 1)
        _ = run_git(dest, W("update-ref"), W(ref), W(target))


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
    held = Prose(f"{commit:.12} holds its recorded hashes, and go fetches each command at its tag")
    return _report(check_commit(root, commit, None), held)


def main(argv: list[CommandWord] | None = None) -> ExitStatus:
    """Run the command ``argv`` names."""
    parser = argparse.ArgumentParser(description=HelpText(__doc__ or ""))
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("move-major", "write", "check"):
        _ = commands.add_parser(name)
    _ = commands.add_parser("check-tags").add_argument("remote", type=RemoteName)
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
            check_tags(
                root,
                [RefLine(line) for line in sys.stdin.read().splitlines()],
                cast("RemoteName", arguments.remote),
            ),
            Prose(
                "the release tags pushed keep the two pushes' order, on a commit check-commit holds"
            ),
        ),
        W("check-published"): lambda: _report(
            check_published(root, cast("ReleaseVersion", arguments.version)),
            Prose("the published modules hash as the tagged commit records or holds them"),
        ),
    }
    try:
        return actions[cast("CommandWord", arguments.command)]()
    except CannotCheckError as error:
        emit(f"go_release: cannot check: {error}")
        return ExitStatus(2)


if __name__ == "__main__":
    sys.exit(reporting(main, Prose("go-release")))
