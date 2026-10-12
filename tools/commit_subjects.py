# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/commit_subjects.py — The commit-subject vocabulary, and what each subject owes CHANGELOG.

A subject reads ``type(scope)!: text``: a type and a scope from the lists below,
the breaking mark ``!`` after the scope, a colon, one space and the text.  The
lists are closed.  A type or a scope they do not name is refused, and adding or
retiring one is a change to this module, whose tests pin each list.  A pull
request's title is the subject its squash commit lands with, so the title is
held to the same vocabulary as every commit on the branch.

Whether a subject owes the CHANGELOG an entry is one table (``owed_entry``):

* ``feat``, ``fix`` and ``perf`` name a scope.  With a shipped scope they owe an
  entry, under ``### Added``, ``### Fixed`` and ``### Changed``; with an
  internal scope, the project's own tooling, none.
* ``refactor``, ``test``, ``docs``, ``ci``, ``build``, ``deps`` and ``chore``
  owe none, and may omit the scope for a change across the tree.
* ``revert`` names no scope and no mark of its own: its text is the subject it
  reverts, which is not itself a revert (re-applying a change is that change's
  own subject), and it owes what that subject owes.
* The breaking mark makes any subject owe an entry, with a BREAKING lead under
  ``### Changed``, or ``### Removed`` when surface goes.
* A branch edits the CHANGELOG only when a subject owes it an entry or a record
  of the public surface changed, the release preparation apart:
  ``chore(dist): prepare vX.Y.Z`` moves the unreleased entries under the
  version's heading and owes none (``cuts_a_release``; ``release_version``
  reads the version, ``released`` every version a branch prepares).

The text is one line of printable characters, starting with one that is not a
space.

A label is the author's claim, so it is held to the files the branch changes
where a file can say it (``mislabelled``): a branch that changes what users get
(``ships``) carries a label naming a shipped scope, or none, never internal ones
alone.  A behaviour change filed as a ``refactor`` of a shipped scope reads the
same as a real one from its files, and stays a reviewer's call; so does a change
to the dist rules, ``shake/Rules/Dist.hs``, which ``ships`` leaves out.

Nothing here needs a package beyond the standard library and the project's own,
so the pull-request title check runs on a bare interpreter.
"""

from __future__ import annotations

import re
import sys
from enum import StrEnum
from typing import NamedTuple, NewType

from tools._common import RelPath, find_executable, run_capture

from aletheia.common_types import Prose

# A revision as git's command line names it, and one argument of a git command.
Revision = NewType("Revision", str)
GitArg = NewType("GitArg", str)
# A release's version as its CHANGELOG heading spells it, ``X.Y.Z`` (its tag is ``vX.Y.Z``).
ReleaseVersion = NewType("ReleaseVersion", str)


class CommitType(StrEnum):
    """The types a subject may carry."""

    FEAT = "feat"
    FIX = "fix"
    PERF = "perf"
    REFACTOR = "refactor"
    TEST = "test"
    DOCS = "docs"
    CI = "ci"
    BUILD = "build"
    DEPS = "deps"
    CHORE = "chore"
    REVERT = "revert"


class Scope(StrEnum):
    """The scopes a subject may name: what users get, then the project's own tooling."""

    KERNEL = "kernel"
    FFI = "ffi"
    PYTHON = "python"
    GO = "go"
    CPP = "cpp"
    RUST = "rust"
    CLI = "cli"
    EXCEL = "excel"
    DIST = "dist"
    CI = "ci"
    MUTATION = "mutation"
    BENCH = "bench"
    TOOLS = "tools"
    PROBES = "probes"
    HOOKS = "hooks"
    DOCS = "docs"
    BUILD = "build"
    DEPS = "deps"
    PROOFS = "proofs"


# What users get: the kernel, its C ABI, the four bindings, the command lines,
# the Excel loaders and the distribution.  Every other scope is internal.
SHIPPED_SCOPES = frozenset(
    {
        Scope.KERNEL,
        Scope.FFI,
        Scope.PYTHON,
        Scope.GO,
        Scope.CPP,
        Scope.RUST,
        Scope.CLI,
        Scope.EXCEL,
        Scope.DIST,
    }
)
# The types that name a scope, and the CHANGELOG category each owes a shipped one.
_ENTRY_TYPES = {
    CommitType.FEAT: Prose("### Added"),
    CommitType.FIX: Prose("### Fixed"),
    CommitType.PERF: Prose("### Changed"),
}
_BREAKING = Prose("a BREAKING lead under ### Changed, or ### Removed when surface goes")
_TYPE_WORDS = frozenset(kind.value for kind in CommitType)
_SCOPE_WORDS = frozenset(scope.value for scope in Scope)
_SHAPE = re.compile(
    r"(?P<type>[a-z]+)(?:\((?P<scope>[a-z-]+)\))?(?P<bang>!)?: "
    + r"(?P<text>[^\s\x00-\x1f\x7f][^\x00-\x1f\x7f]*)"
)


class Subject(NamedTuple):
    """A subject the vocabulary accepts.

    ``scope`` is None only where the type may omit it; ``reverted`` is the
    subject a ``revert`` reverts, parsed, and None for every other type.
    """

    type: CommitType
    scope: Scope | None
    breaking: bool
    text: Prose
    reverted: Subject | None = None


class Refusal(NamedTuple):
    """Why the vocabulary refuses a subject, worded for the person who wrote it."""

    reason: Prose


def _named(words: type[StrEnum]) -> Prose:
    return Prose(", ".join(word.value for word in words))


def parse(subject: Prose) -> Subject | Refusal:
    """Read a subject against the vocabulary: the subject it is, or why it is refused."""
    shape = _SHAPE.fullmatch(subject)
    if shape is None:
        return Refusal(Prose("it does not read `type(scope)!: text`"))
    read = _read(
        Prose(shape["type"]),
        None if shape["scope"] is None else Prose(shape["scope"]),
        breaking=shape["bang"] is not None,
        text=Prose(shape["text"]),
    )
    if isinstance(read, Refusal) or read.type is not CommitType.REVERT:
        return read
    return _revert(read)


def _read(
    word: Prose, scope_word: Prose | None, *, breaking: bool, text: Prose
) -> Subject | Refusal:
    """Hold a subject's type and scope words to the lists, and the scope to its type."""
    if word not in _TYPE_WORDS:
        return Refusal(Prose(f"`{word}` is not a type: {_named(CommitType)}"))
    if scope_word is not None and scope_word not in _SCOPE_WORDS:
        return Refusal(Prose(f"`{scope_word}` is not a scope: {_named(Scope)}"))
    kind = CommitType(word)
    if kind in _ENTRY_TYPES and scope_word is None:
        return Refusal(Prose(f"a `{kind}` subject names its scope"))
    scope = None if scope_word is None else Scope(scope_word)
    return Subject(kind, scope, breaking=breaking, text=text)


def _revert(subject: Subject) -> Subject | Refusal:
    """Read a revert: no scope or mark of its own, its text a subject that is not a revert."""
    if subject.scope is not None or subject.breaking:
        return Refusal(Prose("a revert names no scope or mark; its text is the subject it reverts"))
    inner = _SHAPE.fullmatch(subject.text)
    if inner is not None and inner["type"] == CommitType.REVERT:
        return Refusal(Prose("a revert reverts no revert: re-applying a change is its own subject"))
    reverted = parse(subject.text)
    if isinstance(reverted, Refusal):
        return Refusal(Prose(f"the reverted subject is refused: {reverted.reason}"))
    return subject._replace(reverted=reverted)


def owed_entry(subject: Subject) -> Prose | None:
    """Say where the CHANGELOG entry a subject owes goes, or None when it owes none."""
    if subject.reverted is not None:
        subject = subject.reverted
    if subject.breaking:
        return _BREAKING
    if subject.scope in SHIPPED_SCOPES:
        return _ENTRY_TYPES.get(subject.type)
    return None


# A release's version as SemVer writes X.Y.Z: ASCII digits, no leading zero.
VERSION_PATTERN = r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)"
# The release preparation's text (docs/development/RELEASE.md), the one subject
# that edits the CHANGELOG while owing it nothing; its group is the version cut.
_RELEASE_TEXT = re.compile(rf"prepare v({VERSION_PATTERN})")


def release_version(subject: Subject) -> ReleaseVersion | None:
    """Return the version the release preparation cuts, or None for any other subject."""
    if subject.type is not CommitType.CHORE or subject.scope is not Scope.DIST:
        return None
    matched = _RELEASE_TEXT.fullmatch(subject.text)
    return None if matched is None else ReleaseVersion(matched.group(1))


def cuts_a_release(subject: Subject) -> bool:
    """Say whether the subject is the release preparation, which edits the CHANGELOG owing none."""
    return release_version(subject) is not None


def released(branch: Branch) -> frozenset[ReleaseVersion]:
    """Return the versions the branch's commits prepare, a subject the vocabulary refuses aside."""
    reads = [read for read in map(parse, branch.subjects) if isinstance(read, Subject)]
    return frozenset(version for version in map(release_version, reads) if version is not None)


# Where what users get lives, outside the kernel: every file under these
# directories, the tests beside a binding's code included, so a change there names
# that binding's scope; the manifests that build or resolve a shipped artifact;
# and the runtime image.
_SHIPPED_DIRS = (
    "python/aletheia/",
    "go/aletheia/",
    "go/excel/",
    "go/cmd/",
    "cpp/src/",
    "cpp/include/",
    "rust/src/",
    "rust/excel/src/",
    "haskell-shim/src/",
    "haskell-shim/include/",
    "haskell-shim/cbits/",
    "packaging/",
    "cpp/cmake/",
)
_SHIPPED_FILES = frozenset(
    {
        RelPath("Dockerfile.runtime"),
        RelPath("python/pyproject.toml"),
        RelPath("go/go.mod"),
        RelPath("go/go.sum"),
        RelPath("cpp/CMakeLists.txt"),
        RelPath("rust/Cargo.toml"),
        RelPath("rust/Cargo.lock"),
        RelPath("rust/excel/Cargo.toml"),
        RelPath("rust/excel/Cargo.lock"),
        RelPath("haskell-shim/aletheia.cabal"),
    }
)
# The kernel's shipped modules are the ones the shared library compiles, which
# the shim's reviewed snapshot lists; a proof module outside it ships nothing.
RUNTIME_CLOSURE = RelPath("haskell-shim/runtime-closure.snapshot")
_KERNEL_MODULE = "MAlonzo.Code.Aletheia."


def kernel_sources(snapshot: Prose) -> frozenset[RelPath]:
    """Give the Agda sources of the kernel modules a runtime-closure snapshot lists."""
    return frozenset(
        RelPath("src/Aletheia/" + line.removeprefix(_KERNEL_MODULE).replace(".", "/") + ".agda")
        for line in snapshot.splitlines()
        if line.startswith(_KERNEL_MODULE)
    )


def ships(path: RelPath, kernel: frozenset[RelPath]) -> bool:
    """Say whether a tracked path is part of what users get, or a test living beside it."""
    return path in kernel or path in _SHIPPED_FILES or path.startswith(_SHIPPED_DIRS)


def _scope(subject: Subject) -> Scope | None:
    """Give the scope a subject claims; a revert claims the one of the subject it reverts."""
    return subject.scope if subject.reverted is None else subject.reverted.scope


def mislabelled(
    changed: list[RelPath], kernel: frozenset[RelPath], labels: list[Subject]
) -> list[RelPath]:
    """Give the shipped files a branch changes when every label names an internal scope.

    An empty list is a branch whose labels are consistent with its files: one of
    them names a shipped scope or none, there is no label, or nothing it
    changes ships.
    """
    if not labels or any(
        _scope(label) is None or _scope(label) in SHIPPED_SCOPES for label in labels
    ):
        return []
    return [path for path in changed if ships(path, kernel)]


class Branch(NamedTuple):
    """What a branch holds since its merge-base: the files it changed, its commits' subjects.

    Merge commits are left out: a branch brought up to date with its base gains
    one, worded by git, which is no change of the branch's own.  ``merge_base``
    is the commit the branch is read from.
    """

    changed: list[RelPath]
    subjects: list[Prose]
    merge_base: Revision


def _git(tool: Prose, *args: GitArg) -> list[Prose] | None:
    """Run git; give the lines it printed, or write why it failed, naming ``tool``, and None."""
    out = run_capture([find_executable("git"), *args])
    if out.returncode != 0:
        _ = sys.stderr.write(f"{tool}: git {' '.join(args)} failed\n{out.stderr}")
        return None
    return [Prose(line) for line in out.stdout.splitlines() if line]


def toplevel(tool: Prose) -> Prose | None:
    """Give the repository's top level, or None when git cannot say."""
    found = _git(tool, GitArg("rev-parse"), GitArg("--show-toplevel"))
    return None if found is None else Prose("".join(found))


def read_branch(tool: Prose, base: Revision) -> Branch | None:
    """Read what HEAD holds since its merge-base with ``base``, or None when git cannot say."""
    merge_base = _git(tool, GitArg("merge-base"), GitArg("HEAD"), GitArg(base))
    if merge_base is None:
        return None
    fork = Revision("".join(merge_base))
    span = GitArg(f"{fork}..HEAD")
    changed = _git(tool, GitArg("diff"), GitArg("--name-only"), span)
    subjects = _git(tool, GitArg("log"), GitArg("--no-merges"), GitArg("--format=%s"), span)
    if changed is None or subjects is None:
        return None
    return Branch([RelPath(line) for line in changed], subjects, fork)
