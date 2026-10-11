# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.commit_subjects`` — the closed vocabulary and the CHANGELOG table.

The lists are pinned whole, so adding or retiring a type or a scope changes a
test as well as the module; the parser is held to each refusal it words; the
table is held cell by cell, every type against a shipped scope, an internal
scope and none, with and without the breaking mark.
"""

from __future__ import annotations

import pytest

from tools._common import RelPath
from tools.commit_subjects import (
    SHIPPED_SCOPES,
    CommitType,
    Refusal,
    Scope,
    Subject,
    kernel_sources,
    mislabelled,
    owed_entry,
    parse,
    ships,
)

from aletheia.common_types import Prose

ADDED = Prose("### Added")
FIXED = Prose("### Fixed")
CHANGED = Prose("### Changed")
BREAKING = Prose("a BREAKING lead under ### Changed, or ### Removed when surface goes")
OFF_SHAPE = Refusal(Prose("it does not read `type(scope)!: text`"))
ENTRY_TYPES = [CommitType.FEAT, CommitType.FIX, CommitType.PERF]
QUIET_TYPES = [
    CommitType.REFACTOR,
    CommitType.TEST,
    CommitType.DOCS,
    CommitType.CI,
    CommitType.BUILD,
    CommitType.DEPS,
    CommitType.CHORE,
]


def test_the_types_are_the_eleven_ruled() -> None:
    """The types, in the order the vocabulary lists them."""
    assert [kind.value for kind in CommitType] == [
        "feat",
        "fix",
        "perf",
        "refactor",
        "test",
        "docs",
        "ci",
        "build",
        "deps",
        "chore",
        "revert",
    ]


def test_the_scopes_are_the_nineteen_ruled() -> None:
    """The scopes, what users get first, then the project's own tooling."""
    assert [scope.value for scope in Scope] == [
        "kernel",
        "ffi",
        "python",
        "go",
        "cpp",
        "rust",
        "cli",
        "excel",
        "dist",
        "ci",
        "mutation",
        "bench",
        "tools",
        "probes",
        "hooks",
        "docs",
        "build",
        "deps",
        "proofs",
    ]


def test_the_shipped_scopes_are_the_first_nine() -> None:
    """What users get: the kernel, its ABI, the four bindings, the CLIs, Excel and the bundle."""
    assert {scope.value for scope in SHIPPED_SCOPES} == {
        "kernel",
        "ffi",
        "python",
        "go",
        "cpp",
        "rust",
        "cli",
        "excel",
        "dist",
    }


@pytest.mark.parametrize(
    ("subject", "expected"),
    [
        (
            Prose("feat(python): a feature"),
            Subject(CommitType.FEAT, Scope.PYTHON, breaking=False, text=Prose("a feature")),
        ),
        (
            Prose("refactor: across the tree"),
            Subject(CommitType.REFACTOR, None, breaking=False, text=Prose("across the tree")),
        ),
        (
            Prose("docs(kernel)!: breaking"),
            Subject(CommitType.DOCS, Scope.KERNEL, breaking=True, text=Prose("breaking")),
        ),
        (
            Prose("ci(mutation): a lane"),
            Subject(CommitType.CI, Scope.MUTATION, breaking=False, text=Prose("a lane")),
        ),
    ],
    ids=["scoped", "unscoped", "breaking", "internal"],
)
def test_a_subject_is_read_whole(subject: Prose, expected: Subject) -> None:
    """A subject reads as its type, scope, mark and text."""
    assert parse(subject) == expected


@pytest.mark.parametrize(
    "subject",
    [
        Prose("refactor!(log): the mark before the scope"),
        Prose("fix(python):no space"),
        Prose("fix(python):  two spaces"),
        Prose("fix(python): "),
        Prose("fix(python)"),
        Prose("Fix(python): capitalised"),
        Prose("fix(Python): capitalised scope"),
        Prose("fix (python): a space before the scope"),
        Prose("fix(python) : a space before the colon"),
        Prose("fix(): an empty scope"),
        Prose("Merge branch 'main' into feature"),
        Prose('Revert "fix(python): a bug"'),
        Prose("fixup! fix(python): a bug"),
        Prose("fix(python,go): two scopes"),
        Prose(" fix(python): indented"),
        Prose("fix(python): one line\nand another"),
        Prose("fix(python): a\ttab"),
        Prose("fix(python): a carriage\rreturn"),
        Prose("fix(python): a\x00nul"),
        Prose("fix(python): a\x7fdel"),
        Prose("fix(python): \u3000a wide space first"),
        Prose("fix(python): \x00a nul first"),
        Prose("fix(python): \x7fa del first"),
        Prose(""),
    ],
)
def test_a_subject_off_the_shape_is_refused(subject: Prose) -> None:
    """Anything but ``type(scope)!: text`` exactly, lowercase, one space, is refused."""
    assert parse(subject) == OFF_SHAPE


def test_a_type_outside_the_vocabulary_is_refused_and_the_types_named() -> None:
    """An unknown type is named, with every type the vocabulary holds."""
    assert parse(Prose("style(python): a")) == Refusal(
        Prose(
            "`style` is not a type: feat, fix, perf, refactor, test, docs, ci, build, deps, "
            + "chore, revert"
        )
    )


def test_a_scope_outside_the_vocabulary_is_refused_and_the_scopes_named() -> None:
    """An unknown scope is named, with every scope the vocabulary holds."""
    assert parse(Prose("fix(go-excel): a")) == Refusal(
        Prose(
            "`go-excel` is not a scope: kernel, ffi, python, go, cpp, rust, cli, excel, dist, "
            + "ci, mutation, bench, tools, probes, hooks, docs, build, deps, proofs"
        )
    )


@pytest.mark.parametrize("kind", ENTRY_TYPES)
def test_an_entry_deciding_type_names_its_scope(kind: CommitType) -> None:
    """``feat``, ``fix`` and ``perf`` without a scope are refused, marked or not."""
    reason = Refusal(Prose(f"a `{kind}` subject names its scope"))
    assert parse(Prose(f"{kind}: across the tree")) == reason
    assert parse(Prose(f"{kind}!: across the tree")) == reason


@pytest.mark.parametrize("kind", QUIET_TYPES)
def test_every_other_type_may_omit_its_scope(kind: CommitType) -> None:
    """The types that owe nothing may leave the scope out."""
    assert parse(Prose(f"{kind}: across the tree")) == Subject(
        kind, None, breaking=False, text=Prose("across the tree")
    )


def test_a_revert_reads_the_subject_it_reverts() -> None:
    """A revert's text is a subject of its own, read in the same vocabulary."""
    assert parse(Prose("revert: feat(go): a feature")) == Subject(
        CommitType.REVERT,
        None,
        breaking=False,
        text=Prose("feat(go): a feature"),
        reverted=Subject(CommitType.FEAT, Scope.GO, breaking=False, text=Prose("a feature")),
    )


@pytest.mark.parametrize(
    "subject",
    [Prose("revert(go): feat(go): a feature"), Prose("revert!: feat(go): a feature")],
    ids=["scope", "mark"],
)
def test_a_revert_carries_no_scope_or_mark_of_its_own(subject: Prose) -> None:
    """What a revert owes is the reverted subject's, so it names neither."""
    assert parse(subject) == Refusal(
        Prose("a revert names no scope or mark; its text is the subject it reverts")
    )


def test_a_revert_reverts_no_revert() -> None:
    """Re-applying a change is that change's own subject, so a revert of a revert is refused."""
    assert parse(Prose("revert: revert: fix(go): a bug")) == Refusal(
        Prose("a revert reverts no revert: re-applying a change is its own subject")
    )


def test_a_long_chain_of_reverts_is_refused_without_raising() -> None:
    """However deep the chain an author writes, the reading ends in a refusal, not a crash."""
    read = parse(Prose("revert: " * 5000 + "fix(go): a bug"))
    assert isinstance(read, Refusal)


def test_a_revert_of_text_off_the_shape_is_refused_and_says_why() -> None:
    """A revert whose text is no subject at all is refused with the shape's reason."""
    assert parse(Prose("revert: Fix the loader")) == Refusal(
        Prose("the reverted subject is refused: it does not read `type(scope)!: text`")
    )


def test_a_revert_of_a_refused_subject_is_refused_and_says_why() -> None:
    """A revert whose text the vocabulary refuses is refused with that reason."""
    assert parse(Prose("revert: style: a")) == Refusal(
        Prose(
            "the reverted subject is refused: `style` is not a type: feat, fix, perf, refactor, "
            + "test, docs, ci, build, deps, chore, revert"
        )
    )


def _owes(subject: Prose) -> Prose | None:
    read = parse(subject)
    assert isinstance(read, Subject), read
    return owed_entry(read)


@pytest.mark.parametrize(
    ("kind", "expected"), list(zip(ENTRY_TYPES, [ADDED, FIXED, CHANGED], strict=True))
)
def test_an_entry_deciding_type_owes_its_category_on_every_shipped_scope(
    kind: CommitType, expected: Prose
) -> None:
    """``feat``, ``fix`` and ``perf`` on a shipped scope owe their category's entry."""
    for scope in SHIPPED_SCOPES:
        assert _owes(Prose(f"{kind}({scope}): a change")) == expected


@pytest.mark.parametrize("kind", ENTRY_TYPES)
def test_an_entry_deciding_type_owes_nothing_on_an_internal_scope(kind: CommitType) -> None:
    """On the project's own tooling, ``feat``, ``fix`` and ``perf`` owe no entry."""
    for scope in set(Scope) - SHIPPED_SCOPES:
        assert _owes(Prose(f"{kind}({scope}): a change")) is None


@pytest.mark.parametrize("kind", QUIET_TYPES)
def test_every_other_type_owes_nothing_whatever_its_scope(kind: CommitType) -> None:
    """The types that change nothing a user sees owe no entry, scoped or not."""
    assert _owes(Prose(f"{kind}: a change")) is None
    for scope in Scope:
        assert _owes(Prose(f"{kind}({scope}): a change")) is None


@pytest.mark.parametrize("kind", [*ENTRY_TYPES, *QUIET_TYPES])
def test_the_breaking_mark_owes_a_breaking_entry_whatever_the_scope(kind: CommitType) -> None:
    """The mark makes any subject owe an entry with a BREAKING lead, internal scope included."""
    for scope in Scope:
        assert _owes(Prose(f"{kind}({scope})!: a change")) == BREAKING


@pytest.mark.parametrize(
    ("subject", "expected"),
    [
        (Prose("revert: feat(python): a feature"), ADDED),
        (Prose("revert: fix(ci): a gate"), None),
        (Prose("revert: refactor(kernel)!: a break"), BREAKING),
        (Prose("revert: perf(rust): a speed-up"), CHANGED),
    ],
    ids=["shipped-feat", "internal-fix", "breaking", "shipped-perf"],
)
def test_a_revert_owes_what_the_subject_it_reverts_owes(
    subject: Prose, expected: Prose | None
) -> None:
    """A revert's entry is the one its reverted subject would owe."""
    assert _owes(subject) == expected


KERNEL = frozenset({RelPath("src/Aletheia/Main.agda"), RelPath("src/Aletheia/CAN/Frame.agda")})


def test_the_kernel_sources_are_the_aletheia_modules_the_snapshot_lists() -> None:
    """Each ``MAlonzo.Code.Aletheia.*`` line names a source under ``src/``; stdlib lines none."""
    snapshot = Prose(
        "MAlonzo.Code.Agda.Builtin.Bool\nMAlonzo.Code.Aletheia.CAN.Frame\n"
        + "MAlonzo.Code.Aletheia.Main\nMAlonzo.Code.Data.Nat.Base\n"
    )
    assert kernel_sources(snapshot) == KERNEL


@pytest.mark.parametrize(
    "path",
    [
        RelPath("src/Aletheia/Main.agda"),
        RelPath("python/aletheia/client/_client.py"),
        RelPath("python/pyproject.toml"),
        RelPath("go/aletheia/client.go"),
        RelPath("go/aletheia/aletheia_abi.h"),
        RelPath("go/aletheia/client_test.go"),
        RelPath("go/aletheia/testdata/doc_examples/checks.yaml"),
        RelPath("go/go.mod"),
        RelPath("go/go.sum"),
        RelPath("go/excel/excel.go"),
        RelPath("go/excel/excel_test.go"),
        RelPath("go/cmd/aletheia/main.go"),
        RelPath("cpp/src/client.cpp"),
        RelPath("cpp/include/aletheia/client.hpp"),
        RelPath("cpp/CMakeLists.txt"),
        RelPath("cpp/cmake/aletheia-cpp-config.cmake.in"),
        RelPath("rust/src/lib.rs"),
        RelPath("rust/src/tests.rs"),
        RelPath("rust/Cargo.toml"),
        RelPath("rust/Cargo.lock"),
        RelPath("rust/excel/src/lib.rs"),
        RelPath("rust/excel/Cargo.toml"),
        RelPath("rust/excel/Cargo.lock"),
        RelPath("haskell-shim/src/AletheiaFFI.hs"),
        RelPath("haskell-shim/include/aletheia.h"),
        RelPath("haskell-shim/cbits/abi_version.c"),
        RelPath("haskell-shim/aletheia.cabal"),
        RelPath("packaging/install.fish"),
        RelPath("Dockerfile.runtime"),
    ],
)
def test_what_users_get_ships(path: RelPath) -> None:
    """The kernel's compiled modules, every binding's tree and manifests, the shim, the bundle."""
    assert ships(path, KERNEL)


@pytest.mark.parametrize(
    "path",
    [
        RelPath("src/Aletheia/CAN/Frame/Properties.agda"),
        RelPath("python/tests/test_client.py"),
        RelPath("cpp/tests/unit_tests.cpp"),
        RelPath("rust/tests/dbc_model.rs"),
        RelPath("rust/excel/tests/excel_portability.rs"),
        RelPath("go/benchmarks/main.go"),
        RelPath("go/README.md"),
        RelPath("go/go.work"),
        RelPath("haskell-shim/ffi-exports.snapshot"),
        RelPath("haskell-shim/runtime-closure.snapshot"),
        RelPath("Shakefile.hs"),
        RelPath("tools/check_changelog.py"),
        RelPath("docs/FEATURE_MATRIX.yaml"),
    ],
)
def test_suites_benchmarks_tools_docs_and_proofs_do_not_ship(path: RelPath) -> None:
    """A proof module, the suites outside a binding's tree, benchmarks, gates and docs."""
    assert not ships(path, KERNEL)


def _labels(*subjects: Prose) -> list[Subject]:
    read = [parse(subject) for subject in subjects]
    assert all(isinstance(label, Subject) for label in read), read
    return [label for label in read if isinstance(label, Subject)]


BRANCH_FILES = [RelPath("tools/x.py"), RelPath("python/aletheia/client/_client.py")]


def test_shipped_files_under_internal_labels_alone_are_named() -> None:
    """Every label internal and a shipped file changed: the shipped files are named."""
    labels = _labels(Prose("fix(tools): a gate"), Prose("ci(mutation): a lane"))
    assert mislabelled(BRANCH_FILES, KERNEL, labels) == [
        RelPath("python/aletheia/client/_client.py")
    ]


@pytest.mark.parametrize(
    "labels",
    [
        (Prose("fix(tools): a gate"), Prose("fix(python): a bug")),
        (Prose("refactor: across the tree"),),
        (Prose("revert: fix(python): a bug"),),
        (),
    ],
    ids=["one-shipped", "unscoped", "revert-of-shipped", "no-label"],
)
def test_a_label_naming_a_shipped_scope_or_none_fits_shipped_files(
    labels: tuple[Prose, ...],
) -> None:
    """One label naming a shipped scope or none, or no label at all, fits any branch."""
    assert mislabelled(BRANCH_FILES, KERNEL, _labels(*labels)) == []


def test_a_revert_of_an_internal_subject_is_internal() -> None:
    """A revert claims the scope of what it reverts, so reverting a tooling fix is internal."""
    assert mislabelled(BRANCH_FILES, KERNEL, _labels(Prose("revert: fix(tools): a gate"))) == [
        RelPath("python/aletheia/client/_client.py")
    ]


def test_internal_labels_fit_a_branch_that_ships_nothing() -> None:
    """Internal labels on a branch whose files ship nothing are consistent."""
    assert mislabelled([RelPath("tools/x.py")], KERNEL, _labels(Prose("fix(tools): a gate"))) == []
