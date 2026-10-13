# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_changelog``: a branch's subjects, the entries they owe, the section.

Three layers:

* ``owed`` / ``subjects_refused`` — the pure reading of a branch: the surface
  records it changed and the subjects owing an entry by the vocabulary's table,
  and every subject the vocabulary refuses (the table itself is
  ``test_commit_subjects``'s).
* ``unreleased_headers`` / ``headers_refused`` — the pure audit of the section's
  ``###`` headers, read as CommonMark; ``cut_problem``, the pure reading of a
  release cut against its base, each way a CHANGELOG falls short of one named.
* ``main`` — an end-to-end run over a planted top level, the branch fed as the
  data git lists: a refused subject fails; a subject owing an entry, or a
  surface record changed, fails without a CHANGELOG edit and passes with one;
  anything else passes without one; a release preparation passes with its cut
  and fails without it, or beside a second release; a git step that cannot
  answer, or a base CHANGELOG not given as UTF-8, stops the gate with exit 2.
  One run plants a git repository, its claim being what git itself lists: a
  merge commit is no subject of the branch's.
"""

from __future__ import annotations

import subprocess
from types import SimpleNamespace
from typing import TYPE_CHECKING, Literal, NewType

import pytest
from _git_repo import commit, git, merge

from tools._common import RelPath
from tools.check_changelog import (
    CHANGELOG,
    SURFACE_RECORDS,
    Category,
    CutProblem,
    Owed,
    OwedSubject,
    UnreleasedHeaders,
    cut_problem,
    headers_refused,
    main,
    owed,
    subjects_refused,
    unreleased_headers,
)
from tools.commit_subjects import Branch, GitArg, ReleaseVersion, Revision

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

ADDED = Prose("### Added")
FIXED = Prose("### Fixed")
# The unreleased entry, and the same entry cut under 1.2.3, each after a title line.
ENTRY_TAIL = "\n## [Unreleased]\n\n### Fixed\n\n- **A bug.** Gone.\n"
CUT_TAIL = "\n## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n\n### Fixed\n\n- **A bug.** Gone.\n"
ENTRY = Prose("# Changelog\n" + ENTRY_TAIL)
CUT = Prose("# Changelog\n" + CUT_TAIL)
RELEASE = Prose("chore(dist): prepare v1.2.3")
VERSION = ReleaseVersion("1.2.3")
BASE = Revision("base")
MAIN = Revision("main")
# A top level's defaults: an empty section, and a snapshot naming Main and one stdlib module.
UNRELEASED = Prose("# Changelog\n\n## [Unreleased]\n")
SNAPSHOT = Prose("MAlonzo.Code.Aletheia.Main\nMAlonzo.Code.Data.Nat.Base\n")
# CHANGELOG.md's bytes as the base commits them.
BaseBytes = NewType("BaseBytes", bytes)
# The git step a stand-in for git makes fail.
type GitStep = Literal["rev-parse", "merge-base", "diff", "log"]


def test_the_surface_records_are_the_four_named() -> None:
    """The records are the feature matrix, the ABI snapshot, the wire codes and the log events."""
    assert {
        RelPath("docs/FEATURE_MATRIX.yaml"),
        RelPath("haskell-shim/ffi-exports.snapshot"),
        RelPath("docs/WIRE_CODES.yaml"),
        RelPath("docs/LOG_EVENTS.yaml"),
    } == SURFACE_RECORDS


@pytest.mark.parametrize("record", sorted(SURFACE_RECORDS))
def test_a_surface_record_changed_is_owed(record: RelPath) -> None:
    """Each public-surface record a branch changes is named as owing an entry."""
    assert owed(Branch([RelPath("tools/x.py"), record], [], BASE)) == Owed([record], [])


def test_the_subjects_owing_an_entry_are_named_with_where_it_goes() -> None:
    """Each subject the table says owes an entry is named, in order, with its category."""
    branch = Branch(
        [RelPath("tools/x.py")],
        [
            Prose("feat(python): a feature"),
            Prose("refactor(python): a shape"),
            Prose("fix(ci): a gate"),
            Prose("fix(go): a bug"),
        ],
        BASE,
    )
    assert owed(branch) == Owed(
        [],
        [
            OwedSubject(Prose("feat(python): a feature"), ADDED),
            OwedSubject(Prose("fix(go): a bug"), FIXED),
        ],
    )


def test_a_refused_subject_owes_nothing_and_is_named(
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A subject off the vocabulary owes no entry of its own; the refusal names it and why."""
    branch = Branch([], [Prose("style(python): a"), Prose("feat(python): fine")], BASE)
    assert owed(branch) == Owed([], [OwedSubject(Prose("feat(python): fine"), ADDED)])
    assert subjects_refused(branch)
    assert capsys.readouterr().err == (
        "check-changelog: FAIL — 'style(python): a': `style` is not a type: feat, fix, perf, "
        + "refactor, test, docs, ci, build, deps, chore, revert.\n"
    )


def test_subjects_in_the_vocabulary_are_not_refused(
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A branch whose every subject reads in the vocabulary has nothing refused, and is silent."""
    assert not subjects_refused(Branch([], [Prose("docs: a"), Prose("fix(tools): b")], BASE))
    assert capsys.readouterr().err == ""


# ── End-to-end of main(): a planted top level, the branch fed as data ────────


def _top_level(tmp_path: Path, changelog: Prose | BaseBytes, *, snapshot: bool) -> None:
    """Plant ``changelog`` as CHANGELOG.md under ``tmp_path``, and the snapshot when asked."""
    raw = changelog if isinstance(changelog, bytes) else changelog.encode("utf-8")
    _ = (tmp_path / CHANGELOG).write_bytes(raw)
    if snapshot:
        (tmp_path / "haskell-shim").mkdir()
        _ = (tmp_path / "haskell-shim" / "runtime-closure.snapshot").write_text(
            SNAPSHOT, encoding="utf-8"
        )


def _branch(path: RelPath, *subjects: Prose, changelog: bool = False) -> Branch:
    """Give the branch git lists: ``path`` changed under ``subjects``, CHANGELOG.md when asked."""
    changed = [CHANGELOG, path] if changelog else [path]
    return Branch(changed, list(subjects), BASE)


def _gate(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    branch: Branch,
    *,
    changelog: Prose | BaseBytes | None = None,
    snapshot: bool = True,
) -> ExitStatus:
    """Run ``main`` with ``tmp_path`` as its top level and ``branch`` as what it reads since main.

    ``toplevel`` and ``read_branch``, the gate's two readings of git, are each
    replaced by their answer, so the run starts no process.  CHANGELOG.md holds
    ``changelog``: by default the entry when the branch edits it, the empty
    section otherwise.
    """
    if changelog is None:
        changelog = ENTRY if CHANGELOG in branch.changed else UNRELEASED
    _top_level(tmp_path, changelog, snapshot=snapshot)

    def toplevel(_tool: Prose) -> Prose:
        return Prose(str(tmp_path))

    def read_branch(_tool: Prose, _base: Revision) -> Branch:
        return branch

    monkeypatch.setattr("tools.check_changelog.toplevel", toplevel)
    monkeypatch.setattr("tools.check_changelog.read_branch", read_branch)
    monkeypatch.setattr("sys.argv", ["check_changelog"])
    return main()


def _base_holds(monkeypatch: pytest.MonkeyPatch, base: Prose) -> None:
    """Give ``base`` as the CHANGELOG.md the branch's merge-base holds."""

    def base_changelog(_branch: Branch) -> Prose:
        return base

    monkeypatch.setattr("tools.check_changelog.base_changelog", base_changelog)


def _git_fails_at(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    step: GitStep,
    stderr: Prose,
    *,
    base: Revision = MAIN,
) -> ExitStatus:
    """Run ``main`` over a stand-in for git at ``run_capture``: ``step`` fails with ``stderr``.

    Every other step answers, and ``_git`` still reads the failure and writes
    the line naming the command.  ``base`` is the comparison ref the gate is given.
    """
    _top_level(tmp_path, UNRELEASED, snapshot=True)
    answers = {
        "rev-parse": Prose(f"{tmp_path}\n"),
        "merge-base": Prose(f"{BASE}\n"),
        "diff": Prose("tools/thing.py\n"),
        "log": Prose("fix(tools): a gate\n"),
    }

    def run_capture(cmd: list[GitArg]) -> subprocess.CompletedProcess[Prose]:
        if cmd[1] == step:
            return subprocess.CompletedProcess(cmd, 128, Prose(""), stderr)
        return subprocess.CompletedProcess(cmd, 0, answers[cmd[1]], Prose(""))

    monkeypatch.setattr("tools.commit_subjects.run_capture", run_capture)
    monkeypatch.setattr("sys.argv", ["check_changelog", base])
    return main()


# The one run over a git repository, the merge-commit test: its claim is git's own listing.


def _make_repo(tmp_path: Path) -> Path:
    """Init a repo with a ``main`` branch carrying a baseline commit."""
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-b", "main")
    (repo / "README.md").write_text("# base\n", encoding="utf-8")
    (repo / "CHANGELOG.md").write_text(UNRELEASED, encoding="utf-8")
    (repo / "haskell-shim").mkdir()
    (repo / "haskell-shim" / "runtime-closure.snapshot").write_text(SNAPSHOT, encoding="utf-8")
    commit(repo, "base")
    return repo


def _run_gate(repo: Path, monkeypatch: pytest.MonkeyPatch) -> ExitStatus:
    """Run ``check_changelog.main()`` from inside ``repo``, against its default base."""
    monkeypatch.chdir(repo)
    monkeypatch.setattr("sys.argv", ["check_changelog"])
    return main()


def _on_a_branch(repo: Path, path: RelPath, subject: Prose) -> None:
    """Commit, on a new branch, a change to ``path`` under ``subject``."""
    git(repo, "checkout", "-b", "feature")
    (repo / path).parent.mkdir(parents=True, exist_ok=True)
    (repo / path).write_text("x = 1\n", encoding="utf-8")
    commit(repo, subject)


def test_e2e_a_subject_owing_nothing_passes_without_a_changelog_edit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tooling fix owes no entry, so its branch passes without a CHANGELOG edit."""
    branch = _branch(RelPath("tools/thing.py"), Prose("fix(tools): a gate"))
    assert _gate(tmp_path, monkeypatch, branch) == 0


def test_e2e_a_subject_owing_nothing_fails_with_a_changelog_edit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A refactor owes no entry, so a branch that edits CHANGELOG.md under it fails."""
    branch = _branch(RelPath("cpp/src/thing.cpp"), Prose("refactor(cpp): tidy"), changelog=True)
    assert _gate(tmp_path, monkeypatch, branch) == 1
    assert capsys.readouterr().err == (
        "check-changelog: FAIL — the branch edits CHANGELOG.md, and no subject owes it an entry:\n"
        + "  refactor(cpp): tidy\n"
        + "An entry is owed by a feat, fix or perf on a shipped scope, a breaking mark, or a\n"
        + "changed public-surface record; relabel the change, or leave CHANGELOG.md alone.\n"
    )


SHAPE_FIX = Prose(
    "Cut it as docs/development/RELEASE.md says: the entries move under "
    + "'## [1.2.3] — YYYY-MM-DD', below an empty '## [Unreleased]', and nothing else changes."
)


def test_e2e_the_release_preparation_edits_the_changelog_owing_none(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The release preparation moves the unreleased entries under a version, owing none."""
    branch = _branch(RelPath("python/pyproject.toml"), RELEASE, changelog=True)
    _base_holds(monkeypatch, ENTRY)
    assert _gate(tmp_path, monkeypatch, branch, changelog=CUT) == 0
    assert capsys.readouterr().out == (
        "check-changelog: ok (the subjects since main read in the vocabulary, and CHANGELOG.md "
        + "is edited exactly when they owe it an entry, the release preparation apart)\n"
    )


def test_e2e_a_release_preparation_that_leaves_the_entries_unreleased_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A release preparation whose CHANGELOG keeps its entries unreleased is refused."""
    branch = _branch(RelPath("python/pyproject.toml"), RELEASE)
    _base_holds(monkeypatch, ENTRY)
    assert _gate(tmp_path, monkeypatch, branch, changelog=ENTRY) == 1
    assert capsys.readouterr().err == (
        "check-changelog: FAIL — the branch prepares release 1.2.3, and CHANGELOG.md is not "
        + f"empty under '## [Unreleased]'.\n{SHAPE_FIX}\n"
    )


def test_e2e_a_branch_preparing_two_releases_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A branch whose commits prepare two versions is refused, both named, and told to keep one."""
    branch = _branch(
        RelPath("python/pyproject.toml"), Prose("chore(dist): prepare v1.2.4"), RELEASE
    )
    assert _gate(tmp_path, monkeypatch, branch, changelog=ENTRY) == 1
    assert capsys.readouterr().err == (
        "check-changelog: FAIL — the branch prepares more than one release: 1.2.3, 1.2.4.\n"
        + "Keep one: reword or drop the earlier preparation commit, then force-push the re-signed "
        + "branch (git push --force-with-lease); never pull the old one back.\n"
    )


@pytest.mark.parametrize(
    "base",
    [None, BaseBytes(b"# Changelog\n\n## [Unreleased]\n\n\xff\n")],
    ids=["absent", "not-utf-8"],
)
def test_e2e_a_base_changelog_that_cannot_be_read_stops_the_gate(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    base: BaseBytes | None,
) -> None:
    """A release preparation is judged against the base's CHANGELOG; unread, the gate stops."""

    def run(
        cmd: list[GitArg], *, capture_output: bool, check: bool
    ) -> subprocess.CompletedProcess[BaseBytes]:
        assert capture_output
        assert not check
        assert cmd[1:] == [GitArg("show"), GitArg(f"{BASE}:{CHANGELOG}")]
        if base is None:
            refusal = BaseBytes(b"fatal: path 'CHANGELOG.md' does not exist in 'base'\n")
            return subprocess.CompletedProcess(cmd, 128, BaseBytes(b""), refusal)
        return subprocess.CompletedProcess(cmd, 0, base, BaseBytes(b""))

    monkeypatch.setattr("tools.check_changelog.subprocess", SimpleNamespace(run=run))
    branch = _branch(RelPath("python/pyproject.toml"), RELEASE, changelog=True)
    assert _gate(tmp_path, monkeypatch, branch, changelog=CUT) == 2
    assert capsys.readouterr().err.startswith(
        "check-changelog: FAIL — CHANGELOG.md cannot be read at the merge-base "
    )


OLDER = Prose("\n## [1.2.2] — 2026-01-01\n\n- **Old.** Kept.\n")
HEAD = "# Changelog\n\n## [Unreleased]\n\n"
# A preamble quoting a later version's heading and holding one deeper than a release's.
QUOTED = "# Changelog\n\n> ## [9.9.9] — 2026-01-01\n\n### [9.9.9] — 2026-01-01\n"


@pytest.mark.parametrize(
    ("changelog", "base"),
    [
        (CUT, ENTRY),
        (Prose(CUT + OLDER), Prose(ENTRY + OLDER)),
        (
            Prose(QUOTED + CUT_TAIL),
            Prose(QUOTED + ENTRY_TAIL),
        ),
        (
            Prose(HEAD + "## [1.2.3] — 2026-10-12\n### Fixed\n- **A bug.** Gone.\n"),
            Prose("# Changelog\n\n## [Unreleased]\n### Fixed\n- **A bug.** Gone.\n"),
        ),
        (
            Prose("# Change\u2028log\n" + CUT_TAIL),
            Prose("# Change\u2028log\n" + ENTRY_TAIL),
        ),
        (
            Prose(
                "# Changelog\n\n## [Unreleased]\n\t \n## [1.2.3] — 2026-10-12\n\n### Fixed\n\n"
                + "- **A bug.** Gone.\n"
            ),
            ENTRY,
        ),
    ],
    ids=[
        "cut",
        "older-release-kept",
        "quoted-and-deeper-are-no-release",
        "no-blank-under-the-headings",
        "line-separator-in-the-preamble",
        "tab-and-space-are-blank",
    ],
)
def test_a_release_cut_has_no_problem(changelog: Prose, base: Prose) -> None:
    """The base's unreleased lines under the dated heading, nothing else moved, is the cut."""
    assert cut_problem(changelog, base, VERSION) is None


_WANTED = "'## [1.2.3] — YYYY-MM-DD'"


@pytest.mark.parametrize(
    ("changelog", "found"),
    [
        (
            "# Changelog\n\n## [Unreleased]\n\n- **A bug.** Gone.\n\n## [1.2.3] — 2026-10-12\n",
            "is not empty under '## [Unreleased]'",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n- **A bug.** Gone.\n\n## [1.2.3] — 2026-10-12\n",
            "is not empty under '## [Unreleased]'",
        ),
        (
            HEAD + "[x]: https://example.com\n\n## [1.2.3] — 2026-10-12\n",
            "is not empty under '## [Unreleased]'",
        ),
        (
            HEAD + "\u00a0\n\n## [1.2.3] — 2026-10-12\n",
            "is not empty under '## [Unreleased]'",
        ),
        ("# Changelog\n\n## [Unreleased]\n", f"has no {_WANTED} heading after '## [Unreleased]'"),
        (
            "# Changelog\n\n## [Unreleased]\n\n# [1.2.3] — 2026-10-12\n",
            f"has no {_WANTED} heading after '## [Unreleased]'",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.2] — 2026-10-12\n",
            f"heads the section after '## [Unreleased]' '[1.2.2] — 2026-10-12', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3]\n",
            f"heads the section after '## [Unreleased]' '[1.2.3]', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] - 2026-10-12\n",
            f"heads the section after '## [Unreleased]' '[1.2.3] - 2026-10-12', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 20261012\n",
            f"heads the section after '## [Unreleased]' '[1.2.3] — 20261012', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [01.2.3] — 2026-10-12\n",
            f"heads the section after '## [Unreleased]' '[01.2.3] — 2026-10-12', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — \u0662\u0660\u0662\u0666-10-12\n",
            "heads the section after '## [Unreleased]' "
            + "'[1.2.3] — \u0662\u0660\u0662\u0666-10-12', not "
            + _WANTED,
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [Other]\n\n## [1.2.3] — 2026-10-12\n",
            f"heads the section after '## [Unreleased]' '[Other]', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-13-40\n",
            "dates release 1.2.3 '2026-13-40', which is not a calendar date",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n\n## [Unreleased]\n",
            "has 2 '## [Unreleased]' sections, not one",
        ),
        ("# Changelog\n", "has 0 '## [Unreleased]' sections, not one"),
    ],
    ids=[
        "entries-left",
        "entry-under-the-heading",
        "definition-left",
        "no-break-space-left",
        "no-heading",
        "level-one",
        "another-version",
        "undated",
        "hyphen",
        "basic-date",
        "leading-zero",
        "arabic-indic-date",
        "heading-between",
        "not-a-date",
        "two-unreleased",
        "no-unreleased",
    ],
)
def test_a_changelog_short_of_the_cut_says_how(changelog: Prose, found: Prose) -> None:
    """Each way a CHANGELOG falls short of the cut's shape is named, with the cut as the fix."""
    assert cut_problem(changelog, ENTRY, VERSION) == CutProblem(found, SHAPE_FIX)


_NEWER = "names release 1.2.3, not newer than the base's newest release, "
MOVED = Prose(
    "holds under release 1.2.3 other lines, or the same in another order, than the base's "
    + "'## [Unreleased]' held"
)
# Two older releases: by SemVer 1.2.10 is the newer, as text 1.2.9 is.
SEMVER = Prose(
    "\n## [1.2.10] — 2026-09-02\n\n- **Later.** Kept.\n"
    + "\n## [1.2.9] — 2026-09-01\n\n- **Old.** Kept.\n"
)


@pytest.mark.parametrize(
    ("changelog", "base", "problem"),
    [
        (
            Prose(HEAD + "## [1.2.3] — 2026-10-12\n\n### Fixed\n\n- **B.** b\n- **A.** a\n"),
            Prose(HEAD + "### Fixed\n\n- **A.** a\n- **B.** b\n"),
            CutProblem(MOVED, SHAPE_FIX),
        ),
        (
            Prose(HEAD + "## [1.2.3] — 2026-10-12\n\n### Added\n\n- **A.** a\n\n### Fixed\n\n"),
            Prose(HEAD + "### Added\n\n### Fixed\n\n- **A.** a\n\n"),
            CutProblem(MOVED, SHAPE_FIX),
        ),
        (
            Prose("# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n"),
            ENTRY,
            CutProblem(
                MOVED,
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "- **New.** Slipped in.\n"),
            ENTRY,
            CutProblem(
                MOVED,
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "\n## [1.2.2] — 2026-01-01\n\n- **Old.** Edited.\n"),
            Prose(ENTRY + OLDER),
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose("# Change log\n" + CUT_TAIL),
            ENTRY,
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(
                "# Changelog\n"
                + OLDER
                + "\n## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n\n"
                + "### Fixed\n\n- **A bug.** Gone.\n"
            ),
            Prose(ENTRY + OLDER),
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "\n## [1.2.4] — 2026-09-01\n\n- **Later.** Kept.\n" + OLDER),
            Prose(ENTRY + "\n## [1.2.4] — 2026-09-01\n\n- **Later.** Kept.\n" + OLDER),
            CutProblem(
                Prose(_NEWER + "1.2.4"),
                Prose(
                    "Prepare a version newer than 1.2.4, in the commit, the title and the heading."
                ),
            ),
        ),
        (
            Prose(
                "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-09-01\n\n- **A bug.** Gone.\n"
            ),
            Prose(
                "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-09-01\n\n- **A bug.** Gone.\n"
            ),
            CutProblem(
                Prose(_NEWER + "1.2.3"),
                Prose(
                    "Prepare a version newer than 1.2.3, in the commit, the title and the heading."
                ),
            ),
        ),
        (
            CUT,
            Prose(ENTRY + "\n## [Unreleased]\n"),
            CutProblem(
                Prose("is cut from a base with 2 '## [Unreleased]' sections, not one"),
                Prose("Merge the base's '## [Unreleased]' sections into one on main first."),
            ),
        ),
        (
            CUT,
            Prose("# Changelog\n"),
            CutProblem(
                Prose("is cut from a base with 0 '## [Unreleased]' sections, not one"),
                Prose("Merge the base's '## [Unreleased]' sections into one on main first."),
            ),
        ),
        (
            Prose(CUT + SEMVER),
            Prose(ENTRY + SEMVER),
            CutProblem(
                Prose(_NEWER + "1.2.10"),
                Prose(
                    "Prepare a version newer than 1.2.10, in the commit, the title and the heading."
                ),
            ),
        ),
        (
            Prose("# Changelog\n\n## [1.2.3] — 2026-10-12\n" + CUT_TAIL),
            ENTRY,
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "\n"),
            ENTRY,
            CutProblem(
                MOVED,
                SHAPE_FIX,
            ),
        ),
        (
            Prose(HEAD + "## [1.2.3] — 2026-10-12\n\n- a\n- b\u0085- c\n"),
            Prose(HEAD + "- a\u0085- b\n- c\n"),
            CutProblem(
                MOVED,
                SHAPE_FIX,
            ),
        ),
        (
            Prose("## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n\n- a\n\n# Changelog\n\n"),
            Prose("# Changelog\n\n## [Unreleased]\n\n- a\n"),
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(
                "# Changelog\n\n## [1.0.0] — 2026-01-01\n\n- old\n## [Unreleased]\n\n"
                + "## [1.2.3] — 2026-10-12\n\n- a\n- b\n"
            ),
            Prose(
                "# Changelog\n\n## [Unreleased]\n\n- a\n- b\n\n## [1.0.0] — 2026-01-01\n\n- old\n"
            ),
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "\n## [1.2.3] — 2026-01-01 and earlier\n\n- **Old.** Kept.\n"),
            Prose(ENTRY + "\n## [1.2.3] — 2026-01-01 and earlier\n\n- **Old.** Kept.\n"),
            CutProblem(
                Prose(_NEWER + "1.2.3"),
                Prose(
                    "Prepare a version newer than 1.2.3, in the commit, the title and the heading."
                ),
            ),
        ),
    ],
    ids=[
        "entries-reordered",
        "entry-moved-to-another-category",
        "entries-dropped",
        "entry-added",
        "older-release-edited",
        "preamble-edited",
        "unreleased-below-older",
        "not-newer",
        "already-released",
        "base-two-unreleased",
        "base-no-unreleased",
        "semver-order",
        "release-heading-also-above",
        "blank-line-added",
        "entry-boundary-moved-across-a-next-line",
        "title-moved-below-the-release",
        "release-placed-below-an-older-one",
        "older-heading-in-another-form",
    ],
)
def test_a_cut_that_differs_from_its_base_says_how(
    changelog: Prose, base: Prose, problem: CutProblem
) -> None:
    """Against the base, the cut moves exactly its unreleased lines, and to a newer version."""
    assert cut_problem(changelog, base, VERSION) == problem


def test_e2e_a_subject_owing_an_entry_fails_without_one(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A shipped fix with no CHANGELOG edit fails the gate, which names it and the category."""
    branch = _branch(RelPath("python/aletheia/thing.py"), Prose("fix(python): a bug"))
    assert _gate(tmp_path, monkeypatch, branch) == 1
    err = capsys.readouterr().err
    assert "  fix(python): a bug: owes ### Fixed\n" in err
    assert err.endswith("however intricate the change; the detail belongs to the commit message.\n")


def test_e2e_a_subject_owing_an_entry_passes_with_one(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The same shipped fix passes once the branch edits CHANGELOG.md."""
    branch = _branch(
        RelPath("python/aletheia/thing.py"), Prose("fix(python): a bug"), changelog=True
    )
    assert _gate(tmp_path, monkeypatch, branch) == 0


def test_e2e_a_refused_subject_fails_even_with_an_entry(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A subject off the vocabulary fails the gate whatever else the branch carries."""
    branch = _branch(RelPath("tools/thing.py"), Prose("Tidy the tools"), changelog=True)
    assert _gate(tmp_path, monkeypatch, branch) == 1
    assert "'Tidy the tools': it does not read `type(scope)!: text`.\n" in capsys.readouterr().err


def test_e2e_a_surface_record_changed_without_a_changelog_edit_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A branch moving the feature matrix with no CHANGELOG edit fails, naming the record."""
    branch = _branch(RelPath("docs/FEATURE_MATRIX.yaml"), Prose("refactor: move a row"))
    assert _gate(tmp_path, monkeypatch, branch) == 1
    assert "  changes the public-surface record docs/FEATURE_MATRIX.yaml\n" in (
        capsys.readouterr().err
    )


def test_e2e_a_surface_record_changed_with_an_entry_passes_under_an_internal_subject(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The record owes the entry, so the branch edits the CHANGELOG whatever its subject says."""
    branch = _branch(
        RelPath("docs/FEATURE_MATRIX.yaml"), Prose("refactor: move a row"), changelog=True
    )
    assert _gate(tmp_path, monkeypatch, branch) == 0


def test_e2e_a_merge_commit_is_no_subject_of_the_branch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A branch brought up to date with a merge git wrote passes on its own subjects."""
    repo = _make_repo(tmp_path)
    _on_a_branch(repo, RelPath("tools/thing.py"), Prose("ci(tools): a step"))
    git(repo, "checkout", "main")
    (repo / "README.md").write_text("# moved\n", encoding="utf-8")
    commit(repo, "docs: move the readme")
    git(repo, "checkout", "feature")
    merge(repo, Revision("main"))
    assert _run_gate(repo, monkeypatch) == 0


@pytest.mark.parametrize(
    "path", [RelPath("python/aletheia/thing.py"), RelPath("src/Aletheia/Main.agda")]
)
def test_e2e_shipped_files_under_an_internal_label_fail(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    path: RelPath,
) -> None:
    """A binding file, or a kernel module the closure compiles, under a tooling label fails."""
    assert _gate(tmp_path, monkeypatch, _branch(path, Prose("fix(tools): a gate"))) == 1
    assert capsys.readouterr().err == (
        "check-changelog: FAIL — the branch changes what users get, and every subject names "
        + f"an internal scope:\n  {path}\nName the shipped scope the change is in: cli, cpp, "
        + "dist, excel, ffi, go, kernel, python, rust.\n"
    )


def test_e2e_a_proof_module_under_an_internal_label_passes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A kernel module outside the runtime closure ships nothing, so a proofs label fits it."""
    branch = _branch(RelPath("src/Aletheia/Main/Properties.agda"), Prose("refactor(proofs): a"))
    assert _gate(tmp_path, monkeypatch, branch) == 0


def test_e2e_an_unreadable_snapshot_stops_the_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without the runtime-closure snapshot the kernel's shipped files are unknown: exit 2."""
    assert _gate(tmp_path, monkeypatch, Branch([], [], BASE), snapshot=False) == 2
    err = capsys.readouterr().err
    assert err.startswith("check-changelog: FAIL — ")
    assert "runtime-closure.snapshot cannot be read: " in err


def test_e2e_without_the_comparison_ref_the_branch_cannot_be_read(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A comparison ref git cannot resolve stops the gate with exit 2, naming the command."""
    refusal = Prose("fatal: Not a valid object name no-such-ref\n")
    base = Revision("no-such-ref")
    assert _git_fails_at(tmp_path, monkeypatch, "merge-base", refusal, base=base) == 2
    assert capsys.readouterr().err.startswith(
        "check-changelog: git merge-base HEAD no-such-ref failed\n"
    )


def test_e2e_a_branch_whose_files_git_cannot_list_stops_the_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A ``git diff`` that fails after the merge-base is found stops the gate with exit 2."""
    refusal = Prose("fatal: bad boolean config value 'bogus' for 'diff.renames'\n")
    assert _git_fails_at(tmp_path, monkeypatch, "diff", refusal) == 2
    err = capsys.readouterr().err
    assert "check-changelog: git diff --name-only " in err
    assert "bad boolean config value 'bogus' for 'diff.renames'" in err


def test_e2e_a_branch_whose_subjects_git_cannot_list_stops_the_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A ``git log`` that fails after the files are listed stops the gate with exit 2."""
    refusal = Prose("fatal: unknown date format bogus\n")
    assert _git_fails_at(tmp_path, monkeypatch, "log", refusal) == 2
    assert "check-changelog: git log --no-merges --format=%s " in capsys.readouterr().err


def test_e2e_outside_a_repository_the_changelog_cannot_be_found(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no repository to name a top level, the gate stops with exit 2 and says why."""
    refusal = Prose("fatal: not a git repository (or any of the parent directories): .git\n")
    assert _git_fails_at(tmp_path, monkeypatch, "rev-parse", refusal) == 2
    err = capsys.readouterr().err
    assert err.startswith("check-changelog: git rev-parse --show-toplevel failed\n")
    assert err.count("check-changelog:") == 1


def test_e2e_a_repeated_category_header_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Two ``### Changed`` under Unreleased fail."""
    changelog = Prose(
        "# Changelog\n\n## [Unreleased]\n\n### Changed\n\n- one\n\n### Fixed\n\n- two\n\n"
        + "### Changed\n\n- three\n\n## [1.0.0]\n\n### Changed\n\n- released\n"
    )
    assert _gate(tmp_path, monkeypatch, Branch([], [], BASE), changelog=changelog) == 1
    assert "### Changed" in capsys.readouterr().err


def test_e2e_a_header_outside_the_categories_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A ``### Improved`` under Unreleased is refused and named."""
    changelog = Prose(
        "# Changelog\n\n## [Unreleased]\n\n### Improved\n\n- one\n\n"
        + "## [1.0.0]\n\n### Changed\n\n- x\n"
    )
    assert _gate(tmp_path, monkeypatch, Branch([], [], BASE), changelog=changelog) == 1
    assert "### Improved" in capsys.readouterr().err


def test_e2e_one_header_per_category_passes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A header repeated only in a released section is not the Unreleased one."""
    changelog = Prose(
        "# Changelog\n\n## [Unreleased]\n\n### Changed\n\n- one\n\n### Fixed\n\n- two\n\n"
        + "## [1.0.0]\n\n### Changed\n\n- released\n"
    )
    assert _gate(tmp_path, monkeypatch, Branch([], [], BASE), changelog=changelog) == 0


def test_unreleased_headers_are_the_level_three_headings_of_the_section() -> None:
    """A heading-shaped line in code is neither a header nor the section's end."""
    changelog = (
        "# Changelog\n\n## [Unreleased]\n\n### Added\n\n- x\n\n```\n### Added\n## [9.0.0]\n```\n\n"
        + "### Fixed\n\n- y\n\n### Fixed\n\n#### Fixed\n\n## [1.0.0]\n\n### Bogus\n"
    )
    assert unreleased_headers(changelog) == UnreleasedHeaders([Category.FIXED], [])


def test_a_header_word_outside_the_categories_is_named() -> None:
    """A level-three heading in the section is its category, whole, so more words are not one."""
    changelog = "## [Unreleased]\n\n### Bogus words\n\n### Added\n"
    assert unreleased_headers(changelog) == UnreleasedHeaders([], ["Bogus words"])


@pytest.mark.parametrize(
    "changelog",
    [
        Prose("# Changelog\n\n### Added\n"),
        Prose("## \\[Unreleased\\]\n\n### Added\n"),
        Prose("> ## [Unreleased]\n"),
    ],
    ids=["none", "escaped-brackets", "quoted"],
)
def test_a_changelog_without_the_section_is_missing_it(changelog: Prose) -> None:
    """No top-level heading written ``[Unreleased]`` at level two: the section is missing."""
    assert unreleased_headers(changelog) == UnreleasedHeaders([], [], missing=True)


def test_a_missing_section_is_refused(capsys: pytest.CaptureFixture[Prose]) -> None:
    """The gate names the section it could not find, and refuses."""
    assert headers_refused(UnreleasedHeaders([], [], missing=True))
    assert capsys.readouterr().err == (
        "check-changelog: FAIL — CHANGELOG.md has no '## [Unreleased]' section.\n"
    )


@pytest.mark.parametrize(
    ("changelog", "expected"),
    [
        (
            Prose("## [Unreleased]\n\n### Added\n\n#### Added\n"),
            UnreleasedHeaders([], []),
        ),
        (Prose("## [Unreleased]\n### Bogus\n"), UnreleasedHeaders([], ["Bogus"])),
        (Prose("## [Unreleased]\n\n###\n"), UnreleasedHeaders([], [""])),
    ],
    ids=["deeper-heading", "header-on-the-first-line", "empty-header"],
)
def test_a_header_is_a_level_three_heading_anywhere_in_the_section(
    changelog: Prose, expected: UnreleasedHeaders
) -> None:
    """A deeper heading is no header; one under the section's heading is; an empty one is named."""
    assert unreleased_headers(changelog) == expected


@pytest.mark.parametrize(
    ("changelog", "expected"),
    [
        (
            Prose("> ## [Unreleased]\n\n## [Unreleased]\n\n### Fixed\n\n### Fixed\n"),
            UnreleasedHeaders([Category.FIXED], []),
        ),
        (
            Prose("## [Unreleased]\n\n### Added\n\n## [Unreleased]\n\n### Added\n"),
            UnreleasedHeaders([Category.ADDED], []),
        ),
        (Prose("## [Unreleased]\n\n### &#70;ixed\n"), UnreleasedHeaders([], [])),
        (Prose("## [Unreleased]\n\n### Added\n\n> ### Added\n"), UnreleasedHeaders([], [])),
    ],
    ids=[
        "quoted-unreleased-first",
        "two-unreleased-sections",
        "entity-in-the-word",
        "quoted-header",
    ],
)
def test_the_section_is_every_top_level_unreleased_heading_and_its_headers_top_level(
    changelog: Prose, expected: UnreleasedHeaders
) -> None:
    """A quoted heading opens no section and is no header; every top-level section is read."""
    assert unreleased_headers(changelog) == expected


@pytest.mark.parametrize(
    ("header", "word"),
    [(Prose("Fixed bugs"), Prose("Fixed bugs")), (Prose("~~Fixed~~ Added"), Prose("Fixed Added"))],
    ids=["more-words", "struck-out-word"],
)
def test_a_header_is_its_whole_text(header: Prose, word: Prose) -> None:
    """A header carries its category and nothing else, as it reads."""
    changelog = Prose(f"## [Unreleased]\n\n### {header}\n")
    assert unreleased_headers(changelog) == UnreleasedHeaders([], [word])


def test_e2e_a_changelog_that_is_not_utf8_cannot_be_checked(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A CHANGELOG.md the gate cannot read as UTF-8 stops it with exit 2, naming the file."""
    garbled = BaseBytes(b"# Changelog\n\n## [Unreleased]\n\xff\n")
    assert _gate(tmp_path, monkeypatch, Branch([], [], BASE), changelog=garbled) == 2
    err = capsys.readouterr().err
    assert err.startswith("check-changelog: FAIL — ")
    assert "CHANGELOG.md cannot be read: " in err
    assert err.endswith("\n")
