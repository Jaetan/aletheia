# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_changelog``: a branch's subjects, the entries they owe, the section.

Three layers:

* ``owed`` / ``subjects_refused`` — the pure reading of a branch: the surface
  records it changed and the subjects owing an entry by the vocabulary's table,
  and every subject the vocabulary refuses (the table itself is
  ``test_commit_subjects``'s).
* ``unreleased_headers`` / ``headers_refused`` — the pure audit of the section's
  ``###`` headers, read as CommonMark.
* ``main`` — a hermetic end-to-end run in a throwaway git repo: a refused
  subject fails; a subject owing an entry, or a surface record changed, fails
  without a CHANGELOG edit and passes with one; anything else passes without
  one; a merge commit is no subject of the branch's; git that cannot answer
  stops the gate with exit 2.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import commit, git

from tools._common import RelPath
from tools.check_changelog import (
    SURFACE_RECORDS,
    Category,
    Owed,
    OwedSubject,
    UnreleasedHeaders,
    headers_refused,
    main,
    owed,
    subjects_refused,
    unreleased_headers,
)
from tools.commit_subjects import Branch

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

ADDED = Prose("### Added")
FIXED = Prose("### Fixed")


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
    assert owed(Branch([RelPath("tools/x.py"), record], [])) == Owed([record], [])


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
    branch = Branch([], [Prose("style(python): a"), Prose("feat(python): fine")])
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
    assert not subjects_refused(Branch([], [Prose("docs: a"), Prose("fix(tools): b")]))
    assert capsys.readouterr().err == ""


# ── Hermetic end-to-end of main() in a throwaway git repo ──────────────────


def _make_repo(tmp_path: Path) -> Path:
    """Init a repo with a ``main`` branch carrying a baseline commit."""
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-b", "main")
    (repo / "README.md").write_text("# base\n", encoding="utf-8")
    (repo / "CHANGELOG.md").write_text("# Changelog\n\n## [Unreleased]\n", encoding="utf-8")
    (repo / "haskell-shim").mkdir()
    (repo / "haskell-shim" / "runtime-closure.snapshot").write_text(
        "MAlonzo.Code.Aletheia.Main\nMAlonzo.Code.Data.Nat.Base\n", encoding="utf-8"
    )
    commit(repo, "base")
    return repo


def _run_gate(repo: Path, monkeypatch: pytest.MonkeyPatch) -> ExitStatus:
    """Run ``check_changelog.main()`` from inside ``repo``, against its default base."""
    monkeypatch.chdir(repo)
    monkeypatch.setattr("sys.argv", ["check_changelog"])
    return main()


def _on_a_branch(repo: Path, path: RelPath, subject: Prose, *, changelog: bool = False) -> None:
    """Commit, on a new branch, a change to ``path`` under ``subject``, and an entry when asked."""
    git(repo, "checkout", "-b", "feature")
    (repo / path).parent.mkdir(parents=True, exist_ok=True)
    (repo / path).write_text("x = 1\n", encoding="utf-8")
    if changelog:
        (repo / "CHANGELOG.md").write_text(
            "# Changelog\n\n## [Unreleased]\n\n### Fixed\n\n- **A bug.** Gone.\n",
            encoding="utf-8",
        )
    commit(repo, subject)


def test_e2e_a_subject_owing_nothing_passes_without_a_changelog_edit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A tooling fix owes no entry, so its branch passes without a CHANGELOG edit."""
    repo = _make_repo(tmp_path)
    _on_a_branch(repo, RelPath("tools/thing.py"), Prose("fix(tools): a gate"))
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_a_subject_owing_an_entry_fails_without_one(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A shipped fix with no CHANGELOG edit fails the gate, which names it and the category."""
    repo = _make_repo(tmp_path)
    _on_a_branch(repo, RelPath("python/aletheia/thing.py"), Prose("fix(python): a bug"))
    assert _run_gate(repo, monkeypatch) == 1
    err = capsys.readouterr().err
    assert "  fix(python): a bug: owes ### Fixed\n" in err
    assert err.endswith("however intricate the change; the detail belongs to the commit message.\n")


def test_e2e_a_subject_owing_an_entry_passes_with_one(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The same shipped fix passes once the branch edits CHANGELOG.md."""
    repo = _make_repo(tmp_path)
    _on_a_branch(
        repo, RelPath("python/aletheia/thing.py"), Prose("fix(python): a bug"), changelog=True
    )
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_a_refused_subject_fails_even_with_an_entry(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A subject off the vocabulary fails the gate whatever else the branch carries."""
    repo = _make_repo(tmp_path)
    _on_a_branch(repo, RelPath("tools/thing.py"), Prose("Tidy the tools"), changelog=True)
    assert _run_gate(repo, monkeypatch) == 1
    assert "'Tidy the tools': it does not read `type(scope)!: text`.\n" in capsys.readouterr().err


def test_e2e_a_surface_record_changed_without_a_changelog_edit_fails(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A branch moving the feature matrix with no CHANGELOG edit fails, naming the record."""
    repo = _make_repo(tmp_path)
    _on_a_branch(repo, RelPath("docs/FEATURE_MATRIX.yaml"), Prose("refactor: move a row"))
    assert _run_gate(repo, monkeypatch) == 1
    assert "  changes the public-surface record docs/FEATURE_MATRIX.yaml\n" in (
        capsys.readouterr().err
    )


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
    git(repo, "merge", "--no-ff", "--no-edit", "main")
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
    repo = _make_repo(tmp_path)
    _on_a_branch(repo, path, Prose("fix(tools): a gate"))
    assert _run_gate(repo, monkeypatch) == 1
    assert capsys.readouterr().err == (
        "check-changelog: FAIL — the branch changes what users get, and every subject names "
        + f"an internal scope:\n  {path}\nName the shipped scope the change is in: cli, cpp, "
        + "dist, excel, ffi, go, kernel, python, rust.\n"
    )


def test_e2e_a_proof_module_under_an_internal_label_passes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A kernel module outside the runtime closure ships nothing, so a proofs label fits it."""
    repo = _make_repo(tmp_path)
    _on_a_branch(repo, RelPath("src/Aletheia/Main/Properties.agda"), Prose("refactor(proofs): a"))
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_an_unreadable_snapshot_stops_the_gate(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """Without the runtime-closure snapshot the kernel's shipped files are unknown: exit 2."""
    repo = _make_repo(tmp_path)
    (repo / "haskell-shim" / "runtime-closure.snapshot").unlink()
    assert _run_gate(repo, monkeypatch) == 2
    err = capsys.readouterr().err
    assert err.startswith("check-changelog: FAIL — ")
    assert "runtime-closure.snapshot cannot be read: " in err


def test_e2e_without_the_comparison_ref_the_branch_cannot_be_read(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A comparison ref git cannot resolve stops the gate with exit 2, naming the command."""
    repo = _make_repo(tmp_path)
    monkeypatch.chdir(repo)
    monkeypatch.setattr("sys.argv", ["check_changelog", "no-such-ref"])
    assert main() == 2
    assert capsys.readouterr().err.startswith(
        "check-changelog: git merge-base HEAD no-such-ref failed\n"
    )


def test_e2e_a_branch_whose_files_git_cannot_list_stops_the_gate(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A ``git diff`` that fails after the merge-base is found stops the gate with exit 2."""
    repo = _make_repo(tmp_path)
    git(repo, "config", "diff.renames", "bogus")
    assert _run_gate(repo, monkeypatch) == 2
    err = capsys.readouterr().err
    assert "check-changelog: git diff --name-only " in err
    assert "bad boolean config value 'bogus' for 'diff.renames'" in err


def test_e2e_a_branch_whose_subjects_git_cannot_list_stops_the_gate(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A ``git log`` that fails after the files are listed stops the gate with exit 2."""
    repo = _make_repo(tmp_path)
    git(repo, "config", "log.date", "bogus")
    assert _run_gate(repo, monkeypatch) == 2
    assert "check-changelog: git log --no-merges --format=%s " in capsys.readouterr().err


def test_e2e_outside_a_repository_the_changelog_cannot_be_found(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """With no repository to name a top level, the gate stops with exit 2 and says why."""
    outside = tmp_path / "outside"
    outside.mkdir()
    monkeypatch.setenv("GIT_CEILING_DIRECTORIES", str(tmp_path))
    assert _run_gate(outside, monkeypatch) == 2
    err = capsys.readouterr().err
    assert err.startswith("check-changelog: git rev-parse --show-toplevel failed\n")
    assert err.count("check-changelog:") == 1


def test_e2e_a_repeated_category_header_fails(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """Two ``### Changed`` under Unreleased fail."""
    repo = _make_repo(tmp_path)
    (repo / "CHANGELOG.md").write_text(
        "# Changelog\n\n## [Unreleased]\n\n### Changed\n\n- one\n\n### Fixed\n\n- two\n\n"
        + "### Changed\n\n- three\n\n## [1.0.0]\n\n### Changed\n\n- released\n",
        encoding="utf-8",
    )
    commit(repo, "split the header")
    assert _run_gate(repo, monkeypatch) == 1
    assert "### Changed" in capsys.readouterr().err


def test_e2e_a_header_outside_the_categories_fails(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A ``### Improved`` under Unreleased is refused and named."""
    repo = _make_repo(tmp_path)
    (repo / "CHANGELOG.md").write_text(
        "# Changelog\n\n## [Unreleased]\n\n### Improved\n\n- one\n\n"
        + "## [1.0.0]\n\n### Changed\n\n- x\n",
        encoding="utf-8",
    )
    commit(repo, "a header of its own")
    assert _run_gate(repo, monkeypatch) == 1
    assert "### Improved" in capsys.readouterr().err


def test_e2e_one_header_per_category_passes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A header repeated only in a released section is not the Unreleased one."""
    repo = _make_repo(tmp_path)
    (repo / "CHANGELOG.md").write_text(
        "# Changelog\n\n## [Unreleased]\n\n### Changed\n\n- one\n\n### Fixed\n\n- two\n\n"
        + "## [1.0.0]\n\n### Changed\n\n- released\n",
        encoding="utf-8",
    )
    commit(repo, "one header each")
    assert _run_gate(repo, monkeypatch) == 0


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
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A CHANGELOG.md the gate cannot read as UTF-8 stops it with exit 2, naming the file."""
    repo = _make_repo(tmp_path)
    (repo / "CHANGELOG.md").write_bytes(b"# Changelog\n\n## [Unreleased]\n\xff\n")
    commit(repo, "garble the changelog")
    assert _run_gate(repo, monkeypatch) == 2
    err = capsys.readouterr().err
    assert err.startswith("check-changelog: FAIL — ")
    assert "CHANGELOG.md cannot be read: " in err
    assert err.endswith("\n")
