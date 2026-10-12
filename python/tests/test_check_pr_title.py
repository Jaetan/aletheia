# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_pr_title`` — a pull request's title against the vocabulary.

End to end in a throwaway git repo: a title off the vocabulary fails before
git is asked anything; a title naming an internal scope fails on a branch that
changes what users get; a title owing an entry passes only when the branch
edits ``CHANGELOG.md``; git that cannot read the branch, or a missing
runtime-closure snapshot, stops the check with exit 2.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import commit, git

from tools._common import RelPath
from tools.check_pr_title import main

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

SHIPPED = RelPath("go/aletheia/x.go")
TOOLING = RelPath("tools/x.py")


def _repo(tmp_path: Path, path: RelPath, *, changelog: bool) -> Path:
    """Make a repo whose ``feature`` branch changes ``path``, and the CHANGELOG when asked."""
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-b", "main")
    (repo / "CHANGELOG.md").write_text("# Changelog\n\n## [Unreleased]\n", encoding="utf-8")
    (repo / "haskell-shim").mkdir()
    (repo / "haskell-shim" / "runtime-closure.snapshot").write_text(
        "MAlonzo.Code.Aletheia.Main\n", encoding="utf-8"
    )
    commit(repo, "base")
    git(repo, "checkout", "-b", "feature")
    (repo / path).parent.mkdir(parents=True, exist_ok=True)
    (repo / path).write_text("x\n", encoding="utf-8")
    if changelog:
        (repo / "CHANGELOG.md").write_text(
            "# Changelog\n\n## [Unreleased]\n\n### Fixed\n\n- **A bug.** Gone.\n",
            encoding="utf-8",
        )
    commit(repo, "fix(go): a bug")
    return repo


def _check(repo: Path, monkeypatch: pytest.MonkeyPatch, *argv: Prose) -> ExitStatus:
    """Run ``check_pr_title.main()`` from inside ``repo`` with ``argv``."""
    monkeypatch.chdir(repo)
    monkeypatch.setattr("sys.argv", ["check_pr_title", *argv])
    return main()


def test_a_title_off_the_vocabulary_fails_before_git_is_asked(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A title the vocabulary refuses fails, quoting the title and the reason, whatever the ref."""
    repo = _repo(tmp_path, SHIPPED, changelog=True)
    assert _check(repo, monkeypatch, Prose("Fix the Go loader"), Prose("no-such-ref")) == 1
    assert capsys.readouterr().err == (
        "check-pr-title: FAIL — 'Fix the Go loader': it does not read `type(scope)!: text`.\n"
    )


@pytest.mark.parametrize("title", [Prose("--help"), Prose("-h")])
def test_a_title_that_reads_as_an_option_is_held_to_the_vocabulary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    title: Prose,
) -> None:
    """After ``--``, as the workflow passes it, a title spelled like an option is a title."""
    repo = _repo(tmp_path, SHIPPED, changelog=True)
    assert _check(repo, monkeypatch, Prose("--"), title) == 1
    assert capsys.readouterr().err == (
        f"check-pr-title: FAIL — {title!r}: it does not read `type(scope)!: text`.\n"
    )


def test_a_title_owing_nothing_on_tooling_passes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A tooling title on a branch that ships nothing owes no entry, and passes."""
    repo = _repo(tmp_path, TOOLING, changelog=False)
    assert _check(repo, monkeypatch, Prose("ci(tools): a step")) == 0
    assert capsys.readouterr().out == (
        "check-pr-title: ok ('ci(tools): a step' reads in the vocabulary and owes no entry)\n"
    )


def test_an_internal_title_on_shipped_files_fails_and_names_them(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A tooling title on a branch that changes a binding fails, naming the shipped file."""
    repo = _repo(tmp_path, SHIPPED, changelog=True)
    assert _check(repo, monkeypatch, Prose("ci(tools): a step")) == 1
    assert capsys.readouterr().err == (
        "check-pr-title: FAIL — 'ci(tools): a step' names an internal scope, and the branch "
        + "changes what users get: go/aletheia/x.go.\n"
    )


@pytest.mark.parametrize(
    ("path", "expected"),
    [
        (RelPath("src/Aletheia/Main.agda"), ExitStatus(1)),
        (RelPath("src/Aletheia/Main/Properties.agda"), ExitStatus(0)),
    ],
    ids=["compiled-module", "proof-module"],
)
def test_a_proofs_title_fits_a_proof_module_and_not_a_compiled_one(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    path: RelPath,
    expected: ExitStatus,
) -> None:
    """The kernel ships the modules the runtime closure compiles, and no proof module."""
    repo = _repo(tmp_path, path, changelog=False)
    assert _check(repo, monkeypatch, Prose("refactor(proofs): a proof")) == expected


def test_a_title_owing_an_entry_fails_when_the_branch_leaves_the_changelog(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A shipped fix's title on a branch with no CHANGELOG edit fails, naming the category."""
    repo = _repo(tmp_path, SHIPPED, changelog=False)
    assert _check(repo, monkeypatch, Prose("fix(go): a bug")) == 1
    assert capsys.readouterr().err == (
        "check-pr-title: FAIL — 'fix(go): a bug' owes ### Fixed, and the branch leaves "
        + "CHANGELOG.md alone.\n"
    )


def test_a_title_owing_an_entry_passes_when_the_branch_edits_the_changelog(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """The same title passes on a branch that edits CHANGELOG.md."""
    repo = _repo(tmp_path, SHIPPED, changelog=True)
    assert _check(repo, monkeypatch, Prose("fix(go): a bug")) == 0
    assert capsys.readouterr().out == (
        "check-pr-title: ok ('fix(go): a bug' owes ### Fixed; the branch edits CHANGELOG.md)\n"
    )


def test_a_title_owing_nothing_fails_when_the_branch_edits_the_changelog(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A tooling title owes no entry, so a branch that edits CHANGELOG.md under it fails."""
    repo = _repo(tmp_path, TOOLING, changelog=True)
    assert _check(repo, monkeypatch, Prose("ci(tools): a step")) == 1
    assert capsys.readouterr().err == (
        "check-pr-title: FAIL — 'ci(tools): a step' owes no entry, and the branch edits "
        + "CHANGELOG.md.\nRelabel the change, or leave CHANGELOG.md alone.\n"
    )


def test_the_release_title_edits_the_changelog_owing_none(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """The release preparation's title passes with the CHANGELOG edit it exists to make."""
    repo = _repo(tmp_path, TOOLING, changelog=True)
    assert _check(repo, monkeypatch, Prose("chore(dist): prepare v1.2.3")) == 0
    assert capsys.readouterr().out == (
        "check-pr-title: ok ('chore(dist): prepare v1.2.3' cuts a release; the branch edits "
        + "CHANGELOG.md)\n"
    )


def test_the_release_title_claims_no_edit_the_branch_leaves_out(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """The release title on a branch that leaves the CHANGELOG alone reads as owing none."""
    repo = _repo(tmp_path, TOOLING, changelog=False)
    assert _check(repo, monkeypatch, Prose("chore(dist): prepare v1.2.3")) == 0
    assert capsys.readouterr().out == (
        "check-pr-title: ok ('chore(dist): prepare v1.2.3' reads in the vocabulary and owes "
        + "no entry)\n"
    )


def test_a_title_is_read_whatever_the_commits_say(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The title decides what it owes: a breaking title owes an entry the commit would not."""
    repo = _repo(tmp_path, TOOLING, changelog=False)
    assert _check(repo, monkeypatch, Prose("refactor(tools)!: a break")) == 1


def test_a_branch_git_cannot_read_stops_the_check(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A title in the vocabulary against a ref git cannot resolve stops the check with exit 2."""
    repo = _repo(tmp_path, SHIPPED, changelog=True)
    assert _check(repo, monkeypatch, Prose("fix(go): a bug"), Prose("no-such-ref")) == 2
    assert capsys.readouterr().err.startswith(
        "check-pr-title: git merge-base HEAD no-such-ref failed\n"
    )


def test_an_unreadable_snapshot_stops_the_check(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """Without the runtime-closure snapshot the kernel's shipped files are unknown: exit 2."""
    repo = _repo(tmp_path, SHIPPED, changelog=True)
    (repo / "haskell-shim" / "runtime-closure.snapshot").unlink()
    assert _check(repo, monkeypatch, Prose("fix(go): a bug")) == 2
    err = capsys.readouterr().err
    assert err.startswith("check-pr-title: FAIL — ")
    assert "runtime-closure.snapshot cannot be read: " in err


def test_outside_a_repository_the_check_stops(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """With no repository to name a top level, the check stops with exit 2 and says why."""
    outside = tmp_path / "outside"
    outside.mkdir()
    monkeypatch.setenv("GIT_CEILING_DIRECTORIES", str(tmp_path))
    assert _check(outside, monkeypatch, Prose("fix(go): a bug")) == 2
    err = capsys.readouterr().err
    assert err.startswith("check-pr-title: git rev-parse --show-toplevel failed\n")
    assert err.count("check-pr-title:") == 1
