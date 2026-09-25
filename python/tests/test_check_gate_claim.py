# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_gate_claim`` — the gate guarding gate-clean claims.

Two layers:

* the build-source digest — the key a sweep's record is filed under.  It is
  content identity: a checkout that rewrites every mtime leaves it unchanged,
  a one-byte edit to a build-relevant file moves it, and the working tree of a
  clean checkout digests to its commit.
* ``main`` — a hermetic end-to-end run in a throwaway git repo, every
  polarity: no claim passes; a claim over a doc-only commit passes; a claim
  over a build-relevant commit fails with no record, passes when the running
  sweep exports the commit's digest, fails when it exports another, passes
  when a finished log records the digest with a passing summary, and fails
  when the log failed or is a fast-tier log that recorded no digest.
"""

from __future__ import annotations

import os
from typing import TYPE_CHECKING

from _git_repo import commit, git

from tools.check_gate_claim import (
    LOG_DIR,
    PASSED_LINE,
    SOURCES_ENV,
    SOURCES_LINE,
    SOURCES_UNRECORDED,
    evidence_for,
    main,
    sources_digest_of_revision,
    sources_digest_of_worktree,
)

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

CLAIM = "feat: widen the parser\n\nAll gates clean.\n"


def _make_repo(tmp_path: Path) -> Path:
    """Init a repo carrying one Agda module and one document, committed."""
    repo = tmp_path / "repo"
    (repo / "src").mkdir(parents=True)
    (repo / "src" / "A.agda").write_text("module A where\n", encoding="utf-8")
    (repo / "README.md").write_text("# base\n", encoding="utf-8")
    git(repo, "init", "-q", "-b", "main")
    _ = commit(repo, "base")
    return repo


def _write_log(repo: Path, name: str, sources: str, *, passed: bool) -> None:
    """Write a sweep log in the shape the orchestrator leaves behind."""
    log_dir = repo / LOG_DIR
    log_dir.mkdir(parents=True, exist_ok=True)
    verdict = (
        "Result:   ALL 3 STEPS PASSED" if passed else "═══ CI FAILED — 1 step(s) failed: x ═══"
    )
    _ = (log_dir / name).write_text(
        "═══ Aletheia offline CI sweep ═══\n"
        + "Branch:   main\n"
        + f"{SOURCES_LINE}{sources}\n"
        + "Steps:    3\n"
        + "─── build (0s) ───\n"
        + "  ✓ build (0s)\n"
        + "═══ CI summary ═══\n"
        + f"{verdict}\n"
        + "Duration: 1s (0m01s)\n",
        encoding="utf-8",
    )


def _run_gate(repo: Path, monkeypatch: pytest.MonkeyPatch, mode: str = "HEAD") -> int:
    """Run ``check_gate_claim.main()`` from inside ``repo`` with no sweep running."""
    monkeypatch.chdir(repo)
    monkeypatch.delenv(SOURCES_ENV, raising=False)
    monkeypatch.setattr("sys.argv", ["check_gate_claim", mode])
    return main()


# ── The digest is content identity ──────────────────────────────────────────


def test_a_checkout_that_moves_mtimes_moves_no_digest(tmp_path: Path) -> None:
    """Every build-relevant file dated into the future digests as before.

    This is the defect the gate had: a branch switch rewrites mtimes and moves
    no content, and a freshness read from mtimes failed every clean tree.
    """
    repo = _make_repo(tmp_path)
    before = sources_digest_of_worktree(repo)
    later = (repo / "src" / "A.agda").stat().st_mtime + 3600
    os.utime(repo / "src" / "A.agda", (later, later))
    assert sources_digest_of_worktree(repo) == before


def test_a_content_edit_moves_the_digest(tmp_path: Path) -> None:
    """One byte in a build-relevant file is a different digest."""
    repo = _make_repo(tmp_path)
    before = sources_digest_of_worktree(repo)
    (repo / "src" / "A.agda").write_text("module A where\n-- edited\n", encoding="utf-8")
    assert sources_digest_of_worktree(repo) != before


def test_a_clean_checkout_digests_to_its_commit(tmp_path: Path) -> None:
    """The working tree and HEAD agree when nothing build-relevant differs."""
    repo = _make_repo(tmp_path)
    assert sources_digest_of_worktree(repo) == sources_digest_of_revision("HEAD", repo=repo)
    (repo / "README.md").write_text("# edited, not build-relevant\n", encoding="utf-8")
    assert sources_digest_of_worktree(repo) == sources_digest_of_revision("HEAD", repo=repo)


def test_an_uncommitted_build_edit_parts_the_worktree_from_its_commit(tmp_path: Path) -> None:
    """A modified module, or an untracked one, is content HEAD does not carry."""
    repo = _make_repo(tmp_path)
    head = sources_digest_of_revision("HEAD", repo=repo)
    (repo / "src" / "B.agda").write_text("module B where\n", encoding="utf-8")
    assert sources_digest_of_worktree(repo) != head, "an untracked module is observed"
    (repo / "src" / "B.agda").unlink()
    (repo / "src" / "A.agda").write_text("module A where\n-- x\n", encoding="utf-8")
    assert sources_digest_of_worktree(repo) != head


def test_the_digest_is_over_build_relevant_paths_only(tmp_path: Path) -> None:
    """A commit that changes only documents keeps its parent's digest."""
    repo = _make_repo(tmp_path)
    parent = sources_digest_of_revision("HEAD", repo=repo)
    (repo / "README.md").write_text("# more\n", encoding="utf-8")
    _ = commit(repo, "docs only")
    assert sources_digest_of_revision("HEAD", repo=repo) == parent


# ── Evidence ────────────────────────────────────────────────────────────────


def test_evidence_prefers_the_running_sweep_then_a_passed_log(tmp_path: Path) -> None:
    """The running sweep's export counts; so does a passed log; nothing else does."""
    digest = "a" * 64
    other = "b" * 64
    assert evidence_for(digest, log_dir=tmp_path, environ={SOURCES_ENV: digest}) is not None
    assert evidence_for(digest, log_dir=tmp_path, environ={SOURCES_ENV: other}) is None
    assert evidence_for(digest, log_dir=tmp_path, environ={}) is None
    _write_log(tmp_path, "a.log", digest, passed=True)
    assert evidence_for(digest, log_dir=tmp_path / LOG_DIR, environ={}) is not None
    assert evidence_for(other, log_dir=tmp_path / LOG_DIR, environ={}) is None


def test_a_failed_log_and_a_fast_log_are_not_evidence(tmp_path: Path) -> None:
    """A log records nothing a claim can rest on unless it passed and vouched."""
    digest = "a" * 64
    _write_log(tmp_path, "failed.log", digest, passed=False)
    _write_log(tmp_path, "fast.log", SOURCES_UNRECORDED, passed=True)
    assert evidence_for(digest, log_dir=tmp_path / LOG_DIR, environ={}) is None


def test_the_passed_line_matches_the_orchestrator_summary() -> None:
    """The verdict regex reads the line the orchestrator writes, and only that."""
    assert PASSED_LINE.match("Result:   ALL 50 STEPS PASSED")
    assert not PASSED_LINE.match("Result:   ALL 50 STEPS PASSED, but the sources moved")


# ── Hermetic end-to-end of main() ───────────────────────────────────────────


def test_e2e_no_claim_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A build-relevant commit whose message claims nothing is not checked."""
    repo = _make_repo(tmp_path)
    (repo / "src" / "A.agda").write_text("module A where\n-- x\n", encoding="utf-8")
    _ = commit(repo, "feat: no claim here")
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_claim_over_docs_only_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A claim over a commit that touches no build source needs no record."""
    repo = _make_repo(tmp_path)
    (repo / "README.md").write_text("# more\n", encoding="utf-8")
    _ = commit(repo, CLAIM)
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_claim_without_a_record_fails_and_names_the_digest(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """No sweep running and no log: the claim is refused with its digest."""
    repo = _make_repo(tmp_path)
    (repo / "src" / "A.agda").write_text("module A where\n-- x\n", encoding="utf-8")
    _ = commit(repo, CLAIM)
    assert _run_gate(repo, monkeypatch) == 1
    err = capsys.readouterr().err
    assert sources_digest_of_revision("HEAD", repo=repo) in err
    assert "src/A.agda" in err
    assert "tools/run_ci.py" in err


def test_e2e_the_running_sweep_vouches_when_it_observes_the_commit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Inside a sweep over this tree the claim passes with no log at all."""
    repo = _make_repo(tmp_path)
    (repo / "src" / "A.agda").write_text("module A where\n-- x\n", encoding="utf-8")
    _ = commit(repo, CLAIM)
    assert _run_gate(repo, monkeypatch) == 1
    monkeypatch.setenv(SOURCES_ENV, sources_digest_of_worktree(repo))
    monkeypatch.setattr("sys.argv", ["check_gate_claim", "HEAD"])
    assert main() == 0


def test_e2e_a_sweep_over_another_tree_does_not_vouch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A sweep whose tree carries an uncommitted build edit is not evidence."""
    repo = _make_repo(tmp_path)
    (repo / "src" / "A.agda").write_text("module A where\n-- x\n", encoding="utf-8")
    _ = commit(repo, CLAIM)
    (repo / "src" / "A.agda").write_text("module A where\n-- y\n", encoding="utf-8")
    monkeypatch.chdir(repo)
    monkeypatch.setenv(SOURCES_ENV, sources_digest_of_worktree(repo))
    monkeypatch.setattr("sys.argv", ["check_gate_claim", "HEAD"])
    assert main() == 1
    assert "not the commit's" in capsys.readouterr().err


def test_e2e_a_passed_log_vouches_whatever_the_mtimes_say(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A finished passing log over the commit's sources is the evidence."""
    repo = _make_repo(tmp_path)
    (repo / "src" / "A.agda").write_text("module A where\n-- x\n", encoding="utf-8")
    _ = commit(repo, CLAIM)
    _write_log(repo, "ci-main.log", sources_digest_of_revision("HEAD", repo=repo), passed=True)
    later = (repo / "src" / "A.agda").stat().st_mtime + 3600
    os.utime(repo / "src" / "A.agda", (later, later))
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_a_failed_or_fast_log_does_not_vouch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A failed sweep, and a fast-tier sweep that passed, leave the claim unbacked."""
    repo = _make_repo(tmp_path)
    (repo / "src" / "A.agda").write_text("module A where\n-- x\n", encoding="utf-8")
    _ = commit(repo, CLAIM)
    _write_log(repo, "failed.log", sources_digest_of_revision("HEAD", repo=repo), passed=False)
    _write_log(repo, "fast.log", SOURCES_UNRECORDED, passed=True)
    assert _run_gate(repo, monkeypatch) == 1


def test_e2e_audit_mode_reads_the_named_commit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An older commit is audited against its own sources, not HEAD's."""
    repo = _make_repo(tmp_path)
    (repo / "src" / "A.agda").write_text("module A where\n-- x\n", encoding="utf-8")
    audited = commit(repo, CLAIM)
    _write_log(repo, "ci-main.log", sources_digest_of_revision(audited, repo=repo), passed=True)
    (repo / "src" / "A.agda").write_text("module A where\n-- y\n", encoding="utf-8")
    _ = commit(repo, "feat: later, no claim")
    assert _run_gate(repo, monkeypatch, mode=audited) == 0
    assert _run_gate(repo, monkeypatch, mode="HEAD") == 0, "HEAD claims nothing"


def test_e2e_a_root_commit_is_diffed_against_nothing_not_skipped(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A repository's first commit adds every file it holds; a claim on it is checked.

    Without ``--root`` git lists no files for a root commit, and the check
    read that as a doc-only commit and passed the claim unread.
    """
    repo = tmp_path / "repo"
    (repo / "src").mkdir(parents=True)
    (repo / "src" / "A.agda").write_text("module A where\n", encoding="utf-8")
    git(repo, "init", "-q", "-b", "main")
    _ = commit(repo, CLAIM)
    assert _run_gate(repo, monkeypatch) == 1
