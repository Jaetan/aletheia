# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_changelog`` — the gate guarding CHANGELOG discipline.

Two layers:

* ``watched_files`` — the pure path matcher.  Exercised by tests parameterized
  over a watched set (public-API + build/CI/tooling) and an excluded set (tests,
  Markdown docs, Agda ``src/``, the separate ``go/excel`` module).  The
  discriminating case is a ``.md`` file *under* a watched dir
  (e.g. ``tools/.../README.md``): it must be excluded, proving the ``.md``
  filter, not merely the repo-root-doc non-match.
* ``main`` — a hermetic end-to-end run in a throwaway git repo, both polarities:
  a watched change WITHOUT a CHANGELOG edit fails; the same change WITH one
  passes; a doc-only change passes.  This is the
  [[feedback_orchestrator_end_to_end_validation]] check at the gate level.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from tools._common import find_executable, run_capture
from tools.check_changelog import main, watched_files

if TYPE_CHECKING:
    from pathlib import Path

# Watched: a representative path per public-API + infra pattern.
WATCHED_PATHS = [
    "python/aletheia/client.py",
    "go/aletheia/client.go",
    "cpp/include/aletheia/client.hpp",
    "rust/src/lib.rs",
    "haskell-shim/ffi-exports.snapshot",
    "haskell-shim/src/AletheiaFFI.hs",
    "haskell-shim/aletheia.cabal",
    "Shakefile.hs",
    "shake.cabal",
    "aletheia.agda-lib",
    "tools/check_changelog.py",
    "tools/run_ci.py",
    ".github/workflows/pr-full-ci.yml",
]

# Excluded: never requires a CHANGELOG entry.  Includes the discriminators that
# tell intent from implementation — a ``.md`` under a watched dir, Agda ``src/``
# (covered transitively via the bindings), and the separate ``go/excel`` module.
EXCLUDED_PATHS = [
    "docs/development/BUILDING.md",
    "README.md",
    "CHANGELOG.md",
    "tools/agda-iwyu-reader/README.md",
    "haskell-shim/NOTES.md",
    "python/tests/test_x.py",
    "go/aletheia/client_test.go",
    "cpp/tests/foo.cpp",
    "rust/tests/dbc_model.rs",
    "haskell-shim/test/ConstructorTest.hs",
    "tools/agda-iwyu-reader/test/manifest.tsv",
    "src/Aletheia/Main.agda",
    "go/excel/loader.go",
]


@pytest.mark.parametrize("path", WATCHED_PATHS)
def test_watched_path_requires_changelog(path: str) -> None:
    """Each watched path is reported as requiring a CHANGELOG entry."""
    assert watched_files([path]) == [path]


@pytest.mark.parametrize("path", EXCLUDED_PATHS)
def test_excluded_path_is_ignored(path: str) -> None:
    """Each excluded path is never reported, even under a watched directory."""
    assert watched_files([path]) == []


def test_mixed_set_reports_only_watched() -> None:
    """A mixed change set yields exactly the watched, non-test/doc files."""
    assert set(watched_files([*WATCHED_PATHS, *EXCLUDED_PATHS])) == set(WATCHED_PATHS)


# ── Hermetic end-to-end of main() in a throwaway git repo ──────────────────


def _git(repo: Path, *args: str) -> None:
    """Run a git command in ``repo``, asserting success (for test setup)."""
    result = run_capture([find_executable("git"), "-C", str(repo), *args])
    assert result.returncode == 0, f"git {' '.join(args)} failed: {result.stderr}"


def _commit(repo: Path, message: str) -> None:
    """Stage everything and commit, with a local identity and signing off."""
    _git(repo, "add", "-A")
    _git(
        repo,
        "-c",
        "user.email=test@example.com",
        "-c",
        "user.name=Test",
        "-c",
        "commit.gpgsign=false",
        "commit",
        "-m",
        message,
    )


def _make_repo(tmp_path: Path) -> Path:
    """Init a repo with a ``main`` branch carrying a baseline commit."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-b", "main")
    (repo / "README.md").write_text("# base\n", encoding="utf-8")
    (repo / "CHANGELOG.md").write_text("# Changelog\n\n## [Unreleased]\n", encoding="utf-8")
    _commit(repo, "base")
    return repo


def _run_gate(repo: Path, monkeypatch: pytest.MonkeyPatch) -> int:
    """Run ``check_changelog.main()`` against ``main`` from inside ``repo``."""
    monkeypatch.chdir(repo)
    monkeypatch.setattr("sys.argv", ["check_changelog", "main"])
    return main()


def test_e2e_watched_change_without_changelog_fails(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A tooling change with no CHANGELOG edit fails the gate."""
    repo = _make_repo(tmp_path)
    _git(repo, "checkout", "-b", "feature")
    (repo / "tools").mkdir()
    (repo / "tools" / "thing.py").write_text("x = 1\n", encoding="utf-8")
    _commit(repo, "touch tooling")
    assert _run_gate(repo, monkeypatch) == 1


def test_e2e_watched_change_with_changelog_passes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The same tooling change passes once CHANGELOG.md is also edited."""
    repo = _make_repo(tmp_path)
    _git(repo, "checkout", "-b", "feature")
    (repo / "tools").mkdir()
    (repo / "tools" / "thing.py").write_text("x = 1\n", encoding="utf-8")
    (repo / "CHANGELOG.md").write_text(
        "# Changelog\n\n## [Unreleased]\n\n### Changed\n\n- internal — no behavior change\n",
        encoding="utf-8",
    )
    _commit(repo, "touch tooling + changelog")
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_doc_only_change_passes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A docs-only change never trips the gate, even with no CHANGELOG edit."""
    repo = _make_repo(tmp_path)
    _git(repo, "checkout", "-b", "feature")
    (repo / "docs").mkdir()
    (repo / "docs" / "GUIDE.md").write_text("hello\n", encoding="utf-8")
    _commit(repo, "doc only")
    assert _run_gate(repo, monkeypatch) == 0
