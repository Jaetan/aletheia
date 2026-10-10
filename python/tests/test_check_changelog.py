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
  passes; a doc-only change passes.  This is the orchestrator end-to-end
  validation check at the gate level.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import commit, git

from tools._common import RelPath
from tools.check_changelog import (
    Category,
    UnreleasedHeaders,
    headers_refused,
    main,
    unreleased_headers,
    watched_files,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

# Watched: a representative path per public-API + infra pattern.
WATCHED_PATHS = [
    RelPath("python/aletheia/client.py"),
    RelPath("go/aletheia/client.go"),
    RelPath("cpp/include/aletheia/client.hpp"),
    RelPath("rust/src/lib.rs"),
    RelPath("haskell-shim/ffi-exports.snapshot"),
    RelPath("haskell-shim/src/AletheiaFFI.hs"),
    RelPath("haskell-shim/aletheia.cabal"),
    RelPath("Shakefile.hs"),
    RelPath("shake.cabal"),
    RelPath("aletheia.agda-lib"),
    RelPath("tools/check_changelog.py"),
    RelPath("tools/run_ci.py"),
    RelPath(".github/workflows/pr-full-ci.yml"),
]

# Excluded: never requires a CHANGELOG entry.  Includes the discriminators that
# tell intent from implementation — a ``.md`` under a watched dir, Agda ``src/``
# (covered transitively via the bindings), and the separate ``go/excel`` module.
EXCLUDED_PATHS = [
    RelPath("docs/development/BUILDING.md"),
    RelPath("README.md"),
    RelPath("CHANGELOG.md"),
    RelPath("tools/agda-iwyu-reader/README.md"),
    RelPath("haskell-shim/NOTES.md"),
    RelPath("python/tests/test_x.py"),
    RelPath("go/aletheia/client_test.go"),
    RelPath("cpp/tests/foo.cpp"),
    RelPath("rust/tests/dbc_model.rs"),
    RelPath("haskell-shim/test/ConstructorTest.hs"),
    RelPath("tools/agda-iwyu-reader/test/manifest.tsv"),
    RelPath("src/Aletheia/Main.agda"),
    RelPath("go/excel/loader.go"),
]


@pytest.mark.parametrize("path", WATCHED_PATHS)
def test_watched_path_requires_changelog(path: RelPath) -> None:
    """Each watched path is reported as requiring a CHANGELOG entry."""
    assert watched_files([path]) == [path]


@pytest.mark.parametrize("path", EXCLUDED_PATHS)
def test_excluded_path_is_ignored(path: RelPath) -> None:
    """Each excluded path is never reported, even under a watched directory."""
    assert watched_files([path]) == []


def test_mixed_set_reports_only_watched() -> None:
    """A mixed change set yields exactly the watched, non-test/doc files."""
    assert set(watched_files([*WATCHED_PATHS, *EXCLUDED_PATHS])) == set(WATCHED_PATHS)


# ── Hermetic end-to-end of main() in a throwaway git repo ──────────────────


def _make_repo(tmp_path: Path) -> Path:
    """Init a repo with a ``main`` branch carrying a baseline commit."""
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-b", "main")
    (repo / "README.md").write_text("# base\n", encoding="utf-8")
    (repo / "CHANGELOG.md").write_text("# Changelog\n\n## [Unreleased]\n", encoding="utf-8")
    commit(repo, "base")
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
    git(repo, "checkout", "-b", "feature")
    (repo / "tools").mkdir()
    (repo / "tools" / "thing.py").write_text("x = 1\n", encoding="utf-8")
    commit(repo, "touch tooling")
    assert _run_gate(repo, monkeypatch) == 1


def test_e2e_watched_change_with_changelog_passes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The same tooling change passes once CHANGELOG.md is also edited."""
    repo = _make_repo(tmp_path)
    git(repo, "checkout", "-b", "feature")
    (repo / "tools").mkdir()
    (repo / "tools" / "thing.py").write_text("x = 1\n", encoding="utf-8")
    (repo / "CHANGELOG.md").write_text(
        "# Changelog\n\n## [Unreleased]\n\n### Changed\n\n- internal — no behavior change\n",
        encoding="utf-8",
    )
    commit(repo, "touch tooling + changelog")
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_doc_only_change_passes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A docs-only change never trips the gate, even with no CHANGELOG edit."""
    repo = _make_repo(tmp_path)
    git(repo, "checkout", "-b", "feature")
    (repo / "docs").mkdir()
    (repo / "docs" / "GUIDE.md").write_text("hello\n", encoding="utf-8")
    commit(repo, "doc only")
    assert _run_gate(repo, monkeypatch) == 0


def test_e2e_a_repeated_category_header_fails(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """Two ``### Changed`` under Unreleased fail, whatever the diff holds."""
    repo = _make_repo(tmp_path)
    git(repo, "checkout", "-b", "feature")
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
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A ``### Improved`` under Unreleased is refused and named."""
    repo = _make_repo(tmp_path)
    git(repo, "checkout", "-b", "feature")
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
    git(repo, "checkout", "-b", "feature")
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


def test_e2e_the_headers_are_audited_before_the_diff(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A repeated header fails the gate even when the comparison ref cannot be read."""
    repo = _make_repo(tmp_path)
    (repo / "CHANGELOG.md").write_text(
        "# Changelog\n\n## [Unreleased]\n\n### Fixed\n\n### Fixed\n", encoding="utf-8"
    )
    commit(repo, "repeat a header")
    monkeypatch.chdir(repo)
    monkeypatch.setattr("sys.argv", ["check_changelog", "no-such-ref"])
    assert main() == 1


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
