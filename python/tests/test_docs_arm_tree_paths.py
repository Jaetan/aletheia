# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the documentation-gate arm ``tools.docs_arms.tree_paths``.

Each test builds a throwaway repository whose building guide names paths in
backticks, and asserts the arm's findings over what that repository tracks: an
untracked path is a finding, a tracked one or a build output is not, and a
guide that is missing or names no path is a finding of its own.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from _git_repo import commit, git

from tools._common import RelPath
from tools.check_docs import run_arm
from tools.docs_arms.tree_paths import GUIDE, findings, tree_paths

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Sequence
    from pathlib import Path

_TRACKED = (
    RelPath("aletheia.cabal"),
    RelPath("cpp/CMakeLists.txt"),
    RelPath("cpp/tests/a.cpp"),
    RelPath("docs/development/CI_LOCAL.md"),
    RelPath("haskell-shim/src/AletheiaFFI.hs"),
    RelPath("tools/run_ci.py"),
)


def _repo(tmp_path: Path, guide: Prose | None, *, extra: Sequence[RelPath] = ()) -> Path:
    """Return a committed repository tracking ``_TRACKED``, ``extra`` and, when given, the guide."""
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q")
    for rel in (*_TRACKED, *extra, *([GUIDE] if guide is not None else [])):
        path = repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        text = guide if rel == GUIDE and guide is not None else "x\n"
        _ = path.write_text(text, encoding="utf-8")
    _ = commit(repo, "base")
    return repo.resolve()


def _findings(repo: Path) -> list[Prose]:
    return run_arm(findings, repo)


def test_clean_guide_has_no_finding(tmp_path: Path) -> None:
    """Tracked paths, bare names, a directory and build outputs raise nothing."""
    lines = [
        "Run `tools/run_ci.py` after `cpp/CMakeLists.txt`; see `CI_LOCAL.md` and",
        "`aletheia.cabal`, under `cpp/tests/` and `haskell-shim/src`.",
        "Outputs land in `build/`, `cpp/build` and `python/.venv`; `*.so` is no path.",
        "",
    ]
    guide = Prose("\n".join(lines))
    assert _findings(_repo(tmp_path, guide)) == []


def test_untracked_paths_are_findings(tmp_path: Path) -> None:
    """A Dockerfile the tree no longer carries and a gone tool are each a finding, once."""
    lines = [
        "Build with `Dockerfile.ci`, then `tools/gone.py`; `Dockerfile.ci` again.",
        "`tools/run_ci.py` is tracked.",
        "",
    ]
    guide = Prose("\n".join(lines))
    assert _findings(_repo(tmp_path, guide)) == [
        Prose(f"{GUIDE}: not tracked: Dockerfile.ci"),
        Prose(f"{GUIDE}: not tracked: tools/gone.py"),
    ]


def test_bare_name_resolves_only_on_a_tracked_base_name(tmp_path: Path) -> None:
    """A bare Cabal name resolves through any tracked file's base name; another does not."""
    guide = Prose("Edit `shim.cabal`, not `other.cabal`.\n")
    repo = _repo(tmp_path, guide, extra=(RelPath("haskell-shim/shim.cabal"),))
    assert _findings(repo) == [Prose(f"{GUIDE}: not tracked: other.cabal")]


def test_an_untracked_file_in_the_worktree_is_a_finding(tmp_path: Path) -> None:
    """A path that sits in the work tree but is not tracked is absent from a checkout."""
    repo = _repo(tmp_path, Prose("Read `tools/local.py`.\n"))
    _ = (repo / "tools" / "local.py").write_text("x\n", encoding="utf-8")
    assert _findings(repo) == [Prose(f"{GUIDE}: not tracked: tools/local.py")]


def test_guide_naming_no_path_is_a_finding(tmp_path: Path) -> None:
    """A guide with no tree path in backticks would pass vacuously; the arm says so."""
    repo = _repo(tmp_path, Prose("Run `make` and `cabal build`; nothing here is a path.\n"))
    assert _findings(repo) == [
        Prose(f"{GUIDE}: names no tree path in backticks; the arm checks nothing")
    ]


def test_guide_absent_is_a_finding(tmp_path: Path) -> None:
    """A tree without the guide gives the arm nothing to check, which it reports."""
    repo = _repo(tmp_path, None)
    assert _findings(repo) == [
        Prose(f"{GUIDE}: not among the tracked documents; the arm checks nothing")
    ]


def test_other_documents_are_out_of_scope(tmp_path: Path) -> None:
    """The claim is the guide's; a path another document names is not checked."""
    repo = _repo(tmp_path, Prose("See `tools/run_ci.py`.\n"), extra=(RelPath("docs/OTHER.md"),))
    _ = (repo / "docs" / "OTHER.md").write_text("`tools/gone.py`\n", encoding="utf-8")
    _ = commit(repo, "other")
    assert _findings(repo) == []


def test_tree_paths_keeps_order_and_drops_build_outputs() -> None:
    """Paths come back once each, in first-named order, trailing slash dropped, outputs gone."""
    spans = ["tools/b.py", "cpp/x/", "build/x", "tools/b.py", "Dockerfile", "rust/target/", "a.md"]
    text = Prose(" ".join(f"`{span}`" for span in spans) + "\n")
    assert tree_paths(text) == [
        RelPath("tools/b.py"),
        RelPath("cpp/x"),
        RelPath("Dockerfile"),
        RelPath("rust/target"),
        RelPath("a.md"),
    ]


def test_the_project_agda_lib_is_a_tree_path(tmp_path: Path) -> None:
    """The project's ``aletheia.agda-lib`` is checked; the standard library's is no tree path."""
    guide = Prose("Pin `standard-library.agda-lib` in `aletheia.agda-lib`.\n")
    assert _findings(_repo(tmp_path, guide)) == [Prose(f"{GUIDE}: not tracked: aletheia.agda-lib")]


def test_a_span_running_past_its_line_is_not_read() -> None:
    """A span is read within one line, so no path the arm reads carries a line break."""
    assert tree_paths(Prose("`tools/a.py\n` and `tools/b.py`\n")) == [RelPath("tools/b.py")]
