# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the source-length gate (``tools/check_source_length.py``).

A code file of 1000 lines passes and one of 1001 fails, wherever it sits in
the tracked tree; a line is a newline byte; data and prose are not measured;
an untracked file is not the tree's; a tracked code file that cannot be read
makes the run could-not-check.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import git

from tools._common import RelPath
from tools.check_source_length import (
    FileBytes,
    LineCount,
    check_tree,
    count_lines,
    finding,
    is_code_file,
    main,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.common_types import ExitStatus


@pytest.mark.parametrize(
    ("data", "lines"),
    [
        (FileBytes(data), LineCount(lines))
        for data, lines in [
            (b"", 0),
            (b"a\n", 1),
            (b"a", 0),
            (b"a\nb", 1),
            (b"\n\n", 2),
            (b"a\r\nb\r\n", 2),
        ]
    ],
)
def test_a_line_is_a_newline_byte(data: FileBytes, lines: LineCount) -> None:
    """Lines are counted as ``wc -l`` counts them, a last line without a newline uncounted."""
    assert count_lines(data) == lines


def test_the_cap_is_inclusive() -> None:
    """A file of exactly 1000 lines is within the cap; 1001 is over it, named with its count."""
    rel = RelPath("Shakefile.hs")
    assert finding(rel, LineCount(1000)) is None
    assert finding(rel, LineCount(1001)) == Prose(
        "Shakefile.hs: 1001 lines, over 1000; split it along a seam it has"
    )


@pytest.mark.parametrize(
    "rel",
    [
        RelPath(rel)
        for rel in (
            "Shakefile.hs",
            "shake/Rules/Dist.hs",
            "haskell-shim/src/AletheiaFFI/Wire.hsc",
            "src/Aletheia/Main.agda",
            "tools/check_source_length.py",
            "python/aletheia/_install_config.pyi",
            "cpp/src/client.cpp",
            "cpp/include/aletheia/client.hpp",
            "haskell-shim/cbits/abi_version.c",
            "haskell-shim/include/aletheia.h",
            "go/aletheia/client.go",
            "rust/src/lib.rs",
            "benchmarks/run_all.sh",
            "packaging/env.fish",
            "any/module.cmake",
            "cpp/CMakeLists.txt",
            "Dockerfile.runtime",
            "Dockerfile.runtime.arm64",
            "docker/Dockerfile",
            "cpp/cmake/aletheia-cpp-config.cmake.in",
        )
    ],
)
def test_code_is_measured(rel: RelPath) -> None:
    """Every language the tree compiles or interprets, and the build programs by name."""
    assert is_code_file(rel)


@pytest.mark.parametrize(
    "rel",
    [
        RelPath(rel)
        for rel in (
            "CHANGELOG.md",
            "docs/PYTHON_IMPRECISE_HINTS.yaml",
            ".github/workflows/pr-full-ci.yml",
            "python/pyproject.toml",
            "shake.cabal",
            "aletheia.agda-lib",
            "haskell-shim/ffi-exports.snapshot",
            "benchmarks/results/cpp_latency_baseline.json",
            "docs/CMakeLists.md",
            "tools/bundle_validation/consumer_rust/Cargo.toml.in",
            ".archive/reviews/frev-cpp-2026-09-15/base/clang_tidy_tests.txt",
        )
    ],
)
def test_data_and_prose_are_not_measured(rel: RelPath) -> None:
    """Data a program reads, prose and package descriptions keep their length."""
    assert not is_code_file(rel)


def _repo(tmp_path: Path, files: dict[RelPath, LineCount]) -> Path:
    """Return a repository tracking one file of each given line count."""
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q")
    for rel, lines in files.items():
        path = repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text("x\n" * lines, encoding="utf-8")
        git(repo, "add", "--", rel)
    return repo


def _run(repo: Path, monkeypatch: pytest.MonkeyPatch) -> ExitStatus:
    monkeypatch.setattr("sys.argv", ["check_source_length"])
    return main(repo=repo)


def test_a_planted_file_over_the_cap_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A tracked code file of 1001 lines exits 1 and is named; its 1000-line sibling is not."""
    big, full = RelPath("shake/Rules/Big.hs"), RelPath("shake/Rules/Full.hs")
    repo = _repo(tmp_path, {big: LineCount(1001), full: LineCount(1000)})
    assert _run(repo, monkeypatch) == 1
    assert check_tree(repo).findings == [finding(big, LineCount(1001))]


def test_a_tree_within_the_cap_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Code at the cap, data over it and an untracked file over it leave the tree clean."""
    repo = _repo(
        tmp_path,
        {RelPath("Shakefile.hs"): LineCount(1000), RelPath("CHANGELOG.md"): LineCount(5000)},
    )
    _ = (repo / "untracked.py").write_text("x\n" * 2000, encoding="utf-8")
    assert _run(repo, monkeypatch) == 0


def test_a_tracked_code_file_that_cannot_be_read_is_not_clean(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tracked code file the work tree lacks exits 2 and is named, even beside a finding."""
    gone, big = RelPath("gone.py"), RelPath("big.rs")
    repo = _repo(tmp_path, {gone: LineCount(1), big: LineCount(1001)})
    (repo / gone).unlink()
    assert _run(repo, monkeypatch) == 2
    scan = check_tree(repo)
    assert [entry.split(":", 1)[0] for entry in scan.unreadable] == [gone]
    assert scan.findings == [finding(big, LineCount(1001))]


@pytest.mark.parametrize(
    "rel", [RelPath("shake/Rules/Ünïcode.hs"), RelPath("shake/Rules/With Space.hs")]
)
def test_a_path_git_would_quote_or_split_is_measured(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, rel: RelPath
) -> None:
    """A tracked path holding a space or a non-ASCII letter is read as itself and measured."""
    repo = _repo(tmp_path, {rel: LineCount(1001)})
    assert _run(repo, monkeypatch) == 1
    assert check_tree(repo).findings == [finding(rel, LineCount(1001))]


def test_the_tracked_tree_is_within_the_cap() -> None:
    """The gate's own subject: every tracked code file of the live tree is within the cap."""
    scan = check_tree()
    assert not scan.findings
    assert not scan.unreadable
