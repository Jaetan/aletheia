# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the source-length gate (``tools/check_source_length.py``).

A code file of 1000 lines passes and one of 1001 fails, wherever it sits in
the tracked tree; a line is a newline byte; data and prose are not measured;
an untracked file is not the tree's; a tracked code file that cannot be read
makes the run could-not-check.
"""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _git_repo import git

from tools._common import RelPath
from tools.check_source_length import (
    MAX_LINES,
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


def _planted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, files: dict[RelPath, LineCount]
) -> Path:
    """Return a directory holding one file of each given line count, each one listed to the gate."""
    lines = {rel: FileBytes(b"x\n" * count) for rel, count in files.items()}
    return _planted_bytes(tmp_path, monkeypatch, lines)


def _planted_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, files: dict[RelPath, FileBytes]
) -> Path:
    """Return a directory holding each given file's bytes, each one listed to the gate.

    The gate's listing names exactly the keys of ``files``, in their order, so
    a file written beside them and not named is not the tree's.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    for rel, data in files.items():
        path = repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_bytes(data)
    tracked = list(files)

    def ls_files(tree: Path) -> list[RelPath]:
        del tree
        return list(tracked)

    monkeypatch.setattr("tools.check_source_length.git_ls_files", ls_files)
    return repo


# The tree's vendored copy of libclang's Python bindings, over the cap, and the
# record naming its upstream blob sha.
_REPO = Path(__file__).resolve().parents[2]
_CINDEX = RelPath("tools/_vendor/clang/cindex.py")
_RECORD = RelPath("tools/_vendor/clang/UPSTREAM.toml")


def _vendored(cindex: RelPath, record: RelPath, data: FileBytes) -> dict[RelPath, FileBytes]:
    """Return the record's bytes at ``record`` and ``data`` at ``cindex``."""
    return {record: FileBytes((_REPO / _RECORD).read_bytes()), cindex: data}


def _cindex() -> FileBytes:
    """Return the vendored bindings' bytes as the tree holds them."""
    return FileBytes((_REPO / _CINDEX).read_bytes())


def test_a_verbatim_vendored_file_is_not_measured(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A vendored file at the blob sha its record names passes, whatever its length."""
    data = _cindex()
    assert count_lines(data) > MAX_LINES
    repo = _planted_bytes(tmp_path, monkeypatch, _vendored(_CINDEX, _RECORD, data))
    assert _run(repo, monkeypatch) == 0


def test_a_vendored_file_with_one_line_changed_is_measured(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An edited copy is no longer upstream's: it is held to the cap at its length."""
    data = _cindex()
    upstream = (_REPO / _CINDEX).read_bytes()
    edited = FileBytes(upstream.replace(b"\nimport os\n", b"\nimport sys\n", 1))
    assert edited != data
    assert count_lines(edited) == count_lines(data)
    repo = _planted_bytes(tmp_path, monkeypatch, _vendored(_CINDEX, _RECORD, edited))
    assert _run(repo, monkeypatch) == 1
    assert check_tree(repo).findings == [finding(_CINDEX, count_lines(edited))]


def test_upstream_bytes_outside_the_vendor_directory_are_measured(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The exemption is by path as well as by sha: the same bytes elsewhere are the tree's."""
    data, elsewhere = _cindex(), RelPath("tools/cindex.py")
    repo = _planted_bytes(tmp_path, monkeypatch, _vendored(elsewhere, _RECORD, data))
    assert check_tree(repo).findings == [finding(elsewhere, count_lines(data))]


def test_a_record_outside_the_vendor_directory_exempts_nothing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A record and its file anywhere but under the vendor directory leave the file measured."""
    data, cindex = _cindex(), RelPath("tools/clang/cindex.py")
    repo = _planted_bytes(
        tmp_path, monkeypatch, _vendored(cindex, RelPath("tools/clang/UPSTREAM.toml"), data)
    )
    assert check_tree(repo).findings == [finding(cindex, count_lines(data))]


def test_a_record_that_does_not_parse_is_not_clean(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A record the gate cannot read exits 2 naming it, and the file it would exempt is measured."""
    data = _cindex()
    repo = _planted_bytes(tmp_path, monkeypatch, {_RECORD: FileBytes(b"[blobs\n"), _CINDEX: data})
    assert _run(repo, monkeypatch) == 2
    scan = check_tree(repo)
    assert [entry.split(":", 1)[0] for entry in scan.unreadable] == [_RECORD]
    assert scan.findings == [finding(_CINDEX, count_lines(data))]


def test_a_tracked_record_the_tree_lacks_is_not_clean(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tracked record the work tree lacks exits 2 naming it, its file measured."""
    data = _cindex()
    repo = _planted_bytes(tmp_path, monkeypatch, _vendored(_CINDEX, _RECORD, data))
    (repo / _RECORD).unlink()
    assert _run(repo, monkeypatch) == 2
    scan = check_tree(repo)
    assert [entry.split(":", 1)[0] for entry in scan.unreadable] == [_RECORD]
    assert scan.findings == [finding(_CINDEX, count_lines(data))]


def test_a_planted_file_over_the_cap_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A tracked code file of 1001 lines exits 1 and is named; its 1000-line sibling is not."""
    big, full = RelPath("shake/Rules/Big.hs"), RelPath("shake/Rules/Full.hs")
    repo = _planted(tmp_path, monkeypatch, {big: LineCount(1001), full: LineCount(1000)})
    assert _run(repo, monkeypatch) == 1
    assert check_tree(repo).findings == [finding(big, LineCount(1001))]


def test_a_tree_within_the_cap_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Code at the cap, data over it and an untracked file over it leave the tree clean."""
    repo = _planted(
        tmp_path,
        monkeypatch,
        {RelPath("Shakefile.hs"): LineCount(1000), RelPath("CHANGELOG.md"): LineCount(5000)},
    )
    _ = (repo / "untracked.py").write_text("x\n" * 2000, encoding="utf-8")
    assert _run(repo, monkeypatch) == 0


def test_a_tracked_code_file_that_cannot_be_read_is_not_clean(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tracked code file the work tree lacks exits 2 and is named, even beside a finding."""
    gone, big = RelPath("gone.py"), RelPath("big.rs")
    repo = _planted(tmp_path, monkeypatch, {gone: LineCount(1), big: LineCount(1001)})
    (repo / gone).unlink()
    assert _run(repo, monkeypatch) == 2
    scan = check_tree(repo)
    assert [entry.split(":", 1)[0] for entry in scan.unreadable] == [gone]
    assert scan.findings == [finding(big, LineCount(1001))]


@pytest.mark.parametrize(
    "rel", [RelPath("shake/Rules/Ünïcode.hs"), RelPath("shake/Rules/With Space.hs")]
)
@pytest.mark.process("git's own listing names a tracked path holding a space or a non-ASCII letter")
def test_a_path_git_would_quote_or_split_is_measured(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, rel: RelPath
) -> None:
    """A tracked path holding a space or a non-ASCII letter is read as itself and measured."""
    repo = _repo(tmp_path, {rel: LineCount(1001)})
    assert _run(repo, monkeypatch) == 1
    assert check_tree(repo).findings == [finding(rel, LineCount(1001))]


@pytest.mark.process(
    "the live tree's tracked files are git's own answer, which no planted list stands for"
)
def test_the_tracked_tree_is_within_the_cap() -> None:
    """The gate's own subject: every tracked code file of the live tree is within the cap."""
    scan = check_tree()
    assert not scan.findings
    assert not scan.unreadable
