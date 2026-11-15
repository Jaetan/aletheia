# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The vendored files are upstream's bytes at the release the C++ toolchain pins.

``tools/_vendor/clang/`` holds LLVM's Python bindings to libclang and LLVM's
licence, each copied byte for byte from the release its ``UPSTREAM.toml``
names.  Each file's git blob sha is held to the record, so a one-byte edit
fails here; the record's toolchain version is held to the ``llvm-toolchain-23``
upstream version ``cpp/toolchain/check_upstream.sh`` pins, so a toolchain moved
without its bindings re-checked fails here too; the two linters that would otherwise read the
directory are told to leave it alone; and the licence header gate leaves out
the files a record names, and only those.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tomllib
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING

import pytest

from tools import check_spdx_headers
from tools._common import RelPath
from tools._vendored import (
    RECORD,
    VENDOR,
    BlobSha,
    FileBytes,
    UpstreamTag,
    VendoredName,
    blob_sha,
    read_record,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from _processes import CommandWord

_REPO = Path(__file__).resolve().parents[2]
_CLANG = _REPO / VENDOR / "clang"
_TOOLCHAIN = _REPO / "cpp" / "toolchain" / "check_upstream.sh"
# The prefix LLVM's release tags carry before the version: ``llvmorg-23.1.5``.
_LLVM_TAG = "llvmorg-"


@pytest.mark.parametrize(
    ("data", "sha"),
    [
        (FileBytes(b""), BlobSha("e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")),
        (FileBytes(b"hello\n"), BlobSha("ce013625030ba8dba906f756967f9e9ca394464a")),
    ],
)
def test_a_blob_sha_is_the_one_git_gives(data: FileBytes, sha: BlobSha) -> None:
    """The name of a blob is git's: ``git hash-object`` printed each of these."""
    assert blob_sha(data) == sha


def test_the_record_names_every_file_beside_it() -> None:
    """A file the record does not name would sit under the vendor directory unheld."""
    beside = sorted(path.name for path in _CLANG.iterdir() if path.is_file())
    assert sorted([*read_record(_CLANG / RECORD).get("blobs", {}), RECORD]) == beside


@pytest.mark.parametrize("name", sorted(read_record(_CLANG / RECORD).get("blobs", {})))
def test_each_vendored_file_is_upstream_s_bytes(name: VendoredName) -> None:
    """Each file's git blob sha is the one it has upstream at the recorded tag."""
    recorded = read_record(_CLANG / RECORD).get("blobs", {})[name]
    assert blob_sha(FileBytes((_CLANG / name).read_bytes())) == recorded


def test_the_bindings_are_checked_at_the_release_the_toolchain_pins() -> None:
    """The record's toolchain is the ``llvm-toolchain-23`` upstream version the toolchain row names.

    apt.llvm.org builds LLVM's release branch, whose version no tag may name yet,
    so the record's tag is a release of the pinned version's major series.
    """
    row = re.search(r'"llvm-toolchain-23 ([^"\s]+)"', _TOOLCHAIN.read_text(encoding="utf-8"))
    assert row is not None, f"{_TOOLCHAIN} pins no llvm-toolchain-23 release"
    record = read_record(_CLANG / RECORD)
    assert record.get("toolchain") == row.group(1)
    tag = record.get("tag", UpstreamTag(""))
    assert tag.startswith(_LLVM_TAG)
    assert tag.removeprefix(_LLVM_TAG).split(".")[0] == row.group(1).split(".")[0]


def test_ruff_leaves_the_vendored_files_unread_and_basedpyright_reports_nothing_there() -> None:
    """Both linters read ``tools`` whole; ruff skips the vendor directory, basedpyright mutes it."""
    vendor = PurePosixPath(VENDOR).as_posix()
    ruff = tomllib.loads((_REPO / "ruff.toml").read_text(encoding="utf-8"))
    assert vendor in ruff["extend-exclude"]
    pyproject = tomllib.loads((_REPO / "python" / "pyproject.toml").read_text(encoding="utf-8"))
    assert f"../{vendor}" in pyproject["tool"]["basedpyright"]["ignore"]


# A vendored directory of a scratch tree: its record, a file it names and one it does not.
_RECORD = RelPath(f"{VENDOR}clang/{RECORD}")
_NAMED = RelPath(f"{VENDOR}clang/cindex.py")
_PLANTED = RelPath(f"{VENDOR}clang/planted.py")


def _tracking(monkeypatch: pytest.MonkeyPatch, root: Path, record: Prose) -> None:
    """Make the licence header gate read ``root`` as a tree whose vendored record is ``record``.

    No file of the tree carries the header, and git's listing of it is answered here.
    """
    _ = (root / "LICENSE.md").write_text(
        f"Copyright {check_spdx_headers.COPYRIGHT_YEAR}\n", encoding="utf-8"
    )
    (root / _RECORD).parent.mkdir(parents=True)
    _ = (root / _RECORD).write_text(record, encoding="utf-8")
    for rel in (_NAMED, _PLANTED):
        _ = (root / rel).write_text("x = 1\n", encoding="utf-8")

    def toplevel() -> Path:
        return root

    def listed(cmd: list[CommandWord], *, check: bool) -> subprocess.CompletedProcess[Prose]:
        assert (cmd[1:], check) == (["-C", str(root), "ls-files"], True)
        listing = Prose("".join(f"{rel}\n" for rel in (_RECORD, _NAMED, _PLANTED)))
        return subprocess.CompletedProcess(cmd, 0, listing, Prose(""))

    def executable(name: CommandWord) -> CommandWord:
        return name

    monkeypatch.setattr(check_spdx_headers, "git_toplevel", toplevel)
    monkeypatch.setattr(check_spdx_headers, "run_capture", listed)
    monkeypatch.setattr(check_spdx_headers, "find_executable", executable)
    monkeypatch.setattr(sys, "argv", ["check_spdx_headers"])


def test_the_licence_header_gate_leaves_out_only_the_files_a_record_names(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A file the record names is upstream's; the record and a file it does not name are not."""
    _tracking(monkeypatch, tmp_path, Prose('tag = "t"\n[blobs]\n"cindex.py" = "0"\n'))
    assert check_spdx_headers.main() == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"SPDX: 2 file(s) missing the header:\n  {_RECORD}\n  {_PLANTED}\n"
        + "Run: python -m tools.check_spdx_headers --apply\n"
    )


def test_a_record_the_licence_header_gate_cannot_read_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without the record, which files are upstream's is unknown, so the gate exits 2 naming it."""
    _tracking(monkeypatch, tmp_path, Prose("[blobs\n"))
    assert check_spdx_headers.main() == ExitStatus(2)
    assert capsys.readouterr().out.startswith(
        f"SPDX: a vendored directory's record cannot be read: {_RECORD}: "
    )
