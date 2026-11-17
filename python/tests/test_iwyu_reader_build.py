# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The IWYU reader is rebuilt when missing, older than its source or built for another toolchain.

The reader links Agda's library, so one built against another Agda cannot read
this Agda's interfaces and answers no query; its build records the toolchain
beside it, and a reader whose record names another is stale.
"""

from __future__ import annotations

import os
from typing import TYPE_CHECKING

from tools._iwyu import ReaderToolchain, reader_current

if TYPE_CHECKING:
    from pathlib import Path

_BUILT_FOR = ReaderToolchain("ghc-9.12.2 Agda-2.9.0\n")
_OTHER = ReaderToolchain("ghc-9.8.4 Agda-2.8.0\n")


def _reader(
    tmp_path: Path, *, older: bool = False, stamp: ReaderToolchain | None = _BUILT_FOR
) -> tuple[Path, Path, Path]:
    """Write a source, a binary past it (before it when ``older``) and a stamp naming ``stamp``."""
    source, binary, record = (
        tmp_path / "Main.hs",
        tmp_path / "reader",
        tmp_path / "reader.toolchain",
    )
    _ = source.write_text("main = pure ()\n", encoding="utf-8")
    _ = binary.write_bytes(b"\x7fELF")
    os.utime(source, ns=(2_000_000_000, 2_000_000_000))
    built = 1_000_000_000 if older else 3_000_000_000
    os.utime(binary, ns=(built, built))
    if stamp is not None:
        _ = record.write_text(stamp, encoding="utf-8")
    return binary, source, record


def test_a_reader_built_from_its_source_for_this_toolchain_is_current(tmp_path: Path) -> None:
    """A binary no older than its source whose stamp names this toolchain is used as it is."""
    assert reader_current(*_reader(tmp_path), _BUILT_FOR)


def test_a_reader_built_for_another_toolchain_is_stale(tmp_path: Path) -> None:
    """A stamp naming another GHC or Agda makes the reader stale, however new the binary."""
    assert not reader_current(*_reader(tmp_path, stamp=_OTHER), _BUILT_FOR)


def test_a_reader_with_no_stamp_is_stale(tmp_path: Path) -> None:
    """A binary its build never stamped names no toolchain, so it is rebuilt."""
    assert not reader_current(*_reader(tmp_path, stamp=None), _BUILT_FOR)


def test_a_reader_older_than_its_source_is_stale(tmp_path: Path) -> None:
    """A binary older than its source is rebuilt, whatever its stamp names."""
    assert not reader_current(*_reader(tmp_path, older=True), _BUILT_FOR)


def test_a_missing_reader_is_stale(tmp_path: Path) -> None:
    """No binary at all is rebuilt."""
    binary, source, record = _reader(tmp_path)
    binary.unlink()
    assert not reader_current(binary, source, record, _BUILT_FOR)
