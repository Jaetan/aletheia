# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""FFI shared-library loader security tests.

R19 cluster B / PY-B-26.11: ``ALETHEIA_LIB`` is implicitly trusted (anyone
who can set the env var can already redirect us to a malicious .so), but
the loader rejects paths that any non-owner can write to.  This catches
the case where an unprivileged third party who cannot set the env var
poisons an existing legitimate path.
"""

from __future__ import annotations

import stat
from typing import TYPE_CHECKING

import pytest

from aletheia.client._ffi import find_ffi_library

if TYPE_CHECKING:
    from pathlib import Path


class TestALETHEIALibPermissionHardening:
    """``ALETHEIA_LIB`` permission check (R19-CARRY-6 / PY-B-26.11)."""

    def test_world_writable_path_rejected(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A world-writable .so path raises ``PermissionError`` before load."""
        fake_lib = tmp_path / "libaletheia-ffi.so"
        fake_lib.write_bytes(b"\x7fELF")  # ELF magic — content not validated
        # Make world-writable (mode 666).
        fake_lib.chmod(
            stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IWGRP | stat.S_IROTH | stat.S_IWOTH
        )
        monkeypatch.setenv("ALETHEIA_LIB", str(fake_lib))
        with pytest.raises(PermissionError, match="group- or world-writable"):
            find_ffi_library()

    def test_group_writable_path_rejected(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A group-writable .so path also raises ``PermissionError``."""
        fake_lib = tmp_path / "libaletheia-ffi.so"
        fake_lib.write_bytes(b"\x7fELF")
        # Mode 664 — owner-rw + group-rw + other-r.
        fake_lib.chmod(stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IWGRP | stat.S_IROTH)
        monkeypatch.setenv("ALETHEIA_LIB", str(fake_lib))
        with pytest.raises(PermissionError, match="group- or world-writable"):
            find_ffi_library()

    def test_owner_writable_only_accepted(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A path writable only by its owner is accepted (mode 644 / 600)."""
        fake_lib = tmp_path / "libaletheia-ffi.so"
        fake_lib.write_bytes(b"\x7fELF")
        # Mode 644 — owner-rw + group-r + other-r.
        fake_lib.chmod(stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IROTH)
        monkeypatch.setenv("ALETHEIA_LIB", str(fake_lib))
        resolved = find_ffi_library()
        assert resolved == fake_lib

    def test_missing_path_still_raises_filenotfound(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A nonexistent ``ALETHEIA_LIB`` path raises ``FileNotFoundError``.

        Verifies the existing behaviour is preserved alongside the new
        permission check (the missing-path check fires first).
        """
        missing = tmp_path / "does_not_exist.so"
        monkeypatch.setenv("ALETHEIA_LIB", str(missing))
        with pytest.raises(FileNotFoundError, match="does not exist"):
            find_ffi_library()
