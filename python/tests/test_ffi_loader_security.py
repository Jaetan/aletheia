# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""FFI shared-library loader security tests.

``ALETHEIA_LIB`` is implicitly trusted (anyone who can set the env var
can already redirect us to a malicious .so), but the loader rejects paths
that any non-owner can write to.  This catches the case where an
unprivileged third party who cannot set the env var poisons an existing
legitimate path.
"""

from __future__ import annotations

import stat
import sys
import types
from typing import TYPE_CHECKING, Literal

import pytest

from aletheia.client._ffi import find_ffi_library
from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path


class TestALETHEIALibPermissionHardening:
    """``ALETHEIA_LIB`` permission check."""

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
        with pytest.raises(PermissionError) as refused:
            find_ffi_library()
        assert str(refused.value) == (
            f"ALETHEIA_LIB={fake_lib} {fake_lib} is group- or world-writable (mode 0o666);"
            " refusing to load for security.  Restrict to owner-only writes"
            f" ('chmod go-w {fake_lib}')."
        )

    def test_group_writable_path_rejected(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A group-writable .so path also raises ``PermissionError``."""
        fake_lib = tmp_path / "libaletheia-ffi.so"
        fake_lib.write_bytes(b"\x7fELF")
        # Mode 664 — owner-rw + group-rw + other-r.
        fake_lib.chmod(stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IWGRP | stat.S_IROTH)
        monkeypatch.setenv("ALETHEIA_LIB", str(fake_lib))
        with pytest.raises(PermissionError) as refused:
            find_ffi_library()
        assert str(refused.value) == (
            f"ALETHEIA_LIB={fake_lib} {fake_lib} is group- or world-writable (mode 0o664);"
            " refusing to load for security.  Restrict to owner-only writes"
            f" ('chmod go-w {fake_lib}')."
        )

    def test_symlinked_path_rejected(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        """A symlink is refused by name even when its target would be accepted."""
        real_lib = tmp_path / "real-libaletheia-ffi.so"
        real_lib.write_bytes(b"\x7fELF")
        real_lib.chmod(stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IROTH)
        link = tmp_path / "libaletheia-ffi.so"
        link.symlink_to(real_lib)
        monkeypatch.setenv("ALETHEIA_LIB", str(link))
        with pytest.raises(PermissionError) as refused:
            find_ffi_library()
        assert str(refused.value) == (
            f"ALETHEIA_LIB={link} {link} is a symlink; refusing to load."
            "  Resolve the link and pass the real path explicitly."
        )

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


def _plant(path: Path) -> Path:
    """Write an owner-writable-only stand-in library at ``path`` (mode 644) and return it."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(b"\x7fELF")
    path.chmod(stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IROTH)
    return path


# The name each search step gives its candidate in a refusal.
type _Source = Literal["install config", "build dir", "dist-newstyle"]


def _symlink_refusal(source: _Source, link: Path) -> Prose:
    """Return the refusal the loader raises for a symlinked candidate found by ``source``."""
    return Prose(
        f"{source} {link} is a symlink; refusing to load."
        + "  Resolve the link and pass the real path explicitly."
    )


class TestSearchWithoutALETHEIALib:
    """The search after ``ALETHEIA_LIB``: install config, build dir, dist-newstyle, refusal.

    Each test places the module in a checkout rooted at ``tmp_path`` and sets
    the search's two other inputs, the variable and the generated install
    config, so every step is reached on its own files.
    """

    @pytest.fixture
    def checkout(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
        """Return a checkout root holding the module, with no variable and no install config."""
        monkeypatch.delenv("ALETHEIA_LIB", raising=False)
        monkeypatch.setitem(sys.modules, "aletheia._install_config", None)
        module = tmp_path / "python" / "aletheia" / "client" / "_ffi.py"
        monkeypatch.setattr("aletheia.client._ffi.__file__", str(module))
        return tmp_path

    @staticmethod
    def _install(monkeypatch: pytest.MonkeyPatch, library: Path) -> None:
        """Stand in for the generated install config, naming ``library``."""
        config = types.ModuleType("aletheia._install_config")
        vars(config)["LIBRARY_PATH"] = library
        monkeypatch.setitem(sys.modules, "aletheia._install_config", config)

    def test_install_config_path_is_returned(
        self, checkout: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """The install config's path is returned before any checkout path is looked at."""
        library = _plant(checkout / "installed" / "libaletheia-ffi.so")
        _plant(checkout / "build" / "libaletheia-ffi.so")
        self._install(monkeypatch, library)
        assert find_ffi_library() == library

    def test_install_config_symlink_refused(
        self, checkout: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A symlinked install-config path is refused, naming the install config."""
        link = checkout / "installed" / "libaletheia-ffi.so"
        link.parent.mkdir()
        link.symlink_to(_plant(checkout / "real.so"))
        self._install(monkeypatch, link)
        with pytest.raises(PermissionError) as refused:
            find_ffi_library()
        assert str(refused.value) == _symlink_refusal("install config", link)

    def test_build_dir_path_is_returned(self, checkout: Path) -> None:
        """With no install config, the checkout's build directory is searched first."""
        library = _plant(checkout / "build" / "libaletheia-ffi.so")
        _plant(checkout / "haskell-shim" / "dist-newstyle" / "libaletheia-ffi.so")
        assert find_ffi_library() == library

    def test_build_dir_symlink_refused(self, checkout: Path) -> None:
        """A symlinked build-directory library is refused, naming the build dir."""
        link = checkout / "build" / "libaletheia-ffi.so"
        link.parent.mkdir()
        link.symlink_to(_plant(checkout / "real.so"))
        with pytest.raises(PermissionError) as refused:
            find_ffi_library()
        assert str(refused.value) == _symlink_refusal("build dir", link)

    def test_dist_newstyle_path_is_returned(self, checkout: Path) -> None:
        """With no build directory library, the Cabal tree is searched at any depth."""
        cabal_build = checkout / "haskell-shim" / "dist-newstyle" / "build" / "x86_64-linux"
        library = _plant(cabal_build / "libaletheia-ffi.so")
        assert find_ffi_library() == library

    def test_dist_newstyle_symlink_refused(self, checkout: Path) -> None:
        """A symlinked library in the Cabal tree is refused, naming dist-newstyle."""
        link = checkout / "haskell-shim" / "dist-newstyle" / "build" / "libaletheia-ffi.so"
        link.parent.mkdir(parents=True)
        link.symlink_to(_plant(checkout / "real.so"))
        with pytest.raises(PermissionError) as refused:
            find_ffi_library()
        assert str(refused.value) == _symlink_refusal("dist-newstyle", link)

    def test_nothing_found_refused(self, checkout: Path) -> None:
        """A checkout holding no library is refused with the command that builds one."""
        (checkout / "haskell-shim" / "dist-newstyle").mkdir(parents=True)
        with pytest.raises(FileNotFoundError) as refused:
            find_ffi_library()
        assert str(refused.value) == (
            "libaletheia-ffi.so not found. Build with: cabal run shake -- build"
        )
