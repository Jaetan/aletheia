# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.cpp_scratch.reap_dead_scratch_dirs``, the sweep's tail.

A C++ test binary killed by a signal never reaches static destruction and
keeps the scratch directory it made, which is what mull does to most of the
mutants it kills. The fixture clears what it finds when the next binary
starts, so the runs at the end of a sweep are the ones with no next binary,
and this is what removes those. What separates a directory whose owner died
from one whose owner is running is the lock: the kernel drops a ``flock``
however its holder ends, whereas a process id is reused and a timestamp is
not a freshness signal.
"""

from __future__ import annotations

import fcntl
import os
import tempfile
from typing import TYPE_CHECKING

import pytest

from tools.cpp_scratch import SCRATCH_PREFIX, reap_dead_scratch_dirs

if TYPE_CHECKING:
    from pathlib import Path


@pytest.fixture(name="temp_root")
def _temp_root(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Point the reaper at a directory of this test's own, not the host's."""
    monkeypatch.setattr(tempfile, "gettempdir", lambda: str(tmp_path))
    return tmp_path


def test_a_directory_no_process_holds_is_removed(temp_root: Path) -> None:
    """A run killed before static destruction leaves this, and it goes with its contents."""
    dead = temp_root / f"{SCRATCH_PREFIX}4242"
    dead.mkdir()
    (dead / "left_behind.bin").write_bytes(b"x")
    assert reap_dead_scratch_dirs() == 1
    assert not dead.exists()


def test_a_directory_its_owner_still_holds_is_kept(temp_root: Path) -> None:
    """A live owner's lock refuses the sweep, and the directory outlives it."""
    live = temp_root / f"{SCRATCH_PREFIX}4243"
    live.mkdir()
    fd = os.open(live, os.O_RDONLY | os.O_CLOEXEC)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert reap_dead_scratch_dirs() == 0
        assert live.is_dir()
    finally:
        os.close(fd)
    assert reap_dead_scratch_dirs() == 1
    assert not live.exists()


def test_nothing_outside_the_scratch_names_is_touched(temp_root: Path) -> None:
    """The sweep reads one prefix and one shape: another name, and a file, stay."""
    other = temp_root / "aletheia-python-mutants"
    other.mkdir()
    named_file = temp_root / f"{SCRATCH_PREFIX}4244.log"
    named_file.write_text("a log, not a scratch directory", encoding="utf-8")
    assert reap_dead_scratch_dirs() == 0
    assert other.is_dir()
    assert named_file.is_file()


def test_a_link_planted_under_the_name_is_refused_rather_than_followed(temp_root: Path) -> None:
    """The temp directory is world writable, so a link's contents are someone else's."""
    target = temp_root / "elsewhere"
    target.mkdir()
    (target / "not_ours.bin").write_bytes(b"x")
    link = temp_root / f"{SCRATCH_PREFIX}4245"
    link.symlink_to(target, target_is_directory=True)
    assert reap_dead_scratch_dirs() == 0
    assert link.is_symlink()
    assert (target / "not_ours.bin").is_file()


def test_a_directory_the_removal_could_not_take_is_not_counted(temp_root: Path) -> None:
    """The count is of directories gone, not of removals attempted."""
    if os.geteuid() == 0:
        pytest.skip("a superuser unlinks through any permission")
    dead = temp_root / f"{SCRATCH_PREFIX}4246"
    held = dead / "held"
    held.mkdir(parents=True)
    (held / "pinned.bin").write_bytes(b"x")
    held.chmod(0o500)
    try:
        assert reap_dead_scratch_dirs() == 0
        assert dead.exists()
    finally:
        held.chmod(0o700)
