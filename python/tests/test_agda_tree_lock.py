# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The repo-wide Agda lock in ``tools/_common.py``: refuse by default, queue on request."""

from __future__ import annotations

import fcntl
import os
import subprocess
import sys
import threading
from typing import TYPE_CHECKING

import pytest

from tools import _common

if TYPE_CHECKING:
    from pathlib import Path


@pytest.fixture(name="held_lock")
def _held_lock(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> int:
    """Point the lock at a scratch file and hold it from a second descriptor.

    ``flock`` locks belong to the open file description, so a second ``open`` of
    the same path in this process contends with the first exactly as another
    process would.
    """
    path = tmp_path / ".agda-tree.lock"
    monkeypatch.setattr(_common, "_agda_lock_path", lambda: path)
    fd = os.open(path, os.O_CREAT | os.O_RDWR, 0o644)
    fcntl.flock(fd, fcntl.LOCK_EX)
    _ = os.write(fd, b"4242\n")
    return fd


def test_a_held_lock_is_refused_by_default(held_lock: int) -> None:
    """Without ``wait`` a contended acquisition exits with a message naming the holder."""
    with pytest.raises(SystemExit) as refused, _common.agda_tree_lock():
        pytest.fail("the lock was acquired while held")
    assert "pid 4242" in str(refused.value.code)
    os.close(held_lock)


def test_a_held_lock_is_waited_for_on_request(
    held_lock: int, capsys: pytest.CaptureFixture[str]
) -> None:
    """With ``wait`` the acquisition says so, blocks until the holder releases, then proceeds.

    The printed line is the evidence of contention: a waiter that merely started
    late would also find the lock free.
    """
    acquired = threading.Event()

    def take() -> None:
        with _common.agda_tree_lock(wait=True):
            acquired.set()

    waiter = threading.Thread(target=take)
    waiter.start()
    assert not acquired.wait(0.5), "the waiter acquired a lock another descriptor held"
    os.close(held_lock)
    assert acquired.wait(5), "the waiter never acquired the released lock"
    waiter.join(5)
    err = capsys.readouterr().err
    assert "waiting for .agda-tree.lock, held by another Agda tool (" in err
    assert "pid 4242" in err


def _reaped_pid() -> int:
    """Spawn a trivial child, wait for it, and return its now-dead pid."""
    with subprocess.Popen([sys.executable, "-c", "pass"]) as child:
        _ = child.wait()
    return child.pid


@pytest.mark.parametrize(
    ("written", "reported"),
    [("{pid}\n", "the recorded pid {pid} is not running"), ("", "no pid recorded")],
)
def test_a_held_lock_is_never_called_stale(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, written: str, reported: str
) -> None:
    """A held flock proves a live holder, whatever pid the file records.

    The kernel frees the lock when its last descriptor closes, so a lock that
    is held has a live holder even when the recorded pid has exited: a child
    that was handed the descriptor, or a holder between taking the lock and
    writing its pid.  The refusal says so rather than inviting a delete.
    """
    path = tmp_path / ".agda-tree.lock"
    monkeypatch.setattr(_common, "_agda_lock_path", lambda: path)
    pid = _reaped_pid()
    fd = os.open(path, os.O_CREAT | os.O_RDWR, 0o644)
    fcntl.flock(fd, fcntl.LOCK_EX)
    _ = os.write(fd, written.format(pid=pid).encode())
    try:
        with pytest.raises(SystemExit) as refused, _common.agda_tree_lock():
            pytest.fail("the lock was acquired while held")
        message = str(refused.value.code)
        assert "stale" not in message
        assert f"held by a live process; {reported.format(pid=pid)}" in message
    finally:
        os.close(fd)
