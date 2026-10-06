# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The repo-wide Agda lock in ``tools/_common.py``: refuse by default, queue on request."""

from __future__ import annotations

import fcntl
import os
from typing import TYPE_CHECKING, NewType

import pytest
from _processes import pid_no_process_holds

from tools import _common

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

Descriptor = NewType("Descriptor", int)
LockOperation = NewType("LockOperation", int)
Step = NewType("Step", str)


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
    held_lock: int, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """With ``wait`` the acquisition says so, blocks until the holder releases, then proceeds.

    The interleaving is driven rather than raced: the holder lets go inside the
    waiter's blocking ``flock``, so the refused try, the line saying the waiter
    queued and the acquisition after the release are seen in that order, with no
    thread and no clock.
    """
    real_flock = fcntl.flock
    steps: list[Step] = []
    queued: list[Prose] = []

    def flock(fd: Descriptor, operation: LockOperation) -> None:
        if operation & fcntl.LOCK_NB:
            try:
                real_flock(fd, operation)
            except BlockingIOError:
                steps.append(Step("try refused"))
                raise
            steps.append(Step("try took the lock"))
            return
        queued.append(Prose(capsys.readouterr().err))
        os.close(held_lock)
        steps.append(Step("holder released"))
        real_flock(fd, operation)
        steps.append(Step("waiter acquired"))

    monkeypatch.setattr(fcntl, "flock", flock)
    with _common.agda_tree_lock(wait=True):
        steps.append(Step("inside"))
    assert steps == ["try refused", "holder released", "waiter acquired", "inside"]
    assert "waiting for .agda-tree.lock, held by another Agda tool (" in queued[0]
    assert "pid 4242" in queued[0]


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
    pid = pid_no_process_holds()
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
