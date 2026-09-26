# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools._common.run_guarded``: a command stops when the process that started it dies.

Each case runs a driver process that starts a stand-in build through
``run_guarded``: a shell holding a scratch lock that every process it starts
inherits, the shape of ``cabal`` running ``shake``.  The driver is then killed
or interrupted, and the test reads whether the watched process and the lock
outlived it.
"""

from __future__ import annotations

import contextlib
import fcntl
import os
import shutil
import signal
import subprocess
import sys
import textwrap
import time
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

import pytest

from tools import _common

if TYPE_CHECKING:
    from collections.abc import Generator

REPO_ROOT = Path(_common.__file__).resolve().parents[1]
BOUND_SECONDS = 5.0


class Build(NamedTuple):
    """A driver running a stand-in build, and what the build holds."""

    driver: subprocess.Popen[str]
    watched: int
    lock: Path


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


def _lock_free(lock: Path) -> bool:
    fd = os.open(lock, os.O_RDWR)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        return False
    finally:
        os.close(fd)
    return True


def _stopped_within(build: Build, bound: float) -> bool:
    deadline = time.monotonic() + bound
    while _alive(build.watched) or not _lock_free(build.lock):
        if time.monotonic() > deadline:
            return False
        time.sleep(0.02)
    return True


@contextlib.contextmanager
def _started(
    tmp_path: Path, *, handlers: bool, shell_body: str, grace_seconds: float = 10.0
) -> Generator[Build]:
    """Start a driver whose command takes the lock and runs ``shell_body``; kill what survives.

    ``shell_body`` writes the pid the test watches into ``{pid_file}``.  The
    command holds the lock on descriptor 9, which every process it starts
    inherits.
    """
    lock = tmp_path / "build.lock"
    pid_file = tmp_path / "watched.pid"
    flock = shutil.which("flock")
    if flock is None:
        pytest.skip("flock(1) is not installed")
    body = f'exec 9>"{lock}"; {flock} 9; ' + shell_body.format(pid_file=f'"{pid_file}"')
    script = textwrap.dedent(f"""
        from tools import _common
        if {handlers}:
            _common.install_restore_handlers()
        _common.run_guarded(["sh", "-c", {body!r}], grace_seconds={grace_seconds!r})
    """)
    with subprocess.Popen(
        [sys.executable, "-c", script],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    ) as driver:
        deadline = time.monotonic() + 30
        while not (pid_file.exists() and pid_file.read_text().strip()):
            if time.monotonic() > deadline or driver.poll() is not None:
                driver.kill()
                pytest.fail("the stand-in build never started")
            time.sleep(0.02)
        watched = int(pid_file.read_text())
        try:
            yield Build(driver, watched, lock)
        finally:
            driver.kill()
            if _alive(watched):
                os.kill(watched, signal.SIGKILL)


def test_the_status_and_the_merged_output_pass_through() -> None:
    """The exit status comes back, and stdout and stderr in the order written, as ``stdout``."""
    result = _common.run_guarded(["sh", "-c", "echo one; echo two >&2; echo three; exit 3"])
    assert (result.returncode, result.stdout, result.stderr) == (3, "one\ntwo\nthree\n", "")


def test_output_sent_to_a_file_lands_in_the_file(tmp_path: Path) -> None:
    """A file handle given as ``output`` receives both streams, and the result carries none."""
    log = tmp_path / "out.log"
    with log.open("w") as logf:
        result = _common.run_guarded(["sh", "-c", "echo out; echo err >&2"], output=logf)
    assert (result.returncode, result.stdout) == (0, "")
    assert log.read_text() == "out\nerr\n"


def test_the_command_reads_no_input() -> None:
    """The command's input is empty even where the caller's is a pipe left open.

    A command in a process group that is not the terminal's foreground job
    stops when it reads the terminal; an open pipe stands in for it here,
    since the command would wait on it as long.
    """
    script = "from tools import _common; _common.run_guarded(['cat'])"
    with subprocess.Popen(
        [sys.executable, "-c", script], cwd=REPO_ROOT, stdin=subprocess.PIPE
    ) as driver:
        try:
            assert driver.wait(BOUND_SECONDS) == 0
        finally:
            driver.kill()


def test_closing_the_stop_descriptor_stops_the_command() -> None:
    """A closed write end behind ``stop_fd`` interrupts the command as the caller's death does."""
    stop_read, stop_write = os.pipe()
    os.close(stop_write)
    try:
        started = time.monotonic()
        result = _common.run_guarded(["sleep", "60"], stop_fd=stop_read)
    finally:
        os.close(stop_read)
    # A guard that stops its group ends in that group's SIGKILL, itself included.
    assert result.returncode == -signal.SIGKILL
    assert time.monotonic() - started < BOUND_SECONDS


def test_no_descriptor_is_left_open() -> None:
    """Both ends of the guard's pipe are closed once the command returns."""
    fds = Path("/proc/self/fd")
    before = sorted(fds.iterdir())
    _ = _common.run_guarded(["true"])
    assert sorted(fds.iterdir()) == before


def test_a_command_a_signal_ended_reports_the_shell_status() -> None:
    """A command a signal ended reports 128 plus the signal number."""
    result = _common.run_guarded(["sh", "-c", "kill -TERM $$"])
    assert result.returncode == 128 + signal.SIGTERM


def test_the_guard_refuses_outside_a_group_of_its_own() -> None:
    """Started in its caller's group, the guard runs nothing rather than risk signalling it."""
    guard = REPO_ROOT / "tools" / "_guarded_run.py"
    watch_read, watch_write = os.pipe()
    try:
        result = subprocess.run(
            [sys.executable, str(guard), str(watch_read), "10", "sh", "-c", "echo ran"],
            capture_output=True,
            text=True,
            pass_fds=(watch_read,),
            check=False,
        )
    finally:
        os.close(watch_read)
        os.close(watch_write)
    assert result.returncode == 2
    assert result.stdout == ""
    assert "not the leader of its own process group" in result.stderr


def test_a_killed_caller_stops_its_command(tmp_path: Path) -> None:
    """SIGKILL of the caller stops the command and frees its lock within the bound."""
    with _started(
        tmp_path, handlers=False, shell_body="echo $$ > {pid_file}; exec sleep 60"
    ) as build:
        build.driver.kill()
        _ = build.driver.wait()
        assert _stopped_within(build, BOUND_SECONDS), "the build outlived its killed caller"


def test_an_interrupted_caller_waits_for_its_command(tmp_path: Path) -> None:
    """A restore handler's exit waits for the command to stop before the caller is gone.

    The command takes half a second to exit on the interrupt, as Shake does
    while it stops its own children, so a caller or guard that does not wait
    exits while the command still runs.
    """
    body = 'trap "sleep 0.5; exit 0" INT; echo $$ > {pid_file}; sleep 60 & wait'
    with _started(tmp_path, handlers=True, shell_body=body) as build:
        build.driver.send_signal(signal.SIGTERM)
        assert build.driver.wait(BOUND_SECONDS) == 128 + signal.SIGTERM
        assert not _alive(build.watched), "the caller exited while its build still ran"
        assert _lock_free(build.lock)


def test_a_command_that_ignores_the_interrupt_is_killed(tmp_path: Path) -> None:
    """What ignores the interrupt is killed once the command has exited."""
    body = '(trap "" INT; exec sleep 60) & echo $! > {pid_file}; wait'
    with _started(tmp_path, handlers=False, shell_body=body) as build:
        build.driver.kill()
        _ = build.driver.wait()
        assert _stopped_within(build, BOUND_SECONDS), "a process ignoring the interrupt survived"


def test_a_command_that_ignores_the_interrupt_is_killed_after_the_grace_period(
    tmp_path: Path,
) -> None:
    """A command still running once the grace period ends gets SIGKILL with its group."""
    body = 'trap "" INT; echo $$ > {pid_file}; exec sleep 60'
    with _started(tmp_path, handlers=False, shell_body=body, grace_seconds=0.5) as build:
        build.driver.kill()
        _ = build.driver.wait()
        assert _stopped_within(build, BOUND_SECONDS), "the grace period never ended"
