# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools._common.run_guarded``: a command stops when the process that started it dies.

Each case runs a driver process that starts a stand-in build through
``run_guarded``: a shell holding a scratch lock that every process it starts
inherits, the shape of ``cabal`` running ``shake``.  The driver is then killed
or interrupted, and the test reads whether the watched process and the lock
outlived it.

No case reads a clock.  The stand-in build blocks on a FIFO nothing ever
writes, so it ends only when something stops it; the build says it started
through another FIFO the test reads; and the test waits for the stop by
blocking on the lock every process of the build holds.  A stop that never
comes hangs the run, which is the run's own limit to report.
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
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

import pytest

from tools import _common

if TYPE_CHECKING:
    from collections.abc import Generator

REPO_ROOT = Path(_common.__file__).resolve().parents[1]


class Build(NamedTuple):
    """A driver running a stand-in build, and what the build holds."""

    driver: subprocess.Popen[str]
    watched: int
    lock: Path


def _stopped(build: Build) -> None:
    """Block until every process the build started has exited.

    Each of them holds the lock's descriptor, the watched one included, so the
    lock frees only once the last of them is gone.
    """
    fd = os.open(build.lock, os.O_RDWR)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
    finally:
        os.close(fd)


def _never(tmp_path: Path) -> Path:
    """Make a FIFO nothing writes: a process reading it blocks until something stops it."""
    never = tmp_path / "never"
    os.mkfifo(never)
    return never


@contextlib.contextmanager
def _started(
    tmp_path: Path, *, handlers: bool, shell_body: str, grace_seconds: float = 10.0
) -> Generator[Build]:
    """Start a driver whose command takes the lock and runs ``shell_body``; kill what survives.

    ``shell_body`` writes the pid the test watches into ``{pid_file}``, a FIFO
    the test reads, and may block on ``{never}``.  The command holds the lock on
    descriptor 9, which every process it starts inherits.  The driver prints the
    guard's return code once ``run_guarded`` is left, however it is left: set
    when ``run_guarded`` waited for the guard, ``None`` when it did not.  With
    ``handlers`` the driver installs the restore handlers and, once inside
    ``communicate`` and once the command has written ``{ready}``, sends itself
    SIGTERM, so the handler always fires while ``run_guarded`` waits on output.
    """
    lock = tmp_path / "build.lock"
    pid_file = tmp_path / "watched.pid"
    ready = tmp_path / "ready"
    for fifo in (pid_file, ready):
        os.mkfifo(fifo)
    never = _never(tmp_path)
    flock = shutil.which("flock")
    if flock is None:
        pytest.skip("flock(1) is not installed")
    body = f'exec 9>"{lock}"; {flock} 9; ' + shell_body.format(
        pid_file=f'"{pid_file}"', never=f'"{never}"', ready=f'"{ready}"'
    )
    script = textwrap.dedent(f"""
        import os
        import signal
        import subprocess
        from tools import _common
        guards = []
        class Recorded(subprocess.Popen):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                guards.append(self)
            def communicate(self, *args, **kwargs):
                if {handlers}:
                    with open({str(ready)!r}) as started:
                        started.read()
                    os.kill(os.getpid(), signal.SIGTERM)
                return super().communicate(*args, **kwargs)
        subprocess.Popen = Recorded
        if {handlers}:
            _common.install_restore_handlers()
        try:
            _common.run_guarded(["sh", "-c", {body!r}], grace_seconds={grace_seconds!r})
        finally:
            print(guards[0].returncode if guards else "no guard", flush=True)
    """)
    with subprocess.Popen(
        [sys.executable, "-c", script],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    ) as driver:
        watched = int(pid_file.read_text())
        try:
            yield Build(driver, watched, lock)
        finally:
            driver.kill()
            with contextlib.suppress(ProcessLookupError):  # gone already when the test passed
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
            assert driver.wait() == 0
        finally:
            driver.kill()


def test_closing_the_stop_descriptor_stops_the_command(tmp_path: Path) -> None:
    """A closed write end behind ``stop_fd`` interrupts the command as the caller's death does.

    The command blocks until something stops it, so its return is the stop.
    """
    stop_read, stop_write = os.pipe()
    os.close(stop_write)
    try:
        result = _common.run_guarded(["cat", str(_never(tmp_path))], stop_fd=stop_read)
    finally:
        os.close(stop_read)
    # A guard that stops its group ends in that group's SIGKILL, itself included.
    assert result.returncode == -signal.SIGKILL


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
    """SIGKILL of the caller stops the command and frees its lock."""
    with _started(
        tmp_path, handlers=False, shell_body="echo $$ > {pid_file}; exec cat {never}"
    ) as build:
        build.driver.kill()
        _ = build.driver.wait()
        _stopped(build)


def test_an_interrupted_caller_waits_for_its_command(tmp_path: Path) -> None:
    """A restore handler's exit waits for the command's guard before the caller is gone.

    The handler's ``SystemExit`` leaves ``run_guarded`` while the command still
    blocks; the guard's return code, printed once ``run_guarded`` is left, is
    set only if ``run_guarded`` waited for the guard, which ends in its group's
    SIGKILL, before the exit propagated.
    """
    body = "echo $$ > {pid_file}; echo > {ready}; exec cat {never}"
    with _started(tmp_path, handlers=True, shell_body=body) as build:
        printed, _ = build.driver.communicate()
        assert build.driver.returncode == 128 + signal.SIGTERM
        assert printed.split() == [str(-signal.SIGKILL)], "the caller left before its guard"
        _stopped(build)


def test_a_command_that_ignores_the_interrupt_is_killed(tmp_path: Path) -> None:
    """What ignores the interrupt is killed once the command has exited."""
    body = '(trap "" INT; exec cat {never}) & echo $! > {pid_file}; wait'
    with _started(tmp_path, handlers=False, shell_body=body) as build:
        build.driver.kill()
        _ = build.driver.wait()
        _stopped(build)


def test_a_command_that_ignores_the_interrupt_is_killed_after_the_grace_period(
    tmp_path: Path,
) -> None:
    """A command still running once the grace period ends gets SIGKILL with its group.

    The period is zero, so the command, which ignores the interrupt and blocks
    until something stops it, is still running when it ends, whatever the
    machine's speed.
    """
    body = 'trap "" INT; echo $$ > {pid_file}; exec cat {never}'
    with _started(tmp_path, handlers=False, shell_body=body, grace_seconds=0.0) as build:
        build.driver.kill()
        _ = build.driver.wait()
        _stopped(build)
