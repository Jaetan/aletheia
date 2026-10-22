# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Test stand-ins: a tool's fake on the search path, a build holding a lock, stand-in kernels."""

from __future__ import annotations

import contextlib
import fcntl
import os
import shutil
import signal
import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType

import pytest
from _processes import CommandWord, ProcessId

if TYPE_CHECKING:
    from collections.abc import Generator

    from tools._determinism_guard import ProcessBytes

# A tool's name, as the lane looks it up on the search path.
ToolName = NewType("ToolName", str)

# A Python script's source, run by the test's own interpreter.
ScriptSource = NewType("ScriptSource", str)


def install_stand_in(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, name: ToolName, source: ScriptSource
) -> None:
    """Put an executable script named ``name`` first on the search path, run by this interpreter."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    tool = bin_dir / name
    _ = tool.write_text(f"#!{sys.executable}\n{source}", encoding="utf-8")
    tool.chmod(0o755)
    monkeypatch.setenv("PATH", f"{bin_dir}:{os.environ['PATH']}")


# A stand-in kernel's name, the stem of its source under haskell-shim/test.
StandInName = NewType("StandInName", str)

_REPO = Path(__file__).resolve().parents[2]


def stand_in_kernel(name: StandInName) -> Path:
    """Return the stand-in kernel the build makes beside the library the tests run against.

    ``cabal run shake -- build`` makes each one in the directory ``ALETHEIA_LIB``
    names, or the repository's ``build/``.
    """
    lib = os.environ.get("ALETHEIA_LIB")
    built = Path(lib).parent if lib else _REPO / "build"
    path = built / "stand-ins" / f"{name}.so"
    assert path.exists(), f"stand-in {path} not built; run 'cabal run shake -- build'"
    return path


def never_written(directory: Path) -> Path:
    """Make a FIFO nothing writes: a process reading it blocks until something stops it."""
    never = directory / "never"
    os.mkfifo(never)
    return never


def stopped(lock: Path) -> None:
    """Block until every process holding ``lock`` has exited.

    Each process a build starts inherits the lock's descriptor, so the lock
    frees only once the last of them is gone.
    """
    fd = os.open(lock, os.O_RDWR)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
    finally:
        os.close(fd)


# The target the stand-in blocks on unless told another: the one the sweep and the gates build.
_BUILD = CommandWord("build")


def _free(lock: Path) -> bool:
    """Say whether no process holds ``lock``, without waiting for one to let it go."""
    fd = os.open(lock, os.O_RDWR)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        return False
    finally:
        os.close(fd)
    return True


class DrivenBuild(NamedTuple):
    """A driver running a stand-in ``cabal``, and the lock its build holds."""

    driver: subprocess.Popen[ProcessBytes]
    lock: Path


@contextlib.contextmanager
def driving_a_held_build(
    tmp_path: Path,
    source: ScriptSource,
    *,
    blocks_on: CommandWord = _BUILD,
    own_group: bool = False,
) -> Generator[DrivenBuild]:
    """Run ``source`` with a stand-in ``cabal``; yield once the build it starts holds its lock.

    The stand-in, first on the driver's search path, answers ``cabal run
    shake -- <target>``: it takes a lock on a descriptor every process it
    starts inherits and, when the target is ``blocks_on``, leaves a shell
    waiting on a child that blocks on a FIFO nothing writes, the shape of
    ``cabal`` running ``shake``.  That child writes its process id to another
    FIFO, which this reads, so no clock decides when the build has started.
    The driver inherits a write end of that FIFO, so a driver that ends before
    its build starts, however early, ends the read rather than leaving it
    blocked.  Any other target exits 0 at once and writes nothing.
    ``own_group`` makes the driver lead a process group of its own, as a
    terminal's foreground job does.  The driver and the build's blocking
    child are killed once the block is left, if either still runs.
    """
    flock = shutil.which("flock")
    if flock is None:
        pytest.skip("flock(1) is not installed")
    root = tmp_path / "held-build"
    (root / "bin").mkdir(parents=True)
    lock, started = root / "build.lock", root / "started"
    os.mkfifo(started)
    never = never_written(root)
    cabal = root / "bin" / "cabal"
    _ = cabal.write_text(
        "#!/bin/sh\n"
        + f'exec 9>"{lock}"\n'
        + f"{flock} 9 || exit 1\n"
        + f'[ "$4" = "{blocks_on}" ] || exit 0\n'
        + f'sh -c \'echo $$ > "{started}"; exec cat "{never}"\'\n',
        encoding="utf-8",
    )
    cabal.chmod(0o755)
    # A FIFO's read end opens at once without blocking; its write end then opens at once too.
    with os.fdopen(os.open(started, os.O_RDONLY | os.O_NONBLOCK), encoding="ascii") as said:
        os.set_blocking(said.fileno(), True)
        held = os.open(started, os.O_WRONLY)
        try:
            driver = subprocess.Popen(
                [sys.executable, "-c", source],
                cwd=_REPO,
                env=os.environ | {"PATH": f"{cabal.parent}{os.pathsep}{os.environ['PATH']}"},
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                pass_fds=(held,),
                process_group=0 if own_group else None,
            )
        finally:
            os.close(held)
        with driver:
            watched: ProcessId | None = None
            try:
                line = said.readline()
                assert line, "the driver ended before the build it runs started"
                watched = ProcessId(int(line))
                yield DrivenBuild(driver, lock)
            finally:
                driver.kill()
                # A free lock means every holder has exited, the watched child among them,
                # whose id may by then be another process's.
                if watched is not None and not _free(lock):
                    with contextlib.suppress(ProcessLookupError):
                        os.kill(watched, signal.SIGKILL)
