# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What ``tools.check_build_incremental`` does before it builds: refuse on a killed run's leftovers.

The gate edits two tracked sources and restores them on exit, on SIGINT and on
SIGTERM, which SIGKILL bypasses.  These tests cover the startup half: a marker
names the run that wrote it; a marker in a source, a build holding Shake's
lock, or another gate holding the Agda lock each refuse the run before any
build starts and before any source is captured or touched.
"""

from __future__ import annotations

import fcntl
import os
import subprocess
import sys
import textwrap
from typing import TYPE_CHECKING

import pytest

from tools import _common
from tools import check_build_incremental as gate
from tools.check_build_incremental import (
    MARKER_PREFIX,
    Probe,
    RunMarker,
    describe_run,
    markers_in,
    shake_lock_holder,
)

if TYPE_CHECKING:
    from collections.abc import Iterator
    from pathlib import Path

NAMED = f"{MARKER_PREFIX}RF_pid4242_20260924T101500Z"


def _spawn_and_reap() -> int:
    """Spawn a trivial child, wait for it, and return its now-dead pid."""
    with subprocess.Popen([sys.executable, "-c", "pass"]) as child:
        _ = child.wait()
    return child.pid


class TestMarkers:
    """A marker names its run; the unnamed form is read as an older gate's."""

    def test_a_named_marker_carries_its_run(self) -> None:
        """Tag, pid and start time come out of the token as written."""
        assert markers_in(f'x = "little_endian_{NAMED}"') == [
            RunMarker(text=NAMED, tag="RF", pid=4242, started="20260924T101500Z")
        ]

    def test_an_unnamed_marker_is_read_as_such(self) -> None:
        """The token an older gate wrote has neither pid nor start."""
        assert markers_in(f'"uncached_atom_{MARKER_PREFIX}DBC"') == [
            RunMarker(text=f"{MARKER_PREFIX}DBC", tag="DBC", pid=None, started=None)
        ]

    def test_clean_text_has_none(self) -> None:
        """A source without the prefix yields nothing."""
        assert not markers_in('formatByteOrder LittleEndian = toList "little_endian"')

    def test_bytes_are_read_the_same(self) -> None:
        """The ``.so`` is scanned as bytes and names the run the same way."""
        assert markers_in(b"\x00\x01" + NAMED.encode() + b"\x00")[0].pid == 4242

    def test_a_gone_run_is_described_as_gone(self) -> None:
        """A pid nothing runs under reads as gone; the running process reads as alive."""
        gone = RunMarker(text=NAMED, tag="RF", pid=_spawn_and_reap(), started="20260924T101500Z")
        assert describe_run(gone).endswith(", gone")
        alive = gone._replace(pid=os.getpid())
        assert describe_run(alive) == f"pid {os.getpid()}, started 20260924T101500Z, still alive"
        assert describe_run(gone._replace(pid=None, started=None)).startswith("an unnamed run")


@pytest.fixture(name="held_shake_lock")
def _held_shake_lock(tmp_path: Path) -> Iterator[tuple[Path, int]]:
    """Hold a POSIX record lock on a scratch lock file from another process.

    Record locks belong to a process, so a lock this process took would read as
    free from this process; only another process shows what Shake's lock looks
    like from the gate.
    """
    lock = tmp_path / ".shake.lock"
    script = textwrap.dedent(
        f"""
        import fcntl, os, time
        fd = os.open({str(lock)!r}, os.O_CREAT | os.O_RDWR, 0o644)
        fcntl.lockf(fd, fcntl.LOCK_EX)
        print("held", flush=True)
        time.sleep(60)
        """
    )
    with subprocess.Popen(
        [sys.executable, "-c", script], stdout=subprocess.PIPE, text=True
    ) as holder:
        assert holder.stdout is not None
        assert holder.stdout.readline().strip() == "held"
        try:
            yield lock, holder.pid
        finally:
            holder.kill()


class TestShakeLock:
    """Only F_GETLK says whether Shake's lock is held; the file's existence does not."""

    def test_a_missing_or_free_file_has_no_holder(self, tmp_path: Path) -> None:
        """No file, or a file nobody locks, reads as free."""
        lock = tmp_path / ".shake.lock"
        assert shake_lock_holder(lock) is None
        _ = lock.write_text("")
        assert shake_lock_holder(lock) is None

    def test_a_held_lock_names_its_holder(self, held_shake_lock: tuple[Path, int]) -> None:
        """The holding process's pid comes back, and the lock reads free once it exits."""
        lock, pid = held_shake_lock
        assert shake_lock_holder(lock) == pid
        os.kill(pid, 9)
        _ = os.waitpid(pid, 0)
        assert shake_lock_holder(lock) is None


@pytest.fixture(name="gate_on_scratch")
def _gate_on_scratch(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, Path]:
    """Point the gate at two scratch sources, a free Shake lock, a scratch Agda lock, no build.

    A build during a refusal is the defect these tests exist to catch, so the
    build step fails the test outright.
    """
    a = tmp_path / "ResponseFormat.agda"
    b = tmp_path / "Formatter.agda"
    _ = a.write_text('formatWarningKind UncachedAtom = "uncached_atom"\n', encoding="utf-8")
    _ = b.write_text('formatByteOrder LittleEndian = toList "little_endian"\n', encoding="utf-8")
    probes = (
        Probe(a, '"uncached_atom"', '"uncached_atom_X"', b"X"),
        Probe(b, '"little_endian"', '"little_endian_Y"', b"Y"),
    )
    monkeypatch.setattr(gate, "_PROBES", probes)
    monkeypatch.setattr(gate, "_SHAKE_LOCK", tmp_path / ".shake.lock")
    monkeypatch.setattr(gate, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(_common, "_agda_lock_path", lambda: tmp_path / ".agda-tree.lock")
    monkeypatch.setattr(gate, "_build", lambda: pytest.fail("the gate built during a refusal"))
    return a, b


class TestStartupRefusals:
    """Each leftover of a killed run refuses the gate before it builds or edits."""

    def test_a_marker_in_a_source_names_the_run_and_the_repair(
        self, gate_on_scratch: tuple[Path, Path], capsys: pytest.CaptureFixture[str]
    ) -> None:
        """The refusal names the file, the run, its liveness and the exact inverse edit."""
        a, b = gate_on_scratch
        pid = _spawn_and_reap()
        marker = f"{MARKER_PREFIX}RF_pid{pid}_20260924T101500Z"
        marked = f'formatWarningKind UncachedAtom = "uncached_atom_{marker}"\n'
        _ = a.write_text(marked, encoding="utf-8")
        assert gate.main() == 1
        out = capsys.readouterr().out
        assert f"{a.name} carries the marker of an interrupted gate run (pid {pid}, " in out
        assert "20260924T101500Z, gone)" in out
        assert f'restore it by replacing "uncached_atom_{marker}" with "uncached_atom"' in out
        assert a.read_text(encoding="utf-8") == marked, "the refusal must not touch the source"
        assert 'toList "little_endian"' in b.read_text(encoding="utf-8")

    @pytest.mark.usefixtures("gate_on_scratch")
    def test_a_build_holding_shakes_lock_is_named(
        self,
        held_shake_lock: tuple[Path, int],
        monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A held Shake lock refuses the run and names the process holding it."""
        lock, pid = held_shake_lock
        monkeypatch.setattr(gate, "_SHAKE_LOCK", lock)
        assert gate.main() == 1
        out = capsys.readouterr().out
        assert f"a build (pid {pid}) holds {lock.name}; wait for it to finish" in out

    def test_a_second_run_reports_the_agda_lock_as_held(
        self, gate_on_scratch: tuple[Path, Path], tmp_path: Path
    ) -> None:
        """While another gate holds the Agda lock, a run exits naming it and edits nothing."""
        a, _ = gate_on_scratch
        fd = os.open(tmp_path / ".agda-tree.lock", os.O_CREAT | os.O_RDWR, 0o644)
        fcntl.flock(fd, fcntl.LOCK_EX)
        _ = os.write(fd, b"4242\n")
        try:
            with pytest.raises(SystemExit) as refused:
                _ = gate.main()
            assert "pid 4242" in str(refused.value.code)
            untouched = 'formatWarningKind UncachedAtom = "uncached_atom"\n'
            assert a.read_text(encoding="utf-8") == untouched
        finally:
            os.close(fd)

    @pytest.mark.usefixtures("gate_on_scratch")
    def test_a_marker_in_the_so_names_the_run(
        self,
        tmp_path: Path,
        monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The baseline check reads the run out of the library's bytes."""
        so = tmp_path / "libaletheia-ffi.so"
        _ = so.write_bytes(b"\x7fELF" + NAMED.encode() + b"\x00")
        monkeypatch.setattr(gate, "_SO", so)
        monkeypatch.setattr(gate, "_build", lambda: None)
        assert gate.main() == 1
        out = capsys.readouterr().out
        assert f"the .so carries the marker {NAMED!r} of an earlier run (pid 4242, " in out
