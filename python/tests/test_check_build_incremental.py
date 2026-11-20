# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What ``tools.check_build_incremental`` does about a killed run: refuse leftovers, end its build.

The gate edits two tracked Agda sources and the C header and restores them on
exit, on SIGINT and on SIGTERM, which SIGKILL bypasses.  Most of these tests
cover the startup half: a marker names the run that wrote it; a marker in a
source, a build holding Shake's lock, or another gate holding the Agda lock
each refuse the run before any build starts and before any source is captured
or touched.  The last holds that the build a killed run started stops with it,
rather than relinking the library with the killed run's marker in it.  The rest
hold the checks' order and the one that ends a run: back on the sources it
started from, the library is the baseline's byte for byte, which the kernel's
deterministic objects make possible; and the build's Agda compile keeps the
runtime's idle collector on, without which the compile hung.
"""

from __future__ import annotations

import fcntl
import os
import re
import subprocess
import sys
import textwrap
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType

import pytest
from _processes import pid_no_process_holds
from _stand_in import ScriptSource, driving_a_held_build, stopped

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

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator

NAMED = f"{MARKER_PREFIX}RF_pid4242_20260924T101500Z"


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
        gone = RunMarker(
            text=NAMED, tag="RF", pid=pid_no_process_holds(), started="20260924T101500Z"
        )
        assert describe_run(gone).endswith(", gone")
        alive = gone._replace(pid=os.getpid())
        assert describe_run(alive) == f"pid {os.getpid()}, started 20260924T101500Z, still alive"
        assert describe_run(gone._replace(pid=None, started=None)).startswith("an unnamed run")


@pytest.fixture(name="held_shake_lock")
def _held_shake_lock(tmp_path: Path) -> Iterator[tuple[Path, int]]:
    """Hold a POSIX record lock on a scratch lock file from another process.

    Record locks belong to a process, so a lock this process took would read as
    free from this process; only another process shows what Shake's lock looks
    like from the gate.  The holder keeps the lock until its standard input,
    which this process holds, closes or the test kills it.
    """
    lock = tmp_path / ".shake.lock"
    script = textwrap.dedent(
        f"""
        import fcntl, os, sys
        fd = os.open({str(lock)!r}, os.O_CREAT | os.O_RDWR, 0o644)
        fcntl.lockf(fd, fcntl.LOCK_EX)
        print("held", flush=True)
        sys.stdin.read()
        """
    )
    with subprocess.Popen(
        [sys.executable, "-c", script], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True
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

    @pytest.mark.process(
        "a record lock reads as free from its own holder, so only another process holding it"
        + " shows its pid through F_GETLK and its release when that process exits"
    )
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
    build step fails the test outright.  The gate runs with no argument.
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
    monkeypatch.setattr("sys.argv", ["check_build_incremental"])
    return a, b


class TestStartupRefusals:
    """Each leftover of a killed run refuses the gate before it builds or edits."""

    def test_a_marker_in_a_source_names_the_run_and_the_repair(
        self, gate_on_scratch: tuple[Path, Path], capsys: pytest.CaptureFixture[str]
    ) -> None:
        """The refusal names the file, the run, its liveness and the exact inverse edit."""
        a, b = gate_on_scratch
        pid = pid_no_process_holds()
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
        tmp_path: Path,
        monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A held Shake lock refuses the run and names the process holding it.

        The holder's pid is the reader's answer, which ``TestShakeLock`` holds;
        here it is given, and the gate's refusal over it is the claim.
        """
        asked: list[Path] = []

        def holder(lock: Path) -> Literal[4242]:
            asked.append(lock)
            return 4242

        monkeypatch.setattr(gate, "shake_lock_holder", holder)
        assert gate.main() == 1
        assert asked == [tmp_path / ".shake.lock"]
        out = capsys.readouterr().out
        assert "a build (pid 4242) holds .shake.lock; wait for it to finish" in out

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


@pytest.mark.process(
    "SIGKILL ends the gate without running any of its code, and only the kernel closing"
    + " the killed gate's pipe end shows the build stopping"
)
def test_a_killed_gate_stops_its_build(tmp_path: Path) -> None:
    """The gate killed mid-build, SIGKILL included, stops the build it started."""
    source = ScriptSource("from tools.check_build_incremental import _build; _build()")
    with driving_a_held_build(tmp_path, source) as build:
        build.driver.kill()
        _ = build.driver.wait()
        stopped(build.lock)


@pytest.mark.process(
    "only a started build writing to the gate's real standard output shows its lines arriving"
    + " while it still runs"
)
def test_the_gate_s_build_writes_its_lines_as_the_build_writes_them(tmp_path: Path) -> None:
    """A build's lines reach the gate's standard output while the build still runs.

    A stand-in ``cabal`` first on the search path writes a line, waits on a FIFO
    only this test writes, then writes another and exits 0.  The first line is
    read while the build waits, which an output captured until the build ends
    never gives: a gate that held it back would hang the read, which is the
    run's own limit to report.
    """
    stand_ins = tmp_path / "bin"
    stand_ins.mkdir()
    release = tmp_path / "release"
    os.mkfifo(release)
    cabal = stand_ins / "cabal"
    _ = cabal.write_text(
        "#!/bin/sh\n"
        + "printf '[1 of 2] Compiling A\\n'\n"
        + f'cat "{release}" > /dev/null\n'
        + "printf '[2 of 2] Compiling B\\n'\n",
        encoding="utf-8",
    )
    cabal.chmod(0o755)
    with subprocess.Popen(
        [sys.executable, "-c", "from tools.check_build_incremental import _build; _build()"],
        cwd=gate.REPO_ROOT,
        env=os.environ | {"PATH": f"{stand_ins}{os.pathsep}{os.environ['PATH']}"},
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    ) as driver:
        assert driver.stdout is not None
        first = driver.stdout.readline()
        # Opening the FIFO waits for the build's read of it; closing it ends that read.
        with release.open("w", encoding="ascii"):
            pass
        rest = driver.stdout.read()
    assert (first, rest, driver.returncode) == (
        b"[1 of 2] Compiling A\n",
        b"[2 of 2] Compiling B\n",
        0,
    )


def _reports(err: Prose) -> list[Prose]:
    """Return the progress reports among the lines of ``err``."""
    return [Prose(line) for line in err.splitlines() if line.startswith("progress: ")]


class _Ran(NamedTuple):
    """A check that ran, and the reports printed between the check before it and its start."""

    check: Prose
    heard: list[Prose]


def test_the_checks_are_reported_as_each_passes_and_stop_at_the_first_that_fails(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The checks run in order, each reported as it passes, none after a failure."""
    ran: list[_Ran] = []

    def check(name: Prose, *, holds: bool) -> Callable[[], bool]:
        def run() -> bool:
            ran.append(_Ran(name, _reports(Prose(capsys.readouterr().err))))
            return holds

        return run

    monkeypatch.setattr(gate, "_check_incremental", check(Prose("incremental"), holds=True))
    monkeypatch.setattr(gate, "_check_compiler_moves", check(Prose("moves"), holds=True))
    same = check(Prose("same library"), holds=True)
    assert gate.properties_hold(check(Prose("edits"), holds=True), same)
    assert ran == [
        ("edits", ["progress: 0/4 checks"]),
        ("incremental", ["progress: 1/4 checks"]),
        ("moves", ["progress: 2/4 checks"]),
        ("same library", ["progress: 3/4 checks"]),
    ]
    assert _reports(Prose(capsys.readouterr().err)) == ["progress: 4/4 checks"]
    ran.clear()
    monkeypatch.setattr(gate, "_check_incremental", check(Prose("incremental"), holds=False))
    assert not gate.properties_hold(check(Prose("edits"), holds=True), same)
    assert ran == [("edits", ["progress: 0/4 checks"]), ("incremental", ["progress: 1/4 checks"])]
    assert not _reports(Prose(capsys.readouterr().err))


# The bytes a scratch library holds.
_Image = NewType("_Image", bytes)


class _Ending(NamedTuple):
    """What the run's rebuilds leave as the library, the gate's status, and a line it prints."""

    library: _Image
    status: Literal[0, 1]
    said: Prose


_BASELINE = _Image(b"\x7fELF the baseline library")


@pytest.mark.parametrize(
    "ending",
    [
        _Ending(
            _Image(b"\x7fELF another library"),
            1,
            Prose("the .so the run ended on is not the baseline's byte for byte"),
        ),
        _Ending(_BASELINE, 0, Prose("the same sources built the baseline .so byte for byte")),
    ],
    ids=["moved", "same"],
)
def test_a_run_ends_on_its_baseline_library_byte_for_byte(
    gate_on_scratch: tuple[Path, Path],
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    ending: _Ending,
) -> None:
    """Back on the sources it started from, a run whose library's bytes moved fails."""
    a, b = gate_on_scratch
    so = tmp_path / "libaletheia-ffi.so"
    _ = so.write_bytes(_BASELINE)
    header = tmp_path / "aletheia.h"
    _ = header.write_text("constexpr uint32_t ALETHEIA_ABI_VERSION = 3;\n", encoding="utf-8")
    originals = {path: path.read_text(encoding="utf-8") for path in (a, b, header)}
    monkeypatch.setattr(gate, "_SO", so)
    monkeypatch.setattr(gate, "_HEADER", header)
    monkeypatch.setattr(gate, "_check_baseline", lambda: originals)
    monkeypatch.setattr(gate, "install_restore_handlers", lambda: None)
    monkeypatch.setattr(gate, "_plant_sibling", list)
    # `bool` stands in for the edit-and-revert check: given the run's originals, a mapping
    # holding three files, it holds.  The compiler moves' rebuilds relink the library.
    monkeypatch.setattr(gate, "_check_edits_and_reverts", bool)
    monkeypatch.setattr(gate, "_check_incremental", lambda: True)
    monkeypatch.setattr(gate, "_check_compiler_moves", lambda: bool(so.write_bytes(ending.library)))
    assert gate.main() == ending.status
    assert ending.said in capsys.readouterr().out


# The build's rules; the one compiling the kernel's Agda sets the runtime options it runs with.
_LIBRARY_RULES = Path(__file__).resolve().parents[2] / "shake" / "Rules" / "Library.hs"


def test_the_agda_compile_keeps_the_idle_collector_on() -> None:
    """The kernel's Agda compile runs with ``-I0.3``, under which no measured gate run hung."""
    rules = _LIBRARY_RULES.read_text(encoding="utf-8")
    found = re.search(r'"agda"\s+"\+RTS"(?P<rts>.*?)"-RTS"\s+"--compile"', rules, re.DOTALL)
    assert found is not None, "no `agda +RTS ... -RTS --compile` call in the library rules"
    assert '"-I0.3"' in found["rts"]


# The kernel's cabal file, whose foreign library's GHC options the byte-for-byte check rests on.
_CABAL = Path(__file__).resolve().parents[2] / "haskell-shim" / "aletheia.cabal"


def test_the_kernel_compiles_to_deterministic_objects() -> None:
    """The foreign library's GHC options name ``-fobject-determinism``, outside any comment."""
    stanza = _CABAL.read_text(encoding="utf-8").split("\nforeign-library aletheia-ffi\n", 1)[1]
    stanza = re.split(r"\n(?=\S)", stanza, maxsplit=1)[0]
    options = stanza.split("ghc-options:", 1)[1].splitlines()
    words = [word for line in options if not line.strip().startswith("--") for word in line.split()]
    assert "-fobject-determinism" in words
