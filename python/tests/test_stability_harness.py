# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``benchmarks/stability.py``: a run's size, a snapshot's counts, and the runs that cannot measure.

``tools/stability_run.py`` reads exit 0 or 1 as the harness's verdict and any
other status as an environment failure, so a run that cannot measure exits 2
with a stderr line and nothing on stdout, and so does a run whose report stdout
refuses, which leaves stdout closed for the interpreter's exit flush to find
nothing in.  A handle the cycles leave behind is a verdict, the
``ctypes_handles`` gate's to fail with exit 1 and the report.  A count variable
that is not ASCII digits from 1 to 2147483647 is refused by name before the
kernel loads.  A snapshot reads its counts from the process filesystem psutil
reads, and one whose resource cannot be read as a count fails, naming the
opening or the closing snapshot, rather than reading the resource as zero.
That filesystem is a tree the test lays out, through ``psutil.PROCFS_PATH``,
and the cycles are replaced by ones that load no kernel, or run with a client
that loads none.
"""

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Final, Literal, Never, NewType, Self, TypedDict, cast

import psutil
import pytest
from _canonical_dbc import make_dbc
from _full_stdout import BUFFERING_IDS, BUFFERINGS, NO_SPACE, Buffering, full_stdout
from _processes import CommandWord

from aletheia import AletheiaError
from aletheia.client._ffi import RTSState
from aletheia.common_types import PositiveInt, Prose
from benchmarks import stability

if TYPE_CHECKING:
    from collections.abc import Callable
    from types import TracebackType

    from aletheia.types import DBCDefinition, DLCCode
    from benchmarks.stability import CountVariable

_COUNT_VARIABLES: Final[list[CountVariable]] = [
    "ALETHEIA_STABILITY_CYCLES",
    "ALETHEIA_STABILITY_FRAMES",
]

# A resource's count, as a sub-check of the report holds it.
ResourceCount = NewType("ResourceCount", int)

# A frame's fields beside its DLC, as a cycle hands them to its client: its
# timestamp, its CAN identifier and its payload.
Timestamp = NewType("Timestamp", int)
CanId = NewType("CanId", int)
Payload = NewType("Payload", bytes)

# The memory file the laid-out tree holds: 1000 pages in all, 300 resident.
_STATM: Final = "1000 300 0 0 0 0 0\n"
_RESIDENT_PAGES: Final = 300


class _SubCheck(TypedDict):
    """One sub-check of the report, in the fields these tests read."""

    name: Literal["rss", "fd_count", "ctypes_handles", "logger_handlers"]
    start: ResourceCount
    delta: ResourceCount
    passed: bool


class _Report(TypedDict):
    """The report, in the fields these tests read."""

    cycles: PositiveInt
    frames_per_cycle: PositiveInt
    sub_checks: list[_SubCheck]
    passed: bool


@pytest.fixture(autouse=True)
def _no_arguments(monkeypatch: pytest.MonkeyPatch) -> None:
    """Run the harness with no argument, as ``tools/stability_run.py`` does."""
    monkeypatch.setattr(sys, "argv", [CommandWord("benchmarks/stability.py")])


def _no_cycle(**_cycle: PositiveInt | DBCDefinition) -> None:
    """Open no client, as a cycle would."""


def _kernel_must_not_load() -> Never:
    """Fail the test: the run reached the kernel."""
    pytest.fail("the kernel loaded before the count variables were checked")


def _without_kernel(monkeypatch: pytest.MonkeyPatch) -> None:
    """Run the harness on the canonical DBC, one cycle of one frame, opening no client."""
    monkeypatch.setattr(stability, "load_dbc", make_dbc)
    monkeypatch.setattr(stability, "_run_cycle", _no_cycle)
    for name in _COUNT_VARIABLES:
        monkeypatch.setenv(name, "1")


def _fake_procfs(monkeypatch: pytest.MonkeyPatch, root: Path) -> Path:
    """Lay out under ``root`` the files a snapshot reads, and have psutil read them.

    The process's stat file is this process's own; its memory file holds
    ``_STATM``; its descriptor directory names one file and one anon_inode.
    Answers the path of the memory file, which a test damages.
    """
    own = root / str(os.getpid())
    own.mkdir()
    stat = (Path("/proc/self") / "stat").read_text(encoding="utf-8")
    (own / "stat").write_text(stat, encoding="utf-8")
    (own / "statm").write_text(_STATM, encoding="utf-8")
    fds = root / "self" / "fd"
    fds.mkdir(parents=True)
    (fds / "3").symlink_to("/dev/null")
    (fds / "4").symlink_to("anon_inode:[eventfd]")
    monkeypatch.setattr(psutil, "PROCFS_PATH", str(root))
    return own / "statm"


def _report(capsys: pytest.CaptureFixture[Prose]) -> _Report:
    """Read the report the run wrote to stdout."""
    return cast("_Report", json.loads(capsys.readouterr().out))


def _count_refusal(name: CountVariable, raw: Prose) -> Prose:
    """Answer the words a count variable ``name`` holding ``raw`` is refused in."""
    return Prose(f"{name} must be a whole number from 1 to 2147483647, got {raw!r}")


@pytest.mark.parametrize("name", _COUNT_VARIABLES)
@pytest.mark.parametrize("raw", ["abc", "0", "-3", "5x", "", "+5", " 5", "1_0", "\u0665"])
def test_a_count_variable_takes_only_a_whole_number_in_range(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    name: CountVariable,
    raw: Prose,
) -> None:
    """Any other value is refused by name, with status 2, before the kernel loads."""
    monkeypatch.setattr(stability, "load_dbc", _kernel_must_not_load)
    monkeypatch.setenv(name, raw)
    assert stability.main() == 2
    captured = capsys.readouterr()
    assert captured.err == f"stability: {_count_refusal(name, raw)}\n"
    assert not captured.out


@pytest.mark.parametrize(
    "raw",
    ["2147483648", "1" + "0" * sys.get_int_max_str_digits()],
    ids=["past the bound", "more digits than int converts"],
)
def test_a_count_past_the_bound_is_refused_in_one_wording(
    monkeypatch: pytest.MonkeyPatch, raw: Prose
) -> None:
    """A value past 2147483647, or more digits than ``int`` converts, is refused alike."""
    monkeypatch.setenv("ALETHEIA_STABILITY_FRAMES", raw)
    refusal = _count_refusal("ALETHEIA_STABILITY_FRAMES", raw)
    with pytest.raises(ValueError, match=f"^{re.escape(refusal)}$"):
        stability.env_count("ALETHEIA_STABILITY_FRAMES", 10)


@pytest.mark.parametrize(
    ("raw", "count"),
    [("2147483647", 2147483647), ("0" * sys.get_int_max_str_digits() + "5", 5)],
    ids=["the bound", "leading zeros past int's digit limit"],
)
def test_a_count_up_to_the_bound_is_read(
    monkeypatch: pytest.MonkeyPatch, raw: Prose, count: PositiveInt
) -> None:
    """2147483647 is read as itself, and leading zeros, however many, as the digits after them."""
    monkeypatch.setenv("ALETHEIA_STABILITY_FRAMES", raw)
    assert stability.env_count("ALETHEIA_STABILITY_FRAMES", 10) == count


@pytest.mark.parametrize(
    ("given", "size"),
    [((Prose("1"), Prose("7")), (1, 7)), ((None, None), (10, 100_000))],
    ids=["given", "unset"],
)
def test_a_count_variable_sizes_the_run(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    tmp_path: Path,
    given: tuple[Prose | None, Prose | None],
    size: tuple[PositiveInt, PositiveInt],
) -> None:
    """A positive whole number is the run's size, and an unset variable is the default's."""
    _without_kernel(monkeypatch)
    _fake_procfs(monkeypatch, tmp_path)
    for name, raw in zip(_COUNT_VARIABLES, given, strict=True):
        if raw is None:
            monkeypatch.delenv(name)
        else:
            monkeypatch.setenv(name, raw)
    assert stability.main() == 0
    report = _report(capsys)
    assert (report["cycles"], report["frames_per_cycle"]) == size


def test_a_snapshot_reads_the_counts_the_process_filesystem_holds(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """The resident set size is the resident pages', and the descriptors are those naming a file."""
    _without_kernel(monkeypatch)
    _fake_procfs(monkeypatch, tmp_path)
    assert stability.main() == 0
    starts = {check["name"]: check["start"] for check in _report(capsys)["sub_checks"]}
    assert starts["rss"] == _RESIDENT_PAGES * os.sysconf("SC_PAGE_SIZE")
    assert starts["fd_count"] == 1


def test_a_descriptor_the_window_leaves_open_fails_the_verdict(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """A descriptor more at the closing snapshot fails the fd gate, and the run exits 1."""
    _without_kernel(monkeypatch)
    _fake_procfs(monkeypatch, tmp_path)

    def _cycle_opening_a_descriptor(**_cycle: PositiveInt | DBCDefinition) -> None:
        """Name one more file in the descriptor directory, as a cycle leaking one would."""
        (tmp_path / "self" / "fd" / "5").symlink_to("/dev/null")

    monkeypatch.setattr(stability, "WARMUP_CYCLES", 0)
    monkeypatch.setattr(stability, "_run_cycle", _cycle_opening_a_descriptor)
    assert stability.main() == 1
    report = _report(capsys)
    checks = {check["name"]: check for check in report["sub_checks"]}
    assert (checks["fd_count"]["delta"], checks["fd_count"]["passed"]) == (1, False)
    assert not report["passed"]


class _ClientLeakingAHandle:
    """A client that counts a handle taken on entering and keeps it on closing.

    It reads as closed inside its block and as open after it, the reverse of a
    client that clears its state, so what a client reads as decides nothing.
    """

    def __init__(self) -> None:
        self._inside = False

    def __enter__(self) -> Self:
        RTSState.refcount += 1
        self._inside = True
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        """Close, keeping the handle."""
        self._inside = False

    @property
    def is_closed(self) -> bool:
        """Read as closed while open, and as open once closed."""
        return self._inside

    def parse_dbc(self, _dbc: DBCDefinition) -> None:
        """Take the DBC, loading no kernel."""

    def start_stream(self) -> None:
        """Start no stream."""

    def send_frame(self, **_frame: Timestamp | CanId | DLCCode | Payload) -> None:
        """Take the frame, checking nothing."""

    def end_stream(self) -> None:
        """End no stream."""


def test_a_handle_the_cycles_leak_fails_the_ctypes_handles_gate(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """A handle each measured cycle leaks fails the ``ctypes_handles`` gate alone, with exit 1.

    The cycles are the harness's own, each with a client that leaks a handle.
    """
    monkeypatch.setattr(stability, "load_dbc", make_dbc)
    monkeypatch.setattr(stability, "AletheiaClient", _ClientLeakingAHandle)
    monkeypatch.setattr(RTSState, "refcount", RTSState.refcount)
    monkeypatch.setenv("ALETHEIA_STABILITY_CYCLES", "3")
    monkeypatch.setenv("ALETHEIA_STABILITY_FRAMES", "1")
    _fake_procfs(monkeypatch, tmp_path)
    assert stability.main() == 1
    captured = capsys.readouterr()
    assert not captured.err
    report = cast("_Report", json.loads(captured.out))
    checks = {check["name"]: check for check in report["sub_checks"]}
    assert (checks["ctypes_handles"]["delta"], checks["ctypes_handles"]["passed"]) == (3, False)
    assert [name for name, check in checks.items() if not check["passed"]] == ["ctypes_handles"]
    assert not report["passed"]


def _empty_root(statm: Path) -> None:
    """Leave the process out of the tree: no directory of its own."""
    statm.parent.joinpath("stat").unlink()
    statm.unlink()
    statm.parent.rmdir()


def _no_statm(statm: Path) -> None:
    """Leave the process's memory file out of the tree."""
    statm.unlink()


def _statm_not_counts(statm: Path) -> None:
    """Make the process's memory file hold words rather than numbers."""
    statm.write_text("garbage\n", encoding="utf-8")


def _no_fd_dir(statm: Path) -> None:
    """Leave the process's descriptor directory out of the tree."""
    fds = statm.parent.parent / "self" / "fd"
    for entry in fds.iterdir():
        entry.unlink()
    fds.rmdir()


@pytest.mark.parametrize(
    ("damage", "reading"),
    [
        (_empty_root, "the resident set size"),
        (_no_statm, "the resident set size"),
        (_statm_not_counts, "the resident set size"),
        (_no_fd_dir, "{root}/self/fd"),
    ],
    ids=["no process", "no memory file", "memory file not counts", "no descriptor directory"],
)
def test_an_opening_snapshot_that_cannot_read_a_count_fails_the_run(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    tmp_path: Path,
    damage: Callable[[Path], None],
    reading: Prose,
) -> None:
    """A resource the opening snapshot cannot read as a count fails the run with status 2."""
    _without_kernel(monkeypatch)
    damage(_fake_procfs(monkeypatch, tmp_path))
    assert stability.main() == 2
    captured = capsys.readouterr()
    lead = f"stability: the opening snapshot failed: reading {reading.format(root=tmp_path)}: "
    assert captured.err.startswith(lead)
    assert captured.err.count("\n") == 1
    assert not captured.out


def test_a_closing_snapshot_that_cannot_read_a_count_fails_the_run(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """A resource the closing snapshot cannot read as a count fails the run with status 2."""
    _without_kernel(monkeypatch)
    statm = _fake_procfs(monkeypatch, tmp_path)

    def _cycle_losing_statm(**_cycle: PositiveInt | DBCDefinition) -> None:
        """Remove the process's memory file, as the cycle's side effect."""
        statm.unlink()

    monkeypatch.setattr(stability, "WARMUP_CYCLES", 0)
    monkeypatch.setattr(stability, "_run_cycle", _cycle_losing_statm)
    assert stability.main() == 2
    captured = capsys.readouterr()
    assert captured.err.startswith(
        "stability: the closing snapshot failed: reading the resident set size: "
    )
    assert captured.err.count("\n") == 1
    assert not captured.out


@pytest.mark.parametrize("buffering", BUFFERINGS, ids=BUFFERING_IDS)
def test_a_report_stdout_refuses_leaves_the_run_without_a_verdict(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, buffering: Buffering
) -> None:
    """A report stdout refuses exits 2 naming the write, and stdout is left closed."""
    _without_kernel(monkeypatch)
    _fake_procfs(monkeypatch, tmp_path)
    with full_stdout(buffering) as streams:
        assert stability.main() == 2
        assert streams.out.closed
    assert streams.err.getvalue() == f"stability: writing the report failed: {NO_SPACE}\n"


def test_a_dbc_that_does_not_load_leaves_the_run_without_a_verdict(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A DBC the harness cannot load exits 2 naming the load, before any cycle."""
    _without_kernel(monkeypatch)

    def _missing_dbc() -> Never:
        """Fail the load, as a missing example file does."""
        raise FileNotFoundError(2, "No such file or directory", "example.dbc")

    monkeypatch.setattr(stability, "load_dbc", _missing_dbc)
    assert stability.main() == 2
    captured = capsys.readouterr()
    assert captured.err == (
        "stability: loading the DBC failed: "
        + "[Errno 2] No such file or directory: 'example.dbc'\n"
    )
    assert not captured.out


def test_a_warm_up_cycle_the_kernel_refuses_leaves_the_run_without_a_verdict(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A warm-up cycle the kernel refuses exits 2 naming the cycle."""
    _without_kernel(monkeypatch)

    def _refused_cycle(**_cycle: PositiveInt | DBCDefinition) -> Never:
        """Fail the cycle, as a refusal from the kernel does."""
        msg = "the kernel refused the frame"
        raise AletheiaError(msg)

    monkeypatch.setattr(stability, "_run_cycle", _refused_cycle)
    assert stability.main() == 2
    captured = capsys.readouterr()
    assert captured.err == (
        f"stability: warm-up cycle 1 of {stability.WARMUP_CYCLES} failed: "
        + "the kernel refused the frame\n"
    )
    assert not captured.out


def test_a_measured_cycle_that_fails_leaves_the_run_without_a_verdict(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """A cycle inside the window whose kernel cannot be opened exits 2 naming the cycle."""
    _without_kernel(monkeypatch)
    monkeypatch.setenv("ALETHEIA_STABILITY_CYCLES", "3")
    _fake_procfs(monkeypatch, tmp_path)

    def _kernel_gone(**_cycle: PositiveInt | DBCDefinition) -> Never:
        """Fail the cycle, as a kernel library the loader cannot open does."""
        msg = "libaletheia-ffi.so: cannot open shared object file: No such file or directory"
        raise OSError(msg)

    monkeypatch.setattr(stability, "WARMUP_CYCLES", 0)
    monkeypatch.setattr(stability, "_run_cycle", _kernel_gone)
    assert stability.main() == 2
    captured = capsys.readouterr()
    assert captured.err == (
        "stability: cycle 1 of 3 failed: "
        + "libaletheia-ffi.so: cannot open shared object file: No such file or directory\n"
    )
    assert not captured.out


def test_a_cycle_raising_any_error_leaves_the_run_without_a_verdict(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """A cycle raising what no kernel, load or file raises exits 2 naming the cycle, not 1."""
    _without_kernel(monkeypatch)
    monkeypatch.setenv("ALETHEIA_STABILITY_CYCLES", "3")
    _fake_procfs(monkeypatch, tmp_path)

    def _harness_defect(**_cycle: PositiveInt | DBCDefinition) -> Never:
        """Fail the cycle, as a defect in the harness itself does."""
        msg = "a defect in the harness"
        raise RuntimeError(msg)

    monkeypatch.setattr(stability, "WARMUP_CYCLES", 0)
    monkeypatch.setattr(stability, "_run_cycle", _harness_defect)
    assert stability.main() == 2
    captured = capsys.readouterr()
    assert captured.err == "stability: cycle 1 of 3 failed: a defect in the harness\n"
    assert not captured.out
