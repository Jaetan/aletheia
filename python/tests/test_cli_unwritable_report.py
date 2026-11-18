# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A report stdout refuses: each CLI subcommand exits 2 with one line naming the refusal.

The command runs in this process with ``sys.stdout`` replaced, so each refusal
the interpreter can meet is set up directly: a full device refusing at the write
or at the flush, a stream that cannot write, a closed descriptor, an encoding the
report does not fit, a stdout an earlier refusal closed, and an unbuffered stdout
whose descriptor takes part of a write.
"""

import errno
import io
import os
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType

import pytest

from aletheia.cli import main
from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Buffer

CORPUS_DIR = Path(__file__).parent / "fixtures" / "dbc_corpus"

# How many bytes a descriptor takes, and the bytes of a report as its stdout's descriptor took them.
ByteCount = NewType("ByteCount", int)
ReportBytes = NewType("ReportBytes", bytes)


class _Run(NamedTuple):
    """A run's exit status and the report its stdout's descriptor took."""

    status: ExitStatus
    report: ReportBytes


class _Descriptor(io.FileIO):
    """The descriptor under an unbuffered stdout (``python -u``), taking at most ``room`` bytes.

    A write past the room takes what fits, as a write reaching a file's size
    limit does, and a write with no room left is refused as that file refuses
    it.  ``taken`` holds every byte it took; nothing reaches the null device
    the descriptor is opened on.
    """

    def __init__(self, room: ByteCount) -> None:
        super().__init__(os.devnull, "wb")
        self.room = room
        self.taken = bytearray()

    def write(self, b: Buffer, /) -> ByteCount:
        if self.room == 0:
            raise OSError(errno.EFBIG, os.strerror(errno.EFBIG))
        data = bytes(b)[: self.room]
        self.room = ByteCount(self.room - len(data))
        self.taken += data
        return ByteCount(len(data))


class _DescriptorTakingNothing(io.FileIO):
    """A descriptor answering every write with no byte taken, as one that would block does."""

    def __init__(self) -> None:
        super().__init__(os.devnull, "wb")

    def write(self, b: Buffer, /) -> ByteCount:
        del b
        return ByteCount(0)


def _unbuffered(descriptor: io.FileIO) -> io.TextIOWrapper:
    """Return the stdout ``python -u`` builds over ``descriptor``: text written straight through."""
    return io.TextIOWrapper(descriptor, encoding="utf-8", write_through=True)


class TestUnwritableReport:
    """A report stdout refuses exits 2 with one error line, stdout closed for the exit flush."""

    @pytest.mark.parametrize("refused_at", ["write", "flush"])
    @pytest.mark.parametrize("report", ["text", "json", "template"])
    def test_a_refused_report_exits_2(
        self,
        report: Literal["text", "json", "template"],
        refused_at: Literal["write", "flush"],
        tmp_path: Path,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Line buffering fails each write; default buffering holds the report for the flush."""
        argv = {
            "text": ["validate", "--dbc", str(CORPUS_DIR / "multiplexing.dbc")],
            "json": ["validate", "--dbc", str(CORPUS_DIR / "multiplexing.dbc"), "--json"],
            "template": ["template", str(tmp_path / "template.xlsx")],
        }[report]
        errors = io.StringIO()
        monkeypatch.setattr(sys, "stderr", errors)
        buffering = 1 if refused_at == "write" else -1
        with Path("/dev/full").open("w", encoding="utf-8", buffering=buffering) as stdout:
            monkeypatch.setattr(sys, "stdout", stdout)
            assert main(argv) == 2
            assert stdout.closed
        assert errors.getvalue() == "Error: writing the report: No space left on device\n"

    def test_a_closed_stdout(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Descriptor 1 closed at start leaves sys.stdout None, refused as a closed descriptor."""
        errors = io.StringIO()
        monkeypatch.setattr(sys, "stderr", errors)
        monkeypatch.setattr(sys, "stdout", None)
        assert main(["validate", "--dbc", str(CORPUS_DIR / "multiplexing.dbc")]) == 2
        assert errors.getvalue() == "Error: writing the report: Bad file descriptor\n"

    @pytest.mark.parametrize("buffering", ["buffered", "unbuffered"])
    def test_a_report_stdout_cannot_encode(
        self,
        buffering: Literal["buffered", "unbuffered"],
        tmp_path: Path,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A report the stdout encoding cannot carry is refused naming the encoding's refusal."""
        errors = io.StringIO()
        monkeypatch.setattr(sys, "stderr", errors)
        stdout = (
            io.TextIOWrapper(_Descriptor(ByteCount(1 << 20)), encoding="ascii", write_through=True)
            if buffering == "unbuffered"
            else io.TextIOWrapper(io.BytesIO(), encoding="ascii")
        )
        monkeypatch.setattr(sys, "stdout", stdout)
        workbook = tmp_path / "caf\u00e9.xlsx"
        assert main(["template", str(workbook)]) == 2
        assert stdout.closed
        assert errors.getvalue().startswith(
            "Error: writing the report: 'ascii' codec can't encode character '\\xe9'"
        )

    def test_a_run_after_a_refusal_answers_a_code(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """A refusal closes stdout; a later run in the process refuses it too, not raising."""
        errors = io.StringIO()
        monkeypatch.setattr(sys, "stderr", errors)
        argv = ["validate", "--dbc", str(CORPUS_DIR / "multiplexing.dbc")]
        with Path("/dev/full").open("w", encoding="utf-8", buffering=1) as stdout:
            monkeypatch.setattr(sys, "stdout", stdout)
            assert main(argv) == 2
            assert main(argv) == 2
        assert errors.getvalue().splitlines() == [
            "Error: writing the report: No space left on device",
            "Error: I/O operation on closed file",
        ]

    def test_a_refusal_without_errno(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """A read-only stdout refuses with no errno, and its own message names the refusal."""
        errors = io.StringIO()
        monkeypatch.setattr(sys, "stderr", errors)
        with Path(os.devnull).open(encoding="utf-8") as stdout:
            monkeypatch.setattr(sys, "stdout", stdout)
            assert main(["validate", "--dbc", str(CORPUS_DIR / "multiplexing.dbc")]) == 2
        assert errors.getvalue() == "Error: writing the report: not writable\n"

    def test_an_unbuffered_stdout_refuses_a_cut_report(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """What a short write leaves is written again, and the write the descriptor refuses is.

        The report is one write, so a stdout dropping the rest of a short write
        would end the run with the report cut and no error.
        """
        errors = io.StringIO()
        monkeypatch.setattr(sys, "stderr", errors)
        descriptor = _Descriptor(ByteCount(64))
        with _unbuffered(descriptor) as stdout:
            monkeypatch.setattr(sys, "stdout", stdout)
            assert main(["format-dbc", "--dbc", str(CORPUS_DIR / "minimal.dbc")]) == 2
        assert len(descriptor.taken) == 64
        assert errors.getvalue() == "Error: writing the report: File too large\n"

    def test_an_unbuffered_stdout_taking_nothing_is_refused(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A descriptor taking no byte is refused as one that would block, not written forever."""
        errors = io.StringIO()
        monkeypatch.setattr(sys, "stderr", errors)
        with _unbuffered(_DescriptorTakingNothing()) as stdout:
            monkeypatch.setattr(sys, "stdout", stdout)
            assert main(["format-dbc", "--dbc", str(CORPUS_DIR / "minimal.dbc")]) == 2
        assert errors.getvalue() == f"Error: writing the report: {os.strerror(errno.EAGAIN)}\n"

    @pytest.mark.parametrize("report", ["lines", "non-ascii"])
    def test_an_unbuffered_stdout_carries_the_buffered_report_byte_for_byte(
        self,
        report: Literal["lines", "non-ascii"],
        tmp_path: Path,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Written past the text layer, a report's bytes are those a buffered stdout writes.

        A report written line by line, one write per message and per signal, and
        one naming a path outside ASCII, which the stdout's own encoding writes.
        """
        workbook = tmp_path / "caf\u00e9.xlsx"
        argv = {
            "lines": ["signals", "--dbc", str(CORPUS_DIR / "multiplexing.dbc")],
            "non-ascii": ["template", str(workbook)],
        }[report]
        runs: list[_Run] = []
        for unbuffered in (False, True):
            descriptor = _Descriptor(ByteCount(1 << 20))
            stdout = (
                _unbuffered(descriptor)
                if unbuffered
                else io.TextIOWrapper(io.BufferedWriter(descriptor), encoding="utf-8")
            )
            with stdout:
                monkeypatch.setattr(sys, "stdout", stdout)
                runs.append(_Run(ExitStatus(main(argv)), ReportBytes(bytes(descriptor.taken))))
            workbook.unlink(missing_ok=True)  # the next run writes it anew
        if report == "lines":
            assert runs[0].report.count(b"\n") > 1, runs[0].report
        assert runs[0].report
        assert runs[0] == runs[1]
