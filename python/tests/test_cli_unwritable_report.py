# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A report stdout refuses: each CLI subcommand exits 2 with one line naming the refusal.

The command runs in this process with ``sys.stdout`` replaced, so each refusal
the interpreter can meet is set up directly: a full device refusing at the write
or at the flush, a stream that cannot write, a closed descriptor, an encoding the
report does not fit, and a stdout an earlier refusal closed.
"""

import io
import os
import sys
from pathlib import Path
from typing import Literal

import pytest

from aletheia.cli import main

CORPUS_DIR = Path(__file__).parent / "fixtures" / "dbc_corpus"


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

    def test_a_report_stdout_cannot_encode(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A report the stdout encoding cannot carry is refused naming the encoding's refusal."""
        errors = io.StringIO()
        monkeypatch.setattr(sys, "stderr", errors)
        stdout = io.TextIOWrapper(io.BytesIO(), encoding="ascii")
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
