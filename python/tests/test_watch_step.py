# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.watch_step``: a workflow step's script run as GitHub runs it, under the watchdog.

The script runs under ``bash -e``, as GitHub's default shell runs it: its
output reaches this process's stdout, the job log, and its status passes
through, a failing command ending it.  A script no declaration names is
refused before it runs.  A watched step that goes past its allowance with no
report is stopped and fails, its verdict written after its output.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _stalling_output import stall_after_first_output

from tools import _watchdog, watch_step
from tools._common import CommandWord
from tools._watchdog import Chunk, Output, PatternText, Progress, Seconds
from tools._workflow_steps import ScriptText, WorkflowStep

if TYPE_CHECKING:
    from tools._common import Descriptor

    from aletheia.common_types import Prose

# A script line the exempt declarations name: the benchmark's report of a diff it does not measure.
_EXEMPT = ScriptText('echo "This diff moves no binding, so nothing was measured."\n')


def _script(tmp_path: Path, text: ScriptText) -> CommandWord:
    """Write ``text`` as a step's script, as GitHub writes one; return its path."""
    script = tmp_path / "step.sh"
    _ = script.write_text(text, encoding="utf-8")
    return CommandWord(str(script))


@pytest.mark.process("only bash running the step's script shows its output and status")
def test_a_step_s_output_reaches_stdout_and_its_status_passes_through(
    tmp_path: Path, capfdbinary: pytest.CaptureFixture[Chunk]
) -> None:
    """The script's lines, stderr merged, reach stdout; its exit status is the step's."""
    status = watch_step.main(
        [_script(tmp_path, ScriptText(_EXEMPT + "echo to-stderr >&2\nexit 3\n"))]
    )
    assert status == 3
    assert capfdbinary.readouterr().out == (
        b"This diff moves no binding, so nothing was measured.\nto-stderr\n"
    )


@pytest.mark.process("only bash -e shows a failing command ending the script")
def test_a_failing_command_ends_the_step_as_github_s_shell_does(
    tmp_path: Path, capfdbinary: pytest.CaptureFixture[Chunk]
) -> None:
    """Under ``bash -e`` the line after a failing command never runs."""
    status = watch_step.main([_script(tmp_path, ScriptText(_EXEMPT + "false\necho after\n"))])
    assert status == 1
    assert b"after" not in capfdbinary.readouterr().out


def test_a_script_no_declaration_names_is_refused_before_it_runs(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Exit 2 naming the script's first line; the script never ran, so its file is not made."""
    marker = tmp_path / "ran"
    status = watch_step.main([_script(tmp_path, ScriptText(f"\ntouch {marker}\n"))])
    assert status == 2
    assert not marker.exists()
    assert f"no declaration in tools/_workflow_steps.py names the step (touch {marker})" in (
        capsys.readouterr().err
    )


@pytest.mark.process(
    "a stall is ended by the guard interrupting bash's group, so only a started step,"
    + " blocked on a pipe no one writes, shows it stopped and failed with its verdict"
)
def test_a_watched_step_that_stalls_is_stopped_and_fails_with_its_verdict(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capfdbinary: pytest.CaptureFixture[Chunk]
) -> None:
    """After its first report the step blocks; past its allowance it is stopped and fails.

    The output is read for real on a clock of the test's: the first wait is
    answered by the output itself, every later one moves the clock past it.
    """
    never = tmp_path / "never"
    os.mkfifo(never)
    counted = Progress(PatternText(r"\[(?P<done>\d+)/(?P<total>\d+)\]"), Seconds(60.0))

    def declared(_script: ScriptText) -> WorkflowStep:
        return WorkflowStep(PatternText(r"x"), counted)

    monkeypatch.setattr(watch_step, "declared_for", declared)
    stall_after_first_output(monkeypatch)
    status = watch_step.main([_script(tmp_path, ScriptText(f"echo '[1/2] parse'\ncat {never}\n"))])
    assert status == 1
    assert capfdbinary.readouterr().out == (
        b"[1/2] parse\nwatchdog: 1 progress reports in 60s, the longest stretch without one 60s\n"
        + b"\nwatchdog: no progress report for 60s; stopped."
        + b" Last report: [1/2] parse. Last line: [1/2] parse\n"
    )


def _eleven_seconds_from_the_first_read(monkeypatch: pytest.MonkeyPatch) -> None:
    """Read watched output for real, each wait until it comes, on a clock 11 s on after one read.

    The output always comes, its line and then its end, so no wait is given a duration.
    """
    really = _watchdog.watched_output

    def scripted(out: Descriptor) -> Output:
        real, clock = really(out), [Seconds(0.0)]

        def read() -> Chunk:
            clock[0] = Seconds(11.0)
            return real.read()

        def readable_within(_wait: Seconds | None) -> bool:
            return real.readable_within(None)

        return Output(read, readable_within, lambda: clock[0])

    monkeypatch.setattr(_watchdog, "watched_output", scripted)


@pytest.mark.process("only a started step shows its output ending with no report in it")
def test_a_watched_step_that_reports_nothing_past_the_window_fails_saying_so(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capfdbinary: pytest.CaptureFixture[Chunk]
) -> None:
    """A step declaring reports that ends 11 s on with none fails, though its script passed."""
    counted = Progress(PatternText(r"\[(?P<done>\d+)/(?P<total>\d+)\]"), Seconds(600.0))

    def declared(_script: ScriptText) -> WorkflowStep:
        return WorkflowStep(PatternText(r"x"), counted)

    monkeypatch.setattr(watch_step, "declared_for", declared)
    _eleven_seconds_from_the_first_read(monkeypatch)
    status = watch_step.main([_script(tmp_path, ScriptText("echo compiling\n"))])
    assert status == 1
    assert capfdbinary.readouterr().out == (
        b"compiling\nwatchdog: 0 progress reports in 11s, the longest stretch without one 11s\n"
        + b"\nwatchdog: the step declares progress reports and made none in 11s\n"
    )


@pytest.mark.process("only a started step shows its own failure ending its output")
def test_a_watched_step_that_failed_keeps_its_status_and_its_last_line(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capfdbinary: pytest.CaptureFixture[Chunk]
) -> None:
    """A reporting step failing 11 s on with no report ends on its own error, not a verdict."""
    counted = Progress(PatternText(r"\[(?P<done>\d+)/(?P<total>\d+)\]"), Seconds(600.0))

    def declared(_script: ScriptText) -> WorkflowStep:
        return WorkflowStep(PatternText(r"x"), counted)

    monkeypatch.setattr(watch_step, "declared_for", declared)
    _eleven_seconds_from_the_first_read(monkeypatch)
    status = watch_step.main(
        [_script(tmp_path, ScriptText("echo 'error: no such file'\nexit 3\n"))]
    )
    assert status == 3
    assert capfdbinary.readouterr().out == (
        b"error: no such file\n"
        + b"watchdog: 0 progress reports in 11s, the longest stretch without one 11s\n"
    )


@pytest.mark.process(
    "GitHub runs the wrapper on a bare interpreter before any venv exists, so only a started"
    + " interpreter with no site-packages shows that everything it imports is there"
)
def test_the_wrapper_runs_a_step_on_a_bare_interpreter_from_the_checkout_s_root(
    tmp_path: Path,
) -> None:
    """With no site-packages and no PYTHONPATH, ``-m tools.watch_step`` runs a step to its end."""
    root = Path(__file__).resolve().parents[2]
    environment = {name: value for name, value in os.environ.items() if name != "PYTHONPATH"}
    script = _script(tmp_path, ScriptText(_EXEMPT + "exit 4\n"))
    ran = subprocess.run(
        [sys.executable, "-S", "-m", "tools.watch_step", script],
        cwd=root,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )
    assert (ran.returncode, ran.stderr) == (4, "")
    assert ran.stdout == "This diff moves no binding, so nothing was measured.\n"
