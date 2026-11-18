# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Run one GitHub Actions step's script under the watchdog: the shell of every workflow.

Usage: ``python3.14 -m tools.watch_step SCRIPT``, each workflow's ``defaults.run.shell``
being ``python3.14 -m tools.watch_step {0}`` and GitHub writing the step's ``run:``
text to ``SCRIPT``; every step runs from the checkout's root.

The script runs as GitHub's own default shell runs it, ``bash -e SCRIPT``.  Its
output, stderr merged, is copied to this process's stdout as it comes, so the
job log shows it live, and read by the watchdog (``tools._watchdog``) under the
declaration ``tools._workflow_steps`` gives for what the script runs: its
progress pattern and allowance, or none for a step only GitHub runs, which no
deadline holds.  A watched step ends with one line saying what the watchdog
measured of it, its reports and its longest stretch without one, from which
its allowance is set.  A step the watchdog stopped, or one that passed, declares
progress reports and ran past ``UNREPORTED_FOR`` without one, fails, saying why;
otherwise this exits with the script's own status.  A script no declaration names, or more
than one, is refused before it runs, exit 2.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from tools._common import CommandWord, ProcessStatus
from tools._watchdog import NO_REPORTS_YET, StepWatch, judged, run_watched
from tools._workflow_steps import ScriptText, declared_for

# The status of a step the watchdog stopped, and of a script no single declaration names.
_STOPPED, _UNDECLARED = ProcessStatus(1), ProcessStatus(2)


def main(argv: list[CommandWord] | None = None) -> ProcessStatus:
    """Run the step script the command line names under the watchdog; return the step's status."""
    parser = argparse.ArgumentParser(description=(__doc__ or "").split("\n\n", maxsplit=1)[0])
    _ = parser.add_argument("script", type=Path, help="the step's script, as GitHub wrote it")
    script = Path(parser.parse_args(argv).script)
    declared = declared_for(ScriptText(script.read_text(encoding="utf-8")))
    if isinstance(declared, str):
        _ = sys.stderr.write(f"watch-step: {declared}\n")
        return _UNDECLARED
    progress = NO_REPORTS_YET if declared.progress is None else declared.progress
    ran = run_watched(
        [CommandWord("bash"), CommandWord("-e"), CommandWord(str(script))],
        cwd=None,
        stop_fd=None,
        watch=StepWatch(sys.stdout.buffer, progress, lambda _report: None),
    )
    ran_for = ran.pumped.ran_for
    if declared.progress is not None:
        _ = sys.stdout.write(
            f"watchdog: {ran.pumped.reports} progress reports in {int(ran_for)}s,"
            + f" the longest stretch without one {int(ran.pumped.longest_quiet)}s\n"
        )
    if judged(progress, ran, ran_for, sys.stdout.buffer):
        return _STOPPED
    status = ran.returncode
    return ProcessStatus(128 - status if status < 0 else status)


if __name__ == "__main__":
    sys.exit(main())
