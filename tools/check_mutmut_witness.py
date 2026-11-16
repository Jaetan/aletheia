# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold that the pinned mutmut writes what the Python lane's witness and its checks read.

The witness (``tools/mutation_witness.py``) and the lane's checks of it
(``tools/mutation_run.py``) read five things of mutmut's: ``run_tests`` names
the mutant whose tests run in a ``mutant_name`` parameter; a mutant's exit is
kept in its source file's ``.meta`` under ``exit_code_by_key``; the exits 1, 0,
33, 34, 37 and 255 mean killed, survived, no tests, skipped, caught by the
type check and timeout, and a mutant not yet checked has none; the progress
line counts every mutant mutmut judged; and the file log ``log_to_file`` turns
on is ``mutants/mutmut-debug.log`` by default.  Each is a fact about the
mutmut release, so the gate runs when the pin in the ``[mutation]`` extra of
``python/pyproject.toml`` moves, or a reader of it or the gate itself does
(``tools/pin_scope.py``).

Each fact is shown by mutmut's own code, in a scratch project whose
``pyproject.toml`` names one empty source and turns the log on: the witness is installed on
``PytestRunner.run_tests``; mutmut's table is read for the six exits and
none; a ``.meta`` that ``SourceFileMutationData.save`` writes and the line
``print_stats`` prints are read back by the lane's parser and its tally check,
which must count each status, pass the tally of the three runs, and refuse it
without one; and ``setup_file_logging``'s file is looked for where the lane
keeps it from.

Exits 0 when every fact holds or nothing they rest on moved, 1 naming each
fact that no longer holds, and 2 when the venv has no mutmut to ask.
"""

from __future__ import annotations

import argparse
import contextlib
import logging
import sys
import tempfile
from importlib import import_module
from pathlib import Path
from typing import TYPE_CHECKING, cast
from unittest.mock import patch

from tools._common import emit, git_toplevel
from tools.check_mutmut_operators import INSTALL_HINT, missing_mutmut
from tools.mutation_run import (
    MUTMUT_LOG,
    PYTHON_WITNESS_DIR,
    MutmutCounts,
    parse_mutmut,
    python_witness_refusal,
)
from tools.mutation_witness import TALLY_FILE, MutantName, witnessed
from tools.pin_scope import PinGate, gate_runs

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

    from mutmut.configuration import Config
    from mutmut.mutation.data import SourceFileMutationData
    from mutmut.runners.harness import PytestRunner

# One mutant per exit the lane reads, and what mutmut must file each as.
_KILLED = MutantName("m.x_f__mutmut_1")
_SURVIVED = MutantName("m.x_f__mutmut_2")
_TIMED_OUT = MutantName("m.x_f__mutmut_3")
_EXITS: dict[MutantName, ExitStatus | None] = {
    _KILLED: ExitStatus(1),
    _SURVIVED: ExitStatus(0),
    _TIMED_OUT: ExitStatus(255),
    MutantName("m.x_f__mutmut_4"): ExitStatus(33),
    MutantName("m.x_f__mutmut_5"): ExitStatus(34),
    MutantName("m.x_f__mutmut_6"): ExitStatus(37),
    MutantName("m.x_f__mutmut_7"): None,
}
STATUSES: dict[ExitStatus | None, Prose] = {
    ExitStatus(1): Prose("killed"),
    ExitStatus(0): Prose("survived"),
    ExitStatus(255): Prose("timeout"),
    ExitStatus(33): Prose("no tests"),
    ExitStatus(34): Prose("skipped"),
    ExitStatus(37): Prose("caught by type check"),
    None: Prose("not checked"),
}
# What the lane's parser must read off the line mutmut prints for _EXITS.
_COUNTS = MutmutCounts(killed=1, survived=1, timeout=1, skipped=1)
# The scratch project's configuration: its one source, which mutmut asks for,
# and the lane's log setting.
_PYPROJECT = Prose('[tool.mutmut]\nsource_paths = ["m.py"]\nlog_to_file = true\n')


def _printed_summary(by_path: Mapping[Prose, SourceFileMutationData]) -> Prose:
    """Return the progress line mutmut's own ``print_stats`` prints for ``by_path``."""
    stats = import_module("mutmut.stats")
    printed: list[Prose] = []

    def capture(text: Prose, *, force_output: bool = False) -> None:
        _ = force_output
        printed.append(text)

    print_stats = cast("Callable[..., None]", stats.print_stats)
    with patch.object(stats, "print_status", capture):
        print_stats(dict(by_path), force_output=True)
    return Prose("\n".join(printed))


def _tally(artifacts: Path, names: list[MutantName]) -> None:
    """Write the witness's tally as the runs of ``names`` leave it."""
    tally = artifacts / PYTHON_WITNESS_DIR / TALLY_FILE
    tally.parent.mkdir(parents=True, exist_ok=True)
    _ = tally.write_text("".join(f"{name}\n" for name in names), encoding="utf-8")


def _tally_check_refusals(artifacts: Path, mutants: Path, line: Prose) -> list[Prose]:
    """Return how the lane's tally check misjudges mutmut's own ``.meta`` and line.

    It must pass the tally of the three runs ``_EXITS`` names, and refuse the
    tally without one of them.
    """
    refusals: list[Prose] = []
    _tally(artifacts, [_KILLED, _SURVIVED, _TIMED_OUT])
    refusal = python_witness_refusal(artifacts, mutants, line)
    if refusal is not None:
        refusals.append(Prose(f"the lane refuses mutmut's own .meta and line: {refusal}"))
    _tally(artifacts, [_KILLED, _SURVIVED])
    if python_witness_refusal(artifacts, mutants, line) is None:
        refusals.append(
            Prose("the lane passes mutmut's own .meta with a run missing from the tally")
        )
    return refusals


def facts_refused(scratch: Path) -> list[Prose]:
    """Return each fact the venv's mutmut no longer holds, asked from ``scratch``.

    Raises ``ImportError`` where the venv has no mutmut.
    """
    refusals: list[Prose] = []
    runner = cast("type[PytestRunner]", import_module("mutmut.runners.harness").PytestRunner)
    try:
        _ = witnessed(runner.run_tests, scratch / "witness")
    except TypeError as exc:
        refusals.append(Prose(f"the witness cannot install on PytestRunner.run_tests: {exc}"))

    table = cast(
        "Mapping[ExitStatus | None, Prose]", import_module("mutmut.stats").status_by_exit_code
    )
    refusals += [
        Prose(f"mutmut files exit {code} as {table[code]!r}, not {status!r}")
        for code, status in STATUSES.items()
        if table[code] != status
    ]

    (scratch / "mutants").mkdir()
    source_data = cast(
        "type[SourceFileMutationData]", import_module("mutmut.mutation.data").SourceFileMutationData
    )
    data = source_data(path="m.py")
    for name, code in _EXITS.items():
        data.exit_code_by_key[name] = code
    data.save()
    line = _printed_summary({Prose("m.py"): data})
    counts = parse_mutmut(line)
    if counts != _COUNTS:
        refusals.append(Prose(f"the lane reads {counts} off mutmut's line {line!r}, not {_COUNTS}"))
    try:
        refusals += _tally_check_refusals(scratch / "artifacts", scratch / "mutants", line)
    except (KeyError, ValueError) as exc:
        refusals.append(Prose(f"the lane cannot read mutmut's own .meta: {exc!r}"))

    config = cast("Callable[[], Config]", import_module("mutmut.configuration").config)()
    if config.log_to_file is not True:
        refusals.append(Prose("mutmut no longer reads log_to_file, so the lane's log is off"))
    setup = cast(
        "Callable[[], None]", import_module("mutmut.utils.logging_utils").setup_file_logging
    )
    setup()
    logging.getLogger("mutmut").debug("the witness facts gate")
    if not (scratch / "mutants" / MUTMUT_LOG).is_file():
        refusals.append(
            Prose(f"mutmut's file log is not mutants/{MUTMUT_LOG}, where the lane keeps it")
        )
    return refusals


def check() -> ExitStatus:
    """Ask the venv's mutmut, from a scratch project, for every fact and judge its answers."""
    with tempfile.TemporaryDirectory(prefix="mutmut-witness-") as directory:
        scratch = Path(directory)
        _ = (scratch / "pyproject.toml").write_text(_PYPROJECT, encoding="utf-8")
        _ = (scratch / "m.py").write_text("", encoding="utf-8")
        with contextlib.chdir(scratch):
            try:
                refusals = facts_refused(scratch)
            except ImportError as exc:
                if not missing_mutmut(exc):
                    raise
                emit(f"check-mutmut-witness: {INSTALL_HINT}")
                return ExitStatus(2)
            finally:
                logging.shutdown()
    for refusal in refusals:
        emit(f"check-mutmut-witness: {refusal}")
    return ExitStatus(1 if refusals else 0)


def main() -> ExitStatus:
    """Show the witness facts when the branch moves the mutmut pin or a reader of it."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.MUTMUT_WITNESS, repo_root):
        return ExitStatus(0)
    return check()


if __name__ == "__main__":
    sys.exit(main())
