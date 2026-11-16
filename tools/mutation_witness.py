# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""mutmut, run with a witness of each mutant's run that does not return.

mutmut's fork server runs each mutant's tests in a child of its own, whose
standard output and error are ``/dev/null``.  A child whose run raises exits
-1, which is 255, and mutmut files it as a timeout and keeps nothing of it; a
child that ends its process leaves only its exit status.  This program wraps
``PytestRunner.run_tests`` in mutmut's own process and then hands mutmut's
command line the arguments it does not take itself, so every child the fork
server forks runs the wrapper.

While a mutant's tests run, ``<witness dir>/<mutant>.running`` holds the
mutant's name, pytest's output, and a ``started <test>`` line as each test
begins, every write reaching the file as it is made.  A run that returns
removes it.  A run that raises appends the traceback, renames it
``<mutant>.txt`` and raises on unchanged, so mutmut sees what it saw before.  A
run that ends its process, by the kernel's runtime exiting, a signal or
mutmut's own timeout, leaves the ``.running`` file naming the test it was in.
The runs naming no mutant, the clean run and the forced-fail run, are left
alone: the forced-fail run's conftest import fails by design.

The test suite loads this module as a pytest plugin for its start lines
(``python/tests/conftest.py``), which write only while the witness names its
file in ``ALETHEIA_MUTATION_WITNESS``, set in the mutant's process alone.

Run as ``cd python && .venv/bin/python ../tools/mutation_witness.py
--witness-dir DIR run``, as ``tools/mutation_run.py`` does before it reads
``DIR``.  The wrapper reads the mutant's name through ``run_tests``'s own
signature, by position or keyword, and refuses to start mutmut on one that has
no ``mutant_name``.  Each named run is tallied in ``witnessed-runs.log`` before
its tests start, and the lane fails when a mutant mutmut ran a child for is
missing from it, so a mutmut that stopped calling ``run_tests`` cannot switch
the witness off unseen.
This module imports nothing of the package under test: mutmut's children must
import the mutated copy, never one this process already holds.
"""

from __future__ import annotations

import argparse
import inspect
import io
import os
import sys
import traceback
from importlib import import_module
from pathlib import Path
from typing import TYPE_CHECKING, NewType, NoReturn, cast

if TYPE_CHECKING:
    from collections.abc import Callable

    import click
    from mutmut.runners.harness import PytestRunner

    from tools._common import CommandWord, EnvName

# The variable naming the file a mutant's run writes to, set in its process alone.
WITNESS_FILE_ENV: EnvName = cast("EnvName", "ALETHEIA_MUTATION_WITNESS")

# The parameter of mutmut's run_tests that names the mutant whose tests run.
MUTANT_PARAMETER = "mutant_name"

# The file in the witness directory holding one line per named run, its mutant's name.
TALLY_FILE = "witnessed-runs.log"

# A mutant's name as mutmut gives it, which names its witness files.
MutantName = NewType("MutantName", str)

# A pytest node id, as pytest names a test it starts.
TestId = NewType("TestId", str)


def witness_path(witness_dir: Path, mutant: MutantName) -> Path:
    """Return the file the witness of ``mutant``'s raising run is renamed to."""
    return witness_dir / f"{mutant}.txt"


def running_path(witness_dir: Path, mutant: MutantName) -> Path:
    """Return the file ``mutant``'s run writes to while it runs, left where it never returns."""
    return witness_dir / f"{mutant}.running"


def pytest_runtest_logstart(nodeid: TestId) -> None:
    """Append ``started <nodeid>`` to the file the witness names, while it names one."""
    running = os.environ.get(WITNESS_FILE_ENV)
    if running:
        with Path(running).open("a", encoding="utf-8") as record:
            _ = record.write(f"started {nodeid}\n")


def witnessed[**P, R](run_tests: Callable[P, R], witness_dir: Path) -> Callable[P, R]:
    """Return ``run_tests`` wrapped so a mutant's run that does not return leaves its witness.

    ``run_tests`` is mutmut's ``PytestRunner.run_tests``, whose ``mutant_name``
    names the mutant, ``None`` for the runs naming none.  A ``run_tests``
    without that parameter is refused here, before any run.
    """
    signature = inspect.signature(run_tests)
    if MUTANT_PARAMETER not in signature.parameters:
        message = f"{run_tests!r} takes no {MUTANT_PARAMETER}: no mutant's run could be told"
        raise TypeError(message)

    def run(*args: P.args, **kwargs: P.kwargs) -> R:
        mutant = signature.bind(*args, **kwargs).arguments.get(MUTANT_PARAMETER)
        if mutant is None:
            return run_tests(*args, **kwargs)
        name = MutantName(str(mutant))
        with (witness_dir / TALLY_FILE).open("a", encoding="utf-8") as tally:
            _ = tally.write(f"{name}\n")
        running = running_path(witness_dir, name)
        saved = sys.stdout, sys.stderr
        named = os.environ.get(WITNESS_FILE_ENV)
        # Unbuffered and appended to, so the start lines interleave in order and
        # a process that ends keeps every byte written before it did.
        raw = io.FileIO(running, "a")
        with io.TextIOWrapper(raw, encoding="utf-8", write_through=True) as output:
            _ = output.write(f"{name}\n")
            os.environ[WITNESS_FILE_ENV] = str(running)
            sys.stdout = sys.stderr = output
            try:
                result = run_tests(*args, **kwargs)
            except BaseException:
                _ = output.write(f"\n{traceback.format_exc()}")
                _ = running.replace(witness_path(witness_dir, name))
                raise
            finally:
                sys.stdout, sys.stderr = saved
                if named is None:
                    _ = os.environ.pop(WITNESS_FILE_ENV, None)
                else:
                    os.environ[WITNESS_FILE_ENV] = named
        running.unlink()
        return result

    return run


def main(argv: list[CommandWord] | None = None) -> NoReturn:
    """Install the witness in this process, then run mutmut's command line on the rest."""
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    _ = parser.add_argument(
        "--witness-dir",
        type=Path,
        required=True,
        help="the directory each mutant run that does not return leaves its witness in",
    )
    known, rest = parser.parse_known_args(argv)
    witness_dir = cast("Path", known.witness_dir)
    witness_dir.mkdir(parents=True, exist_ok=True)
    # mutmut is the mutation extra's alone, so it is imported where it is used.
    runner = cast("type[PytestRunner]", import_module("mutmut.runners.harness").PytestRunner)
    runner.run_tests = witnessed(runner.run_tests, witness_dir)
    cli = cast("click.Group", import_module("mutmut.__main__").cli)
    cli.main(args=rest, prog_name="mutmut")
    raise SystemExit(0)


if __name__ == "__main__":
    main()
