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

A mutant that hands the library an address through a C int keeps its low 32
bits, which still name the block wherever the block lies below 2^32, as an
interpreter built without position independence places its heap; one built
with it places the heap above.  Where the lane's own heap starts below 2^32,
it runs mutmut under ``PLACEMENT_ENV``, where glibc's malloc places every
block by mmap, above 4 GiB, and on every host a run whose process's heap
starts below 2^32 when its tests end leaves ``<mutant>.heap`` naming where,
which fails the lane.
With ``--shard K/N`` the wrapper deals mutmut's mutants as cargo-mutants
deals its own: ``collect_source_file_mutation_data``, which lists every
mutant for mutmut's run, is wrapped to keep every N-th of the sorted names
from the K-th, so N runs of one tree test every mutant once between them
(``tools/mutation_python.py`` holds them to that).
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
from typing import TYPE_CHECKING, NamedTuple, NewType, NoReturn, Protocol, cast

if TYPE_CHECKING:
    from collections.abc import Callable, Sequence

    import click
    from mutmut.mutation.data import SourceFileMutationData
    from mutmut.runners.harness import PytestRunner

    from tools._common import CommandWord, EnvName, EnvValue

    # mutmut's listing as its run calls it, which a shard's deal wraps.
    type _MutmutLister = Lister[
        SourceFileMutationData, MutmutExit | None, dict[SourcePath, SourceFileMutationData]
    ]

    class _MutmutMain(Protocol):
        """The part of ``mutmut.__main__`` the witness runs and deals."""

        @property
        def cli(self) -> click.Group:
            """The command line mutmut runs."""
            ...

        @property
        def collect_source_file_mutation_data(self) -> _MutmutLister:
            """The listing mutmut's run calls, looked up in the module as it runs."""
            ...

        @collect_source_file_mutation_data.setter
        def collect_source_file_mutation_data(self, listing: _MutmutLister) -> None:
            """Replace the listing, as the deal does."""


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

# An address in a process's memory.
Address = NewType("Address", int)

# A process's memory map, as /proc/<pid>/maps writes it.
MapsText = NewType("MapsText", str)

# The map a mutant's run reads when its tests end: its own process's.
PROCESS_MAPS = Path("/proc/self/maps")

# Every block by mmap, also past the 65,536 live mmapped blocks after which
# malloc would grow the heap again, which a process running the whole suite passes.
PLACEMENT_ENV: dict[EnvName, EnvValue] = {
    cast("EnvName", "MALLOC_MMAP_THRESHOLD_"): cast("EnvValue", "0"),
    cast("EnvName", "MALLOC_MMAP_MAX_"): cast("EnvValue", "2147483647"),
}

# The suffix of the file a mutant's run leaves when its process's heap starts below 2^32.
LOW_HEAP_SUFFIX = ".heap"

# The first address a C int cannot hold.
_PAST_32_BITS = Address(1 << 32)


def low_heap(maps: MapsText) -> Address | None:
    """Return where the heap ``maps`` names starts, where that is below 2^32, else None."""
    for line in maps.splitlines():
        if line.endswith("[heap]"):
            start = Address(int(line.partition("-")[0], 16))
            return start if start < _PAST_32_BITS else None
    return None


def placement_env(maps: Path) -> dict[EnvName, EnvValue]:
    """Return ``PLACEMENT_ENV`` where ``maps`` puts the heap below 2^32, else nothing.

    Above it the settings change no verdict and slow every allocation.
    """
    heap = low_heap(MapsText(maps.read_text(encoding="utf-8", errors="replace")))
    return {} if heap is None else PLACEMENT_ENV


def _leave_low_heap(witness_dir: Path, mutant: MutantName, maps: Path) -> None:
    """Leave ``<mutant>.heap`` naming where the heap starts, where ``maps`` puts it below 2^32."""
    heap = low_heap(MapsText(maps.read_text(encoding="utf-8", errors="replace")))
    if heap is not None:
        _ = (witness_dir / f"{mutant}{LOW_HEAP_SUFFIX}").write_text(
            f"{heap:#x}\n", encoding="utf-8"
        )


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


def witnessed[**P, R](run_tests: Callable[P, R], witness_dir: Path, maps: Path) -> Callable[P, R]:
    """Return ``run_tests`` wrapped so a mutant's run that does not return leaves its witness.

    ``run_tests`` is mutmut's ``PytestRunner.run_tests``, whose ``mutant_name``
    names the mutant, ``None`` for the runs naming none.  A ``run_tests``
    without that parameter is refused here, before any run.  A run that
    returns or raises reads its process's heap from ``maps`` as it ends.
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
                _leave_low_heap(witness_dir, name, maps)
        running.unlink()
        return result

    return run


# A shard's place among the shards a deal makes, from one, and how many it makes.
ShardPlace = NewType("ShardPlace", int)
ShardCount = NewType("ShardCount", int)

# The text ``--shard`` takes, ``K/N``.
DealText = NewType("DealText", str)


class Deal(NamedTuple):
    """The shard a run tests: the ``place``-th of ``shards``."""

    place: ShardPlace
    shards: ShardCount


def parse_deal(text: DealText) -> Deal:
    """Read ``K/N``, a shard from one to N of N; raise ``argparse.ArgumentTypeError`` else."""
    place, _, shards = text.partition("/")
    if not (place.isdigit() and shards.isdigit() and 1 <= int(place) <= int(shards)):
        message = f"{text!r} is not K/N with 1 <= K <= N"
        raise argparse.ArgumentTypeError(message)
    return Deal(ShardPlace(int(place)), ShardCount(int(shards)))


# A mutant as mutmut's listing gives it: its file's data, its name, its exit so far.
type ListedMutant[Data, Exit] = tuple[Data, MutantName, Exit]

# The mutants mutmut's listing gives it to run.
type ListedMutants[Data, Exit] = list[ListedMutant[Data, Exit]]

# What mutmut's listing returns: the mutants to run, and every file's data by path.
type Listing[Data, Exit, Files] = tuple[ListedMutants[Data, Exit], Files]

# mutmut's listing, called with ``mutant_names`` alone.
type Lister[Data, Exit, Files] = Callable[..., Listing[Data, Exit, Files]]

# A mutant's exit as mutmut files it, and a source file as mutmut keys its data.
MutmutExit = NewType("MutmutExit", int)
SourcePath = NewType("SourcePath", str)


def dealt[D, R](mutants: Sequence[ListedMutant[D, R]], deal: Deal) -> ListedMutants[D, R]:
    """Keep the mutants ``deal`` gives its shard: every N-th of their sorted names from the K-th."""
    names = sorted(name for _, name, _ in mutants)
    mine = set(names[deal.place - 1 :: deal.shards])
    return [mutant for mutant in mutants if mutant[1] in mine]


def dealing[D, R, B](collect: Lister[D, R, B], deal: Deal) -> Lister[D, R, B]:
    """Return mutmut's mutant listing wrapped to keep the mutants ``deal`` gives its shard."""

    def collect_dealt(*, mutant_names: Sequence[MutantName]) -> Listing[D, R, B]:
        mutants, by_path = collect(mutant_names=mutant_names)
        return dealt(mutants, deal), by_path

    return collect_dealt


def main(argv: list[CommandWord] | None = None) -> NoReturn:
    """Install the witness in this process, then run mutmut's command line on the rest."""
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    _ = parser.add_argument(
        "--witness-dir",
        type=Path,
        required=True,
        help="the directory each mutant run that does not return leaves its witness in",
    )
    _ = parser.add_argument(
        "--shard",
        type=lambda text: parse_deal(DealText(text)),
        help="test only the mutants a deal into N shards gives the K-th: K/N",
    )
    known, rest = parser.parse_known_args(argv)
    witness_dir = cast("Path", known.witness_dir)
    witness_dir.mkdir(parents=True, exist_ok=True)
    # mutmut is the mutation extra's alone, so it is imported where it is used.
    runner = cast("type[PytestRunner]", import_module("mutmut.runners.harness").PytestRunner)
    runner.run_tests = witnessed(runner.run_tests, witness_dir, PROCESS_MAPS)
    mutmut_main = cast("_MutmutMain", import_module("mutmut.__main__"))
    deal = cast("Deal | None", known.shard)
    if deal is not None:
        # mutmut's run looks the listing up in its module as it runs.
        mutmut_main.collect_source_file_mutation_data = dealing(
            mutmut_main.collect_source_file_mutation_data, deal
        )
    mutmut_main.cli.main(args=rest, prog_name="mutmut")
    raise SystemExit(0)


if __name__ == "__main__":
    main()
