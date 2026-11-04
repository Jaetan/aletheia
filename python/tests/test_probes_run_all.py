# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The probe store's runner: each probe's CPU share, a probe that cannot run, and the record.

``probes/run_all.sh`` runs a probe only where ``setpriv`` can apply a Landlock
ruleset; where it cannot, as on the CI image, these tests are skipped, saying so.
The share tests plant a store of one probe, which prints the ``PYTHON_CPU_COUNT``
it was started with beside what ``nproc`` answers it, and fails, so the runner
keeps what it printed. The runner divides ``nproc``, which reads the affinity, a
cgroup's CPU quota and the OpenMP limits; the probe inherits all three from the
runner, so its ``nproc`` is the count the runner divided.

A probe that exits 2 says it cannot reach its claim here: the runner prints it as
UNRUN, keeps it as a failure is kept, records it as UNRUN, counts it apart from the
passes and the failures, and exits non-zero, since it is no pass.

The runner keeps its record in the folder
``python/.venv/bin/python -m tools._records probes`` names, run with the
project's interpreter in the store's checkout: ``probes/<the checkout
directory's name>`` under the records directory, which each planted store is
given by ``ALETHEIA_CI_OUTPUT``, beside the store. Two checkouts of distinct
names sharing that directory keep apart records, so a run in one leaves the
other's as it was. Without that interpreter, or where the module names no
directory, the runner exits 2 having run no probe.
"""

from __future__ import annotations

import os
import re
import shlex
import shutil
import subprocess
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import TYPE_CHECKING, NewType

import pytest

from tools._common import EnvName, EnvValue, run_capture
from tools._records import RECORDS_ENV, environment, probe_records

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

    from aletheia.common_types import PositiveInt

# A probe's file name in the planted store, ``<subject>--<property>.sh``.
ProbeFile = NewType("ProbeFile", str)
# A file of a run's record, read as the runner wrote it.
RecordBytes = NewType("RecordBytes", bytes)

REPO = Path(__file__).resolve().parents[2]
RUNNER = REPO / "probes" / "run_all.sh"
# What the runner names its records directory with, linked untracked into each
# planted store: the package holding the module, and the interpreter.
_TOOLS = Path("tools")
_INTERPRETER = Path("python") / ".venv"
# The directory a store is planted in, under the test's own.
_STORE = Path("store")
_PROBE = (
    "#!/usr/bin/env bash\n"
    'echo "PYTHON_CPU_COUNT=${PYTHON_CPU_COUNT:-unset} NPROC=$(nproc)"\n'
    "exit 1\n"
)
# The one line the probe prints: no bound, or a positive one, and a positive nproc.
_TOLD = re.compile(r"PYTHON_CPU_COUNT=(unset|[1-9][0-9]*) NPROC=([1-9][0-9]*)")
# Why every test starts the runner, and git to make the tree it requires.
_RUNNER_IS_BASH = (
    "the runner is a bash script, so only a started runner shows the share it exports"
    + " to the probe it starts"
)


@dataclass(frozen=True)
class Told:
    """What the planted probe reported: the bound it was started with, if any, and its ``nproc``."""

    bound: PositiveInt | None
    nproc: PositiveInt


@dataclass(frozen=True)
class StoreRun:
    """What one run of the runner gave: its exit status and what it printed."""

    status: ExitStatus
    out: Prose
    err: Prose


@dataclass(frozen=True)
class Start:
    """How a planted store's runner is started.

    ``workers`` sets ``PROBE_WORKERS`` (the runner's default when None). With ``caller_bound``
    the runner starts with a ``PYTHON_CPU_COUNT`` of its own already exported, which it must
    replace; without, the variable is absent and it must export one. ``records`` is the
    ``ALETHEIA_CI_OUTPUT`` it is given, ``_records(tmp)`` when None, whatever the caller
    exported. Without ``interpreter`` the store has no ``python/.venv``.
    """

    workers: PositiveInt | None = None
    caller_bound: bool = False
    records: Path | None = None
    interpreter: bool = True


@cache
def _landlock() -> bool:
    """Whether ``setpriv`` here can apply a Landlock ruleset, as the runner requires."""
    setpriv = shutil.which("setpriv")
    if setpriv is None:
        return False
    probe = [setpriv, "--landlock-access", "fs:write-file", "true"]
    return subprocess.run(probe, capture_output=True, check=False).returncode == 0


def _records(tmp: Path) -> Path:
    """Return the records directory a store planted under ``tmp`` is given, beside the store."""
    return tmp / "records"


def _kept(tmp: Path) -> Path:
    """Return the folder the runner of the store planted at ``tmp / _STORE`` keeps its record in."""
    return probe_records(tmp / _STORE, {RECORDS_ENV: EnvValue(str(_records(tmp)))})


def _plant(root: Path, probes: Mapping[ProbeFile, Prose], *, interpreter: bool) -> Path:
    """Plant ``probes`` and the runner in a git work tree at ``root``; return the runner.

    The tools, and the interpreter unless ``interpreter`` is False, are linked in untracked.
    """
    git = shutil.which("git")
    assert git is not None
    store = root / "probes"
    store.mkdir(parents=True)
    _ = shutil.copy2(RUNNER, store / "run_all.sh")
    for name, text in probes.items():
        probe = store / name
        _ = probe.write_text(text, encoding="utf-8")
        probe.chmod(0o755)
    _ = subprocess.run([git, "init", "-q"], cwd=root, check=True)
    _ = subprocess.run([git, "add", "-A"], cwd=root, check=True)
    for link in (_TOOLS, _INTERPRETER) if interpreter else (_TOOLS,):
        (root / link).parent.mkdir(exist_ok=True)
        (root / link).symlink_to(REPO / link)
    return store / "run_all.sh"


def _environment(tmp: Path, start: Start) -> dict[EnvName, EnvValue]:
    """Return the environment ``start`` gives the runner of a store planted under ``tmp``."""
    bound, workers = EnvName("PYTHON_CPU_COUNT"), EnvName("PROBE_WORKERS")
    env = {k: v for k, v in environment().items() if k not in {bound, workers, RECORDS_ENV}}
    records = _records(tmp) if start.records is None else start.records
    env[RECORDS_ENV] = EnvValue(str(records))
    if start.workers is not None:
        env[workers] = EnvValue(str(start.workers))
    if start.caller_bound:
        env[bound] = EnvValue("99")
    return env


def _run_store(
    tmp: Path,
    probes: Mapping[ProbeFile, Prose],
    start: Start | None = None,
    *,
    store: Path = _STORE,
) -> StoreRun:
    """Plant ``probes`` and the runner in a git work tree at ``tmp / store``, and run it there.

    The runner starts as ``start`` says, or as ``Start()`` does when None. Where ``setpriv``
    cannot apply a Landlock ruleset, the runner refuses, so the test is skipped.
    """
    if not _landlock():
        pytest.skip("setpriv cannot apply a Landlock ruleset here, so the runner refuses")
    start = Start() if start is None else start
    root = tmp / store
    runner = _plant(root, probes, interpreter=start.interpreter)
    env = _environment(tmp, start)
    # The runner by its own shebang, as the store is run.
    run = run_capture([str(runner)], cwd=root, env=env)
    return StoreRun(ExitStatus(run.returncode), Prose(run.stdout), Prose(run.stderr))


def _told(tmp: Path, workers: PositiveInt, *, caller_bound: bool) -> Told:
    """Run the runner over a one-probe store planted under ``tmp``; return what its probe told."""
    probes = {ProbeFile("share--is-told.sh"): Prose(_PROBE)}
    run = _run_store(tmp, probes, Start(workers=workers, caller_bound=caller_bound))
    assert run.status == 1, run.out + run.err
    log = _kept(tmp) / "share--is-told.log"
    assert log.is_file(), run.out + run.err
    line = log.read_text(encoding="utf-8").strip()
    seen = _TOLD.fullmatch(line)
    assert seen is not None, f"the probe printed {line!r}, not a bound and an nproc"
    return Told(None if seen[1] == "unset" else int(seen[1]), int(seen[2]))


def _assert_shared(told: Told, workers: PositiveInt) -> None:
    """Assert the probe was told its ``nproc`` divided by ``workers``, and at least one."""
    assert told.bound == max(1, told.nproc // workers), told


@pytest.mark.process(_RUNNER_IS_BASH)
def test_each_probe_is_told_the_runners_cpus_divided_by_its_workers(tmp_path: Path) -> None:
    """Four workers over the runner's CPUs: each probe is told a quarter of them."""
    _assert_shared(_told(tmp_path, 4, caller_bound=False), 4)


@pytest.mark.process(_RUNNER_IS_BASH)
def test_a_bound_the_caller_exported_is_replaced(tmp_path: Path) -> None:
    """A PYTHON_CPU_COUNT the runner was started with gives way to the share."""
    _assert_shared(_told(tmp_path, 4, caller_bound=True), 4)


@pytest.mark.process(_RUNNER_IS_BASH)
def test_a_share_below_one_cpu_is_one(tmp_path: Path) -> None:
    """More workers than CPUs: each probe is told one CPU, never none."""
    workers = len(os.sched_getaffinity(0)) + 1
    told = _told(tmp_path, workers, caller_bound=False)
    _assert_shared(told, workers)
    assert told.bound == 1, told


# Three probes: one passes, one refuses its claim, one cannot reach it here.
_SHEBANG = "#!/usr/bin/env bash\n"
_VERDICTS = {
    ProbeFile("a--passes.sh"): Prose(_SHEBANG + "exit 0\n"),
    ProbeFile("b--refuses.sh"): Prose(_SHEBANG + "echo 'the claim does not hold'\nexit 1\n"),
    ProbeFile("c--cannot-run-here.sh"): Prose(_SHEBANG + "echo 'no build to read here'\nexit 2\n"),
}


@pytest.mark.process(_RUNNER_IS_BASH)
def test_a_probe_that_exits_2_did_not_run(tmp_path: Path) -> None:
    """Exit 2 reads UNRUN, not FAIL, in its line, its record row and the counts; the run fails."""
    run = _run_store(tmp_path, _VERDICTS)
    lines = run.out.splitlines()

    assert run.status == 1, run.out + run.err
    log = _kept(tmp_path) / "c--cannot-run-here.log"
    [unrun] = [line for line in lines if line.startswith("UNRUN probes/c--cannot-run-here.sh ")]
    assert unrun.endswith(f" exit 2, 1 lines kept in {log}"), unrun
    assert "    no build to read here" in lines
    assert log.is_file(), run.out + run.err
    assert log.read_text(encoding="utf-8") == "no build to read here\n"
    [failed] = [line for line in lines if line.startswith("FAIL ")]
    assert failed.startswith("FAIL probes/b--refuses.sh "), failed
    assert lines[-2:] == [
        "probes: 1 passed, 1 failed, 1 did not reach their claim",
        "probes: 3 run, exit 1",
    ]
    timings = _kept(tmp_path) / "timings.tsv"
    assert timings.is_file(), run.out + run.err
    record = timings.read_text(encoding="utf-8")
    verdicts = {row.split("\t")[0]: row.split("\t")[1] for row in record.splitlines()[1:]}
    assert verdicts == {
        "probes/a--passes.sh": "PASS",
        "probes/b--refuses.sh": "FAIL",
        "probes/c--cannot-run-here.sh": "UNRUN",
    }


def _reads_the_record(kept: Path) -> Prose:
    """Return a probe that says whether the record in ``kept`` is there while its run lasts."""
    record = shlex.quote(str(kept / "timings.tsv"))
    return Prose(
        _SHEBANG + f"if [ -e {record} ]; then echo present; else echo absent; fi\n" + "exit 1\n"
    )


@pytest.mark.process(_RUNNER_IS_BASH)
def test_the_record_appears_when_the_run_ends(tmp_path: Path) -> None:
    """A fresh store has no record until its run ends, so no reader sees a partial one."""
    probes = {ProbeFile("r--reads-the-record.sh"): _reads_the_record(_kept(tmp_path))}
    run = _run_store(tmp_path, probes)

    assert run.status == 1, run.out + run.err
    log = _kept(tmp_path) / "r--reads-the-record.log"
    assert log.is_file(), run.out + run.err
    assert log.read_text(encoding="utf-8") == "absent\n"
    record = (_kept(tmp_path) / "timings.tsv").read_text(encoding="utf-8")
    assert record.splitlines()[1].startswith("probes/r--reads-the-record.sh\tFAIL\t"), record
    assert not (_kept(tmp_path) / "timings.tsv.partial").exists()


@pytest.mark.process(_RUNNER_IS_BASH)
def test_an_unrun_probe_alone_fails_the_run(tmp_path: Path) -> None:
    """A run whose only red is a probe that did not run still exits non-zero."""
    probes = {name: text for name, text in _VERDICTS.items() if name != ProbeFile("b--refuses.sh")}
    run = _run_store(tmp_path, probes)

    assert run.status == 1, run.out + run.err
    assert run.out.splitlines()[-2:] == [
        "probes: 1 passed, 0 failed, 1 did not reach their claim",
        "probes: 2 run, exit 1",
    ]


@pytest.mark.process(_RUNNER_IS_BASH)
def test_a_store_without_the_project_interpreter_runs_no_probe(tmp_path: Path) -> None:
    """Without ``python/.venv`` no records directory is named: exit 2 saying so, no probe run."""
    run = _run_store(tmp_path, _VERDICTS, Start(interpreter=False))

    assert run.status == 2, run.out + run.err
    assert run.out == (
        "run_all: no python/.venv/bin/python, the project's interpreter,"
        + " so no records directory can be named\n"
    )
    assert not _records(tmp_path).exists()


@pytest.mark.process(_RUNNER_IS_BASH)
def test_a_records_directory_it_cannot_name_runs_no_probe(tmp_path: Path) -> None:
    """A relative ``ALETHEIA_CI_OUTPUT``: the module's refusal alone, exit 2, no probe run."""
    run = _run_store(tmp_path, _VERDICTS, Start(records=Path("records")))

    assert (run.status, run.out) == (2, ""), run.out + run.err
    assert run.err == (
        "records: ALETHEIA_CI_OUTPUT names 'records', a relative path;"
        + " it must name an absolute one\n"
    )
    assert not (tmp_path / _STORE / "records").exists()


def _says(word: Prose) -> Prose:
    """Return a probe that prints ``word`` and fails, so the runner keeps what it printed."""
    return Prose(_SHEBANG + f"echo {shlex.quote(word)}\nexit 1\n")


def _kept_log(run: StoreRun) -> Path:
    """Return the file the one failing probe of ``run`` was kept in, as its line names it."""
    [line] = [line for line in run.out.splitlines() if line.startswith("FAIL ")]
    return Path(line.rsplit(" kept in ", 1)[1])


def _contents(paths: tuple[Path, ...]) -> dict[Path, RecordBytes | None]:
    """Return each of ``paths`` with its bytes, or None where no file is."""
    return {path: RecordBytes(path.read_bytes()) if path.is_file() else None for path in paths}


@pytest.mark.process(_RUNNER_IS_BASH)
def test_a_run_in_one_checkout_leaves_another_checkout_s_record_as_it_was(tmp_path: Path) -> None:
    """Two checkouts side by side share one records directory, and keep apart probe records.

    Each checkout's probe fails saying which checkout it is, so each run keeps a log and a
    row of times; the second runs once the first has ended, and the first's log and times
    read the same bytes after it as before.
    """
    first = _run_store(
        tmp_path, {ProbeFile("a--says-first.sh"): _says(Prose("first"))}, store=Path("first")
    )
    assert first.status == 1, first.out + first.err
    log = _kept_log(first)
    record = (log, log.parent / "timings.tsv")
    kept = _contents(record)
    assert kept[log] == b"first\n", first.out
    assert kept[record[1]] is not None, first.out

    second = _run_store(
        tmp_path, {ProbeFile("b--says-second.sh"): _says(Prose("second"))}, store=Path("second")
    )
    assert second.status == 1, second.out + second.err
    assert _contents(record) == kept, second.out
