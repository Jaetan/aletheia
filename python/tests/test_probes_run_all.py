# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The probe store's runner: each probe's share of the CPUs, and a probe that cannot run.

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
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import TYPE_CHECKING, NewType

import pytest

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

    from aletheia.common_types import PositiveInt

# A probe's file name in the planted store, ``<subject>--<property>.sh``.
ProbeFile = NewType("ProbeFile", str)

RUNNER = Path(__file__).resolve().parents[2] / "probes" / "run_all.sh"
_RECORDS = Path("tools") / "ci-output" / "probes"
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


@cache
def _landlock() -> bool:
    """Whether ``setpriv`` here can apply a Landlock ruleset, as the runner requires."""
    setpriv = shutil.which("setpriv")
    if setpriv is None:
        return False
    probe = [setpriv, "--landlock-access", "fs:write-file", "true"]
    return subprocess.run(probe, capture_output=True, check=False).returncode == 0


def _run_store(
    root: Path,
    probes: Mapping[ProbeFile, Prose],
    *,
    workers: PositiveInt | None = None,
    caller_bound: bool = False,
) -> StoreRun:
    """Plant ``probes`` and the runner in a git work tree at ``root``, and run the runner there.

    ``workers`` sets ``PROBE_WORKERS`` (the runner's default when None). With ``caller_bound``
    the runner starts with a ``PYTHON_CPU_COUNT`` of its own already exported, which it must
    replace; without, the variable is absent and it must export one. Where ``setpriv`` cannot
    apply a Landlock ruleset, the runner refuses, so the test is skipped.
    """
    if not _landlock():
        pytest.skip("setpriv cannot apply a Landlock ruleset here, so the runner refuses")
    git = shutil.which("git")
    assert git is not None
    store = root / "probes"
    store.mkdir()
    _ = shutil.copy2(RUNNER, store / "run_all.sh")
    for name, text in probes.items():
        probe = store / name
        _ = probe.write_text(text, encoding="utf-8")
        probe.chmod(0o755)
    _ = subprocess.run([git, "init", "-q"], cwd=root, check=True)
    _ = subprocess.run([git, "add", "-A"], cwd=root, check=True)
    env = {k: v for k, v in os.environ.items() if k not in {"PYTHON_CPU_COUNT", "PROBE_WORKERS"}}
    if workers is not None:
        env["PROBE_WORKERS"] = str(workers)
    if caller_bound:
        env["PYTHON_CPU_COUNT"] = "99"
    runner = store / "run_all.sh"  # by its own shebang, as the store is run
    run = subprocess.run([runner], cwd=root, env=env, capture_output=True, text=True, check=False)
    return StoreRun(ExitStatus(run.returncode), Prose(run.stdout), Prose(run.stderr))


def _told(root: Path, workers: PositiveInt, *, caller_bound: bool) -> Told:
    """Run the runner over a one-probe store planted at ``root``; return what the probe reported."""
    probes = {ProbeFile("share--is-told.sh"): Prose(_PROBE)}
    run = _run_store(root, probes, workers=workers, caller_bound=caller_bound)
    assert run.status == 1, run.out + run.err
    line = (root / _RECORDS / "share--is-told.log").read_text(encoding="utf-8").strip()
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
    log = _RECORDS / "c--cannot-run-here.log"
    [unrun] = [line for line in lines if line.startswith("UNRUN probes/c--cannot-run-here.sh ")]
    assert unrun.endswith(f" exit 2, 1 lines kept in {log}"), unrun
    assert "    no build to read here" in lines
    assert (tmp_path / log).read_text(encoding="utf-8") == "no build to read here\n"
    [failed] = [line for line in lines if line.startswith("FAIL ")]
    assert failed.startswith("FAIL probes/b--refuses.sh "), failed
    assert lines[-2:] == [
        "probes: 1 passed, 1 failed, 1 did not reach their claim",
        "probes: 3 run, exit 1",
    ]
    record = (tmp_path / _RECORDS / "timings.tsv").read_text(encoding="utf-8")
    verdicts = {row.split("\t")[0]: row.split("\t")[1] for row in record.splitlines()[1:]}
    assert verdicts == {
        "probes/a--passes.sh": "PASS",
        "probes/b--refuses.sh": "FAIL",
        "probes/c--cannot-run-here.sh": "UNRUN",
    }


# A probe that says whether the store's record is there while its run lasts.
_READS_THE_RECORD = Prose(
    _SHEBANG
    + f"if [ -e {_RECORDS}/timings.tsv ]; then echo present; else echo absent; fi\n"
    + "exit 1\n"
)


@pytest.mark.process(_RUNNER_IS_BASH)
def test_the_record_appears_when_the_run_ends(tmp_path: Path) -> None:
    """A fresh store has no record until its run ends, so no reader sees a partial one."""
    run = _run_store(tmp_path, {ProbeFile("r--reads-the-record.sh"): _READS_THE_RECORD})

    assert run.status == 1, run.out + run.err
    seen = (tmp_path / _RECORDS / "r--reads-the-record.log").read_text(encoding="utf-8")
    assert seen == "absent\n"
    record = (tmp_path / _RECORDS / "timings.tsv").read_text(encoding="utf-8")
    assert record.splitlines()[1].startswith("probes/r--reads-the-record.sh\tFAIL\t"), record
    assert not (tmp_path / _RECORDS / "timings.tsv.partial").exists()


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
