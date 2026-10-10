# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The probe store's runner tells each probe its share of the CPUs it was given.

``probes/run_all.sh`` runs a probe only where ``setpriv`` can apply a Landlock
ruleset; where it cannot, as on the CI image, these tests are skipped, saying so.
Each test plants a store of one probe, which prints the ``PYTHON_CPU_COUNT`` it
was started with and fails, so the runner keeps what it printed.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

from tools._common import WorkerCount

from aletheia.common_types import Prose

RUNNER = Path(__file__).resolve().parents[2] / "probes" / "run_all.sh"
_PROBE = '#!/usr/bin/env bash\necho "PYTHON_CPU_COUNT=${PYTHON_CPU_COUNT:-unset}"\nexit 1\n'


def _landlock() -> bool:
    """Whether ``setpriv`` here can apply a Landlock ruleset, as the runner requires."""
    setpriv = shutil.which("setpriv")
    if setpriv is None:
        return False
    probe = [setpriv, "--landlock-access", "fs:write-file", "true"]
    return subprocess.run(probe, capture_output=True, check=False).returncode == 0


pytestmark = pytest.mark.skipif(
    not _landlock(), reason="setpriv cannot apply a Landlock ruleset here, so the runner refuses"
)


def _told(root: Path, workers: WorkerCount, *, caller_bound: bool) -> Prose:
    """Run the runner over a planted one-probe store at ``root``; return what the probe was told.

    With ``caller_bound`` the runner is started with a ``PYTHON_CPU_COUNT`` of its own already
    exported, which it must replace; without, the variable is absent and it must export one.
    """
    git = shutil.which("git")
    assert git is not None
    probes = root / "probes"
    probes.mkdir()
    _ = shutil.copy2(RUNNER, probes / "run_all.sh")
    probe = probes / "share--is-told.sh"
    _ = probe.write_text(_PROBE, encoding="utf-8")
    probe.chmod(0o755)
    _ = subprocess.run([git, "init", "-q"], cwd=root, check=True)
    _ = subprocess.run([git, "add", "-A"], cwd=root, check=True)
    # nproc reads the affinity alone once the OpenMP limits it also honours are gone.
    dropped = ("OMP_NUM_THREADS", "OMP_THREAD_LIMIT", "PYTHON_CPU_COUNT")
    env = {k: v for k, v in os.environ.items() if k not in dropped}
    env["PROBE_WORKERS"] = str(workers)
    if caller_bound:
        env["PYTHON_CPU_COUNT"] = "99"
    runner = probes / "run_all.sh"  # by its own shebang, as the store is run
    run = subprocess.run([runner], cwd=root, env=env, capture_output=True, text=True, check=False)
    assert run.returncode == 1, run.stdout + run.stderr
    log = root / "tools" / "ci-output" / "probes" / "share--is-told.log"
    return Prose(log.read_text(encoding="utf-8").strip())


def test_each_probe_is_told_the_runners_cpus_divided_by_its_workers(tmp_path: Path) -> None:
    """Four workers over the runner's CPUs: each probe is told a quarter of them."""
    cpus = len(os.sched_getaffinity(0))
    told = _told(tmp_path, WorkerCount(4), caller_bound=False)
    assert told == f"PYTHON_CPU_COUNT={max(1, cpus // 4)}"


def test_a_bound_the_caller_exported_is_replaced(tmp_path: Path) -> None:
    """A PYTHON_CPU_COUNT the runner was started with gives way to the share."""
    cpus = len(os.sched_getaffinity(0))
    told = _told(tmp_path, WorkerCount(4), caller_bound=True)
    assert told == f"PYTHON_CPU_COUNT={max(1, cpus // 4)}"


def test_a_share_below_one_cpu_is_one(tmp_path: Path) -> None:
    """More workers than CPUs: each probe is told one CPU, never none."""
    cpus = len(os.sched_getaffinity(0))
    assert _told(tmp_path, WorkerCount(cpus + 1), caller_bound=False) == "PYTHON_CPU_COUNT=1"
