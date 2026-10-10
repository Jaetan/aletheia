# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The probe store's runner tells each probe its share of the CPUs it was given.

``probes/run_all.sh`` runs a probe only where ``setpriv`` can apply a Landlock
ruleset; where it cannot, as on the CI image, these tests are skipped, saying so.
Each test plants a store of one probe, which prints the ``PYTHON_CPU_COUNT`` it
was started with beside what ``nproc`` answers it, and fails, so the runner keeps
what it printed. The runner divides ``nproc``, which reads the affinity, a
cgroup's CPU quota and the OpenMP limits; the probe inherits all three from the
runner, so its ``nproc`` is the count the runner divided.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

if TYPE_CHECKING:
    from aletheia.common_types import PositiveInt

RUNNER = Path(__file__).resolve().parents[2] / "probes" / "run_all.sh"
_PROBE = (
    "#!/usr/bin/env bash\n"
    'echo "PYTHON_CPU_COUNT=${PYTHON_CPU_COUNT:-unset} NPROC=$(nproc)"\n'
    "exit 1\n"
)
# The one line the probe prints: no bound, or a positive one, and a positive nproc.
_TOLD = re.compile(r"PYTHON_CPU_COUNT=(unset|[1-9][0-9]*) NPROC=([1-9][0-9]*)")


@dataclass(frozen=True)
class Told:
    """What the planted probe reported: the bound it was started with, if any, and its ``nproc``."""

    bound: PositiveInt | None
    nproc: PositiveInt


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


def _told(root: Path, workers: PositiveInt, *, caller_bound: bool) -> Told:
    """Run the runner over a one-probe store planted at ``root``; return what the probe reported.

    With ``caller_bound`` the runner starts with a ``PYTHON_CPU_COUNT`` of its own already
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
    env = {k: v for k, v in os.environ.items() if k != "PYTHON_CPU_COUNT"}
    env["PROBE_WORKERS"] = str(workers)
    if caller_bound:
        env["PYTHON_CPU_COUNT"] = "99"
    runner = probes / "run_all.sh"  # by its own shebang, as the store is run
    run = subprocess.run([runner], cwd=root, env=env, capture_output=True, text=True, check=False)
    assert run.returncode == 1, run.stdout + run.stderr
    log = root / "tools" / "ci-output" / "probes" / "share--is-told.log"
    line = log.read_text(encoding="utf-8").strip()
    seen = _TOLD.fullmatch(line)
    assert seen is not None, f"the probe printed {line!r}, not a bound and an nproc"
    return Told(None if seen[1] == "unset" else int(seen[1]), int(seen[2]))


def _assert_shared(told: Told, workers: PositiveInt) -> None:
    """Assert the probe was told its ``nproc`` divided by ``workers``, and at least one."""
    assert told.bound == max(1, told.nproc // workers), told


def test_each_probe_is_told_the_runners_cpus_divided_by_its_workers(tmp_path: Path) -> None:
    """Four workers over the runner's CPUs: each probe is told a quarter of them."""
    _assert_shared(_told(tmp_path, 4, caller_bound=False), 4)


def test_a_bound_the_caller_exported_is_replaced(tmp_path: Path) -> None:
    """A PYTHON_CPU_COUNT the runner was started with gives way to the share."""
    _assert_shared(_told(tmp_path, 4, caller_bound=True), 4)


def test_a_share_below_one_cpu_is_one(tmp_path: Path) -> None:
    """More workers than CPUs: each probe is told one CPU, never none."""
    workers = len(os.sched_getaffinity(0)) + 1
    told = _told(tmp_path, workers, caller_bound=False)
    _assert_shared(told, workers)
    assert told.bound == 1, told
