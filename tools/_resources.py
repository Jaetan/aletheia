# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared CPU / memory budget detection for the gate tooling.

One place decides "how many threads / how much memory may a gate step use",
so the answer is consistent across ``run_ci`` and the warm-Agda / IWYU lanes
(no more hand-picked ``-N8`` / ``-N4`` that oversubscribe a small CI runner).

The budgets are **CI-aware** and **WSL2-safe**:

* Under a CI runner (``CI`` / ``GITHUB_ACTIONS`` set) use the runner's full
  resources — the VM *is* the allocation, and there is no interactive host to
  protect.
* Locally, reserve headroom: a couple of cores so the host stays responsive
  (sustained 100 %-all-cores can freeze WSL2), and a memory ceiling well under
  the host RAM so WSL2 never balloons into the OOM crash-and-restart that kills
  the session.

The CPU count and the list a pinned run takes read the CPUs the process was
given rather than the machine's, so a run narrowed by ``taskset`` or a cgroup
cpuset stays inside them.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import NewType

# A logical CPU as the kernel numbers it: what an affinity holds.
Cpu = NewType("Cpu", int)
# CPUs as ``taskset -c`` reads them, their numbers joined by commas.
CpuList = NewType("CpuList", str)

# Cores held back locally so the WSL2 host stays interactive (the
# all-cores-100 % freeze hazard).  CI runners need no reserve.
_LOCAL_CORE_RESERVE = 2
# Local memory ceiling (MiB).  The WSL2 effective budget is well under the
# host's physical RAM; staying beneath it avoids the OOM crash-restart.
_LOCAL_MEM_CAP_MB = 30 * 1024
# Fallback when ``/proc/meminfo`` is unreadable (non-Linux, sandbox): assume a
# small machine rather than risk overcommitting.
_MEM_FALLBACK_MB = 4096


def is_ci() -> bool:
    """Return ``True`` when running on a CI runner (full resources allowed).

    Detected via the two signals our CI (GitHub Actions) actually sets — the
    de-facto-standard ``CI=true`` or the unambiguous ``GITHUB_ACTIONS``.  One
    canonical spelling per variable on purpose: we do NOT accept a permissive
    truthy grab-bag (``1`` / ``yes`` / ``on`` …); other providers' ``CI=1`` is
    irrelevant because this project's only CI is GitHub Actions.
    """
    return os.environ.get("CI", "").lower() == "true" or "GITHUB_ACTIONS" in os.environ


def detect_cpus() -> int:
    """Return how many CPUs the process was given, where ``os.cpu_count`` counts the machine."""
    return os.process_cpu_count() or 1


def polite_cpu_list() -> CpuList:
    """Name every CPU the process was given but its highest, as ``taskset -c`` reads them.

    A pinned run keeps one CPU free so the machine stays usable while it
    lasts, and names none it was not given: ``taskset -c`` widens an affinity
    as readily as it narrows one.  A process given one CPU keeps it.
    """
    given = sorted(Cpu(cpu) for cpu in os.sched_getaffinity(0))
    return CpuList(",".join(map(str, given[:-1] or given)))


def cpu_budget() -> int:
    """Return the thread / job count a gate step may use.

    Full core count under CI; locally the count minus a reserved headroom so
    the interactive host never saturates every core at once.
    """
    cpus = detect_cpus()
    if is_ci():
        return cpus
    return max(1, cpus - _LOCAL_CORE_RESERVE)


def _mem_available_mb() -> int | None:
    """Return ``MemAvailable`` from ``/proc/meminfo`` in MiB, or ``None``."""
    try:
        with Path("/proc/meminfo").open(encoding="ascii") as meminfo:
            for line in meminfo:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) // 1024  # kB -> MiB
    except OSError, ValueError, IndexError:
        return None
    return None


def mem_budget_mb() -> int:
    """Return the memory budget (MiB) for scheduling concurrent gate steps.

    The runner's available memory under CI; locally capped to the WSL2-safe
    ceiling so concurrent heavy steps cannot sum past it into an OOM crash.
    """
    available = _mem_available_mb()
    if available is None:
        return _MEM_FALLBACK_MB
    if is_ci():
        return available
    return min(available, _LOCAL_MEM_CAP_MB)
