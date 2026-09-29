# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ sweep runs inside the CPUs it was given.

The sweep pins its runner with ``taskset -c``, which widens an affinity as
readily as it narrows one, so a list counted from the machine re-pins a run
launched on part of it onto CPUs it was never given.  The machine and the
affinity are faked so the two disagree on every host, and the given CPUs are
neither zero-based nor contiguous, which is what a list counted up from zero
gets wrong; nor does a set of them iterate in order, so the CPU left free is
the highest because it was chosen, not because it came last.
"""

from __future__ import annotations

import os
import shutil
from typing import TYPE_CHECKING

from tools._resources import Cpu
from tools.mutation_sweep_cache import polite

if TYPE_CHECKING:
    import pytest

_MACHINE = 24
_GIVEN = frozenset({Cpu(4), Cpu(5), Cpu(9), Cpu(10)})
_RUNNER = ["mull-runner-23", "unit_tests"]


def _taskset(_name: str) -> str:
    """Find taskset, as a host that has it does."""
    return "/usr/bin/taskset"


def _nowhere(_name: str) -> None:
    """Find nothing, as a host without taskset does."""


def _given(monkeypatch: pytest.MonkeyPatch, cpus: frozenset[Cpu]) -> None:
    """Fake a machine of 24 CPUs with taskset installed, the process given ``cpus``."""

    def affinity(_pid: int) -> set[int]:
        return set(cpus)

    monkeypatch.setattr(os, "cpu_count", lambda: _MACHINE)
    monkeypatch.setattr(os, "sched_getaffinity", affinity)
    monkeypatch.setattr(shutil, "which", _taskset)


def _pinned(argv: list[str]) -> frozenset[Cpu]:
    """Read the CPUs a ``taskset -c`` prefix names, ranges included."""
    assert argv[:2] == ["taskset", "-c"]
    cpus: set[Cpu] = set()
    for part in argv[2].split(","):
        low, _, high = part.partition("-")
        cpus.update(Cpu(cpu) for cpu in range(int(low), int(high or low) + 1))
    return frozenset(cpus)


def test_the_sweep_is_pinned_inside_the_cpus_it_was_given(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every given CPU but the highest, and none outside them."""
    _given(monkeypatch, _GIVEN)
    argv = polite(_RUNNER)
    assert _pinned(argv) == _GIVEN - {max(_GIVEN)}
    assert argv[3:] == _RUNNER


def test_a_sweep_given_one_cpu_keeps_it(monkeypatch: pytest.MonkeyPatch) -> None:
    """There is no CPU to leave, so the sweep runs on the one it has."""
    _given(monkeypatch, frozenset({Cpu(7)}))
    assert _pinned(polite(_RUNNER)) == {Cpu(7)}


def test_without_taskset_the_runner_is_left_alone(monkeypatch: pytest.MonkeyPatch) -> None:
    """A host without the tool runs the argv as the lane wrote it."""
    monkeypatch.setattr(shutil, "which", _nowhere)
    assert polite(_RUNNER) == _RUNNER
