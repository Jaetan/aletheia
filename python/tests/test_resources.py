# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._resources`` — CI-aware, WSL2-safe CPU / memory budgets.

The budgets shield three failure modes: local host unresponsiveness (reserve
core headroom), CI overcommitting (use the runner's real count), and the OOM
crash-restart (cap memory locally).  Inputs are monkeypatched so the behaviour
is asserted deterministically regardless of the host actually running the suite.
"""

from __future__ import annotations

import os
from typing import TYPE_CHECKING

from tools import _resources
from tools._resources import cpu_budget, detect_cpus, is_ci, mem_budget_mb

if TYPE_CHECKING:
    import pytest


def _clear_ci(monkeypatch: pytest.MonkeyPatch) -> None:
    """Force the not-on-CI environment."""
    monkeypatch.delenv("CI", raising=False)
    monkeypatch.delenv("GITHUB_ACTIONS", raising=False)


def test_is_ci_true_on_ci_env(monkeypatch: pytest.MonkeyPatch) -> None:
    """``CI=true`` is recognised as a CI runner."""
    monkeypatch.setenv("CI", "true")
    assert is_ci() is True


def test_is_ci_true_on_github_actions(monkeypatch: pytest.MonkeyPatch) -> None:
    """``GITHUB_ACTIONS`` present (any value) is recognised as a CI runner."""
    monkeypatch.delenv("CI", raising=False)
    monkeypatch.setenv("GITHUB_ACTIONS", "true")
    assert is_ci() is True


def test_is_ci_false_locally(monkeypatch: pytest.MonkeyPatch) -> None:
    """No CI markers ⇒ treated as the interactive local host."""
    _clear_ci(monkeypatch)
    assert is_ci() is False


def test_detect_cpus_counts_the_process_not_the_machine(monkeypatch: pytest.MonkeyPatch) -> None:
    """A run narrowed by ``taskset`` or a cpuset counts the CPUs it was given."""
    monkeypatch.setattr(os, "cpu_count", lambda: 24)
    monkeypatch.setattr(os, "process_cpu_count", lambda: 3)
    assert detect_cpus() == 3


def test_detect_cpus_is_one_where_the_count_is_unknown(monkeypatch: pytest.MonkeyPatch) -> None:
    """A platform that cannot say still yields a usable count."""
    monkeypatch.setattr(os, "process_cpu_count", lambda: None)
    assert detect_cpus() == 1


def test_cpu_budget_uses_full_count_on_ci(monkeypatch: pytest.MonkeyPatch) -> None:
    """Under CI the budget is the runner's full core count (no reserve)."""
    monkeypatch.setenv("CI", "true")
    monkeypatch.setattr(_resources, "detect_cpus", lambda: 8)
    assert cpu_budget() == 8


def test_cpu_budget_reserves_headroom_locally(monkeypatch: pytest.MonkeyPatch) -> None:
    """Locally the budget leaves headroom (the all-cores-100% freeze guard)."""
    _clear_ci(monkeypatch)
    monkeypatch.setattr(_resources, "detect_cpus", lambda: 8)
    budget = cpu_budget()
    assert 1 <= budget < 8


def test_cpu_budget_floored_at_one_locally(monkeypatch: pytest.MonkeyPatch) -> None:
    """A tiny local host still yields a usable budget of at least one."""
    _clear_ci(monkeypatch)
    monkeypatch.setattr(_resources, "detect_cpus", lambda: 1)
    assert cpu_budget() == 1


def test_mem_budget_uses_available_on_ci(monkeypatch: pytest.MonkeyPatch) -> None:
    """Under CI the memory budget is the runner's available memory, uncapped."""
    monkeypatch.setenv("CI", "true")
    monkeypatch.setattr(_resources, "_mem_available_mb", lambda: 12345)
    assert mem_budget_mb() == 12345


def test_mem_budget_capped_locally(monkeypatch: pytest.MonkeyPatch) -> None:
    """Locally a huge available figure is capped to the WSL2-safe ceiling."""
    _clear_ci(monkeypatch)
    monkeypatch.setattr(_resources, "_mem_available_mb", lambda: 10**9)
    assert mem_budget_mb() < 10**9


def test_mem_budget_fallback_when_unreadable(monkeypatch: pytest.MonkeyPatch) -> None:
    """An unreadable ``/proc/meminfo`` yields a positive conservative fallback."""
    monkeypatch.setattr(_resources, "_mem_available_mb", lambda: None)
    assert mem_budget_mb() >= 1
