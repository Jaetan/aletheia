# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``changed_agda_files`` — the iwyu per-push scope collector.

Regression anchor: a branch that DELETES a ``.agda`` module used to crash the
iwyu gate — the deleted path entered the scope and the analyzer's
``read_text`` hit ``FileNotFoundError``.  The fix excludes deletions at
collection time (``--diff-filter=d``): a deleted module has no imports left to
analyze, and its changed importers enter the scope on their own.  Git itself
performs the exclusion, so the test pins the invocation argument and the
mapping behavior around it.
"""

from __future__ import annotations

from types import SimpleNamespace
from typing import TYPE_CHECKING

from tools import _warm

if TYPE_CHECKING:
    import pytest


def _capture_git(monkeypatch: pytest.MonkeyPatch, stdout: str) -> list[list[str]]:
    """Stub ``run_capture`` inside ``_warm``; return the captured argv lists."""
    calls: list[list[str]] = []

    def fake_run_capture(argv: list[str], **_kwargs: object) -> SimpleNamespace:
        calls.append(list(argv))
        return SimpleNamespace(returncode=0, stdout=stdout)

    monkeypatch.setattr(_warm, "run_capture", fake_run_capture)
    return calls


def test_scope_diff_excludes_deleted_files(monkeypatch: pytest.MonkeyPatch) -> None:
    """The git diff that builds the scope must carry ``--diff-filter=d``.

    The exclusion of deleted paths happens inside git; dropping the flag
    reintroduces the FileNotFoundError crash on any module-deleting branch.
    """
    calls = _capture_git(monkeypatch, stdout="")
    assert _warm.changed_agda_files() == []
    assert len(calls) == 1
    argv = calls[0]
    assert "--diff-filter=d" in argv
    assert "main...HEAD" in argv


def test_scope_maps_to_src_relative_sorted(monkeypatch: pytest.MonkeyPatch) -> None:
    """Repo-relative git output maps to sorted src-relative paths; noise drops."""
    _capture_git(
        monkeypatch,
        stdout=(
            "src/Aletheia/Prelude.agda\n"
            "src/Aletheia/CAN/DLC.agda\n"
            "src/Aletheia/README.md\n"  # not .agda — filtered
        ),
    )
    assert _warm.changed_agda_files() == [
        "Aletheia/CAN/DLC.agda",
        "Aletheia/Prelude.agda",
    ]


def test_scope_git_failure_yields_empty_scope(monkeypatch: pytest.MonkeyPatch) -> None:
    """A git failure is surfaced as an empty scope, never a crash."""

    def failing_run_capture(_argv: list[str], **_kwargs: object) -> SimpleNamespace:
        return SimpleNamespace(returncode=128, stdout="")

    monkeypatch.setattr(_warm, "run_capture", failing_run_capture)
    assert _warm.changed_agda_files() == []
