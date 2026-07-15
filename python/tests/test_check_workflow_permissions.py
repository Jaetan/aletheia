# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the workflow-permissions gate (``tools/check_workflow_permissions.py``).

The gate reports compliance by finding no violations, so an empty result is how
it spells "clean".  That makes the cases where it has NOTHING to read as
important as the cases where it finds an over-permissive workflow: a gate that
passes while checking nothing certifies a policy it never applied.  Both are
pinned here.

Exit codes: 0 compliant, 1 policy violation, 2 the gate could not check.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import check_workflow_permissions

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

_STEPS = "jobs:\n  a:\n    runs-on: ubuntu-24.04\n    steps:\n      - run: echo hi\n"
_COMPLIANT = "name: x\non: push\npermissions:\n  contents: read\n" + _STEPS
_NO_PERMISSIONS = "name: x\non: push\n" + _STEPS


def _rooted(monkeypatch: pytest.MonkeyPatch, root: Path) -> None:
    """Point the gate's repo-root resolution at an arbitrary directory."""
    monkeypatch.setattr(check_workflow_permissions, "git_toplevel", lambda: root)


def test_missing_workflows_dir_cannot_certify(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """No workflows directory means nothing was read — the gate must not pass."""
    _rooted(monkeypatch, tmp_path)
    assert check_workflow_permissions.main() == 2


def test_empty_workflows_dir_cannot_certify(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Directory present but zero workflows matched the ``*.y*ml`` glob.

    Guards the regression where the gate reported
    ``ok (0 workflows checked, all declare minimal permissions)`` — a green
    claim about nothing, indistinguishable from real compliance.
    """
    (tmp_path / ".github" / "workflows").mkdir(parents=True)
    _rooted(monkeypatch, tmp_path)
    assert check_workflow_permissions.main() == 2


def test_missing_permissions_block_is_a_violation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A workflow declaring no permissions must fail (exit 1, not 2)."""
    wf = tmp_path / ".github" / "workflows"
    wf.mkdir(parents=True)
    (wf / "ci.yml").write_text(_NO_PERMISSIONS, encoding="utf-8")
    _rooted(monkeypatch, tmp_path)
    assert check_workflow_permissions.main() == 1


def test_compliant_repo_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """The control: a least-privilege top-level block complies."""
    wf = tmp_path / ".github" / "workflows"
    wf.mkdir(parents=True)
    (wf / "ci.yml").write_text(_COMPLIANT, encoding="utf-8")
    _rooted(monkeypatch, tmp_path)
    assert check_workflow_permissions.main() == 0
