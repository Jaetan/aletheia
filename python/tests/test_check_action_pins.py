# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the action-pin gate (``tools/check_action_pins.py``).

The gate reports compliance by finding no violations, so an empty result is how
it spells "clean".  That makes the cases where it has NOTHING to read as
important as the cases where it finds a bad pin: a gate that passes while
checking nothing certifies a policy it never applied.  Both are pinned here.

Exit codes: 0 compliant, 1 policy violation, 2 the gate could not check.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import check_action_pins

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

_JOB = "name: x\non: push\njobs:\n  a:\n    runs-on: ubuntu-24.04\n    steps:\n"


def _repo(tmp_path: Path, workflow: str | None) -> Path:
    """Build a fake repo; ``workflow`` None means no .github/workflows at all."""
    if workflow is not None:
        wf_dir = tmp_path / ".github" / "workflows"
        wf_dir.mkdir(parents=True)
        (wf_dir / "ci.yml").write_text(workflow, encoding="utf-8")
    return tmp_path


def _rooted(monkeypatch: pytest.MonkeyPatch, root: Path) -> None:
    """Point the gate's repo-root resolution at an arbitrary directory."""
    monkeypatch.setattr(check_action_pins, "git_toplevel", lambda: root)


def test_missing_workflows_dir_cannot_certify(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """No workflows directory means nothing was read — the gate must not pass."""
    _rooted(monkeypatch, _repo(tmp_path, None))
    assert check_action_pins.main() == 2


def test_zero_matched_refs_cannot_certify(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Workflows present but no ``uses:`` matched: the matcher lost its input.

    Guards the regression where the gate reported
    ``ok (0 refs checked, all comply with pin policy)`` — a green claim about
    nothing, which would survive ``uses:`` syntax drift forever.
    """
    _rooted(monkeypatch, _repo(tmp_path, _JOB + "      - run: echo hi\n"))
    assert check_action_pins.main() == 2


def test_unpinned_third_party_is_a_violation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A third-party action on a branch ref must fail (exit 1, not 2)."""
    _rooted(monkeypatch, _repo(tmp_path, _JOB + "      - uses: evil/action@main\n"))
    assert check_action_pins.main() == 1


def test_compliant_repo_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """The control: a GitHub-owned tag ref complies, so the gate must pass."""
    _rooted(monkeypatch, _repo(tmp_path, _JOB + "      - uses: actions/checkout@v4\n"))
    assert check_action_pins.main() == 0
