# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Guards for the generated git-hook bodies in ``tools/install_hooks.py``.

The hook bodies are f-strings, so any literal ``{`` in the embedded shell / git
commands must be doubled (``{{``) or the f-string silently substitutes it.  A
``stash@{0}`` that rendered as ``stash@0`` once disabled the whole pre-commit
stash-restore path (an invalid git ref → no restore → lost unstaged work), and
``compile()`` does NOT catch it (``stash@0`` is valid string content).  Pin the
rendered bodies here.
"""

from __future__ import annotations

import importlib.util
import subprocess
from typing import TYPE_CHECKING, cast

from tools.install_hooks import PRE_COMMIT_BODY, PRE_PUSH_BODY

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path

    import pytest


def test_hook_bodies_are_valid_python() -> None:
    """Both generated hook bodies compile (an f-string typo can break them)."""
    compile(PRE_COMMIT_BODY, "<pre-commit>", "exec")
    compile(PRE_PUSH_BODY, "<pre-push>", "exec")


def test_pre_commit_stash_ref_survived_the_fstring() -> None:
    """The stash ref renders as ``stash@{0}`` — the f-string must not eat the braces.

    ``stash@{0}`` in an f-string body renders the ``{0}`` field as ``0`` unless
    doubled to ``{{0}}``; the resulting ``stash@0`` is an invalid git ref that
    silently disables the hook's stash restore. Compilation can't catch it.
    """
    assert "stash@{0}" in PRE_COMMIT_BODY
    assert "stash@0" not in PRE_COMMIT_BODY


def _load_pre_commit(tmp_path: Path) -> dict[str, object]:
    """Import the rendered pre-commit body as a module and return its namespace.

    The body guards ``main`` behind ``__main__``, so importing it runs nothing
    and yields a namespace whose entries a test can replace, ``_run`` included.
    """
    script = tmp_path / "pre_commit.py"
    script.write_text(PRE_COMMIT_BODY, encoding="utf-8")
    spec = importlib.util.spec_from_file_location("aletheia_pre_commit_under_test", script)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return vars(module)


def _gate(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    iwyu: subprocess.CompletedProcess[str],
) -> tuple[int, str, list[str]]:
    """Run the hook's IWYU gate with one staged file and a canned IWYU result.

    Returns the gate's exit code, what it wrote to stderr, and the IWYU command
    line it built.
    """
    staged = tmp_path / "src" / "Aletheia" / "Staged.agda"
    staged.parent.mkdir(parents=True)
    staged.write_text("", encoding="utf-8")
    hook = _load_pre_commit(tmp_path)
    iwyu_args: list[str] = []

    def fake_run(args: list[str], cwd: object = None) -> subprocess.CompletedProcess[str]:
        del cwd
        assert args[:2] == ["git", "diff"], args
        return subprocess.CompletedProcess(args, 0, "src/Aletheia/Staged.agda\n", "")

    def fake_run_iwyu(rels: list[str], cwd: object) -> subprocess.CompletedProcess[str]:
        del cwd
        iwyu_args.extend(rels)
        return iwyu

    hook["_run"] = fake_run
    hook["_run_iwyu"] = fake_run_iwyu
    gate = cast("Callable[[Path], int]", hook["_iwyu_gate"])
    rc = gate(tmp_path)
    assert iwyu_args == ["Aletheia/Staged.agda"]
    return rc, capsys.readouterr().err, iwyu_args


def test_pre_commit_iwyu_gate_refuses_a_run_that_never_happened(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A non-zero exit with nothing on stdout is a run that never reached a verdict.

    Its reason went to the terminal live, so the hook names that, refuses the
    commit, and never dresses the absence of a report up as findings.
    """
    rc, err, _ = _gate(tmp_path, capsys, subprocess.CompletedProcess([], 1, "", None))
    assert rc == 1
    assert "could not run" in err
    assert "refused" in err
    assert "flagged" not in err
    assert "tools.iwyu --check Aletheia/Staged.agda" in err


def test_pre_commit_iwyu_gate_refuses_findings_with_their_report(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A non-zero exit with a report on stdout is findings, and they block."""
    report = (
        "  DEAD Aletheia/Staged.agda: foo (unused named import — remove)\n"
        "=== iwyu: 1 finding(s) ===\n"
    )
    rc, err, _ = _gate(tmp_path, capsys, subprocess.CompletedProcess([], 1, report, None))
    assert rc == 1
    assert "flagged" in err
    assert "DEAD Aletheia/Staged.agda" in err
    assert "refused" in err
    assert "could not run" not in err


def test_pre_commit_iwyu_gate_passes_a_clean_run(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A zero exit passes and says nothing beyond announcing the gate."""
    rc, err, _ = _gate(tmp_path, capsys, subprocess.CompletedProcess([], 0, "", None))
    assert rc == 0
    assert "flagged" not in err
    assert "could not run" not in err


def test_pre_commit_iwyu_gate_queues_behind_the_agda_lock() -> None:
    """The hook's IWYU command carries the wait flag: a sweep delays a commit, never fails it."""
    assert '"--check", "--wait-lock"' in PRE_COMMIT_BODY
