# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_run`` diff-scoping.

``bindings_in_scope`` decides which binding engines run on a PR.  The contract:

* per-binding scoping is GENEROUS (the whole binding dir — tests and config
  included) because mutmut / Mull kill mutants by RUNNING the binding's tests,
  so a test-only or config-only edit can change a binding's survivor count.
  Under-scoping a binding would silently skip a real regression, so the witness
  cases here are a ``python/tests/``-only and a ``cpp/tests/``-only diff: both
  MUST still scope their binding in;
* the GLOBAL set (the shared ``.so`` / this harness / the baselines) and the
  empty-diff / git-error / escape-hatch cases all fail SAFE to ``None`` (run
  everything);
* a docs-only diff scopes to the empty set (run nothing) — and the public
  ``main`` must still exit 0 there so the REQUIRED ``mutation testing`` check
  stays green ([[feedback_orchestrator_end_to_end_validation]]).

Mirrors ``test_check_changelog``: the pure decision function is unit-tested, the
orchestration is covered through a ``main`` end-to-end with monkeypatched runners
(no private-member access — see [[feedback_test_interface_via_di]]).
"""

from __future__ import annotations

import subprocess
from typing import TYPE_CHECKING

import pytest

from tools import mutation_run

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path


def _fake_diff(monkeypatch: pytest.MonkeyPatch, *, files: list[str], returncode: int = 0) -> None:
    """Make ``mutation_run.run_capture`` return a canned ``git diff`` result.

    Only ``bindings_in_scope`` resolves ``run_capture`` through the
    ``mutation_run`` namespace; ``short_sha`` uses ``_common``'s own reference,
    so this fake does not perturb SHA computation.
    """
    stdout = "".join(f"{f}\n" for f in files)

    def fake(cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(cmd, returncode, stdout=stdout, stderr="")

    monkeypatch.setattr(mutation_run, "run_capture", fake)


@pytest.mark.parametrize(
    ("files", "expected"),
    [
        # per-binding source
        (["go/aletheia/check.go"], {"go"}),
        (["python/aletheia/checks.py"], {"python"}),
        (["cpp/src/client.cpp"], {"cpp"}),
        # per-binding TESTS — the under-scoping regression witnesses
        (["python/tests/test_checks.py"], {"python"}),
        (["cpp/tests/test_client.cpp"], {"cpp"}),
        # per-binding config (changes what gets mutated / how tests build)
        (["python/pyproject.toml"], {"python"}),
        (["cpp/CMakeLists.txt"], {"cpp"}),
        # multiple bindings
        (["go/aletheia/check.go", "python/aletheia/checks.py"], {"go", "python"}),
        # docs-only → run NONE (main still exits 0; see the e2e below)
        (["README.md", "docs/PITCH.md"], set[str]()),
    ],
)
def test_scope_matches_changed_bindings(
    monkeypatch: pytest.MonkeyPatch, files: list[str], expected: set[str]
) -> None:
    """Each changed binding directory (source, tests, or config) is scoped in."""
    _fake_diff(monkeypatch, files=files)
    assert mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) == expected


@pytest.mark.parametrize(
    "files",
    [
        ["src/Aletheia/Main.agda"],  # Agda → MAlonzo → .so
        ["haskell-shim/src/AletheiaFFI.hs"],  # FFI shim → .so
        ["Shakefile.hs"],  # build graph → .so
        ["aletheia.agda-lib"],  # build graph → .so
        ["docs/MUTATION_BENCH.yaml"],  # the baselines the drift gate reads
        ["tools/mutation_run.py"],  # this harness
        ["tools/_common.py"],  # the harness's shared helpers
        [".github/workflows/pr-heavy-lanes.yml"],  # the lane definition
        ["go/aletheia/check.go", "src/X.agda"],  # a global path wins over a binding
    ],
)
def test_global_paths_force_all_bindings(monkeypatch: pytest.MonkeyPatch, files: list[str]) -> None:
    """A change to the shared .so / harness / baselines forces the full run."""
    _fake_diff(monkeypatch, files=files)
    assert mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) is None


def test_empty_diff_runs_all(monkeypatch: pytest.MonkeyPatch) -> None:
    """push:main / on-main: HEAD == main → empty diff → the full backstop run."""
    _fake_diff(monkeypatch, files=[])
    assert mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) is None


def test_git_error_fails_safe_to_all(monkeypatch: pytest.MonkeyPatch) -> None:
    """No ``main`` ref / git error: run everything rather than silently skip."""
    _fake_diff(monkeypatch, files=["go/aletheia/check.go"], returncode=128)
    assert mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) is None


def test_git_binary_absent_fails_safe_to_all(monkeypatch: pytest.MonkeyPatch) -> None:
    """No ``git`` binary on PATH (find_executable raises): run all, never crash."""

    def _no_git(_name: str) -> str:
        msg = "required executable not found on PATH: git"
        raise RuntimeError(msg)

    monkeypatch.setattr(mutation_run, "find_executable", _no_git)
    assert mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) is None


def test_escape_hatch_forces_all(monkeypatch: pytest.MonkeyPatch) -> None:
    """The documented escape-hatch env var forces the full run."""
    # Pin the env-var NAME as a contract (not the private constant symbol).
    monkeypatch.setenv("ALETHEIA_MUTATION_NO_DIFF_SCOPE", "1")
    _fake_diff(monkeypatch, files=["go/aletheia/check.go"])
    assert mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) is None


def _recording_runners(
    ran: list[str],
) -> list[tuple[str, str, Callable[[Path], mutation_run.MutationReport]]]:
    """Build a RUNNERS list whose runners record their name and report 0 survivors."""

    def make(name: str) -> Callable[[Path], mutation_run.MutationReport]:
        def runner(_artifact_dir: Path) -> mutation_run.MutationReport:
            ran.append(name)
            return mutation_run.MutationReport(name, "fake", killed=1, survived=0, raw_log="")

        return runner

    return [
        ("python", "ALETHEIA_MUTATION_SKIP_PYTHON", make("python")),
        ("go", "ALETHEIA_MUTATION_SKIP_GO", make("go")),
        ("cpp", "ALETHEIA_MUTATION_SKIP_CPP", make("cpp")),
    ]


def _fixed_sha(_root: Path | None = None) -> str:
    """Stand in for ``short_sha`` with a constant under the sandbox."""
    return "testsha"


def _sandbox_main(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, *, files: list[str], ran: list[str]
) -> None:
    """Point ``main``'s repo-root / artifact-base / SHA at a writable sandbox.

    ``SPEC_PATH`` was bound to the real repo at import, so the real per-binding
    baselines still load; only the artifact tree and the diff are sandboxed.
    """
    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "ARTIFACT_BASE", tmp_path / "artifacts")
    monkeypatch.setattr(mutation_run, "short_sha", _fixed_sha)
    monkeypatch.setattr(mutation_run, "RUNNERS", _recording_runners(ran))
    _fake_diff(monkeypatch, files=files)


def test_main_runs_only_changed_binding(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """End-to-end via public main(): a go-only diff runs only the go engine."""
    ran: list[str] = []
    _sandbox_main(monkeypatch, tmp_path, files=["go/aletheia/check.go"], ran=ran)
    assert mutation_run.main() == 0
    assert ran == ["go"]


def test_main_docs_only_runs_nothing_and_passes(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A docs-only diff runs zero engines, yet main() exits 0 (required → green)."""
    ran: list[str] = []
    _sandbox_main(monkeypatch, tmp_path, files=["README.md"], ran=ran)
    assert mutation_run.main() == 0
    assert not ran  # no engine ran


def test_run_python_erases_stale_mutants_tree(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """run_python wipes python/mutants/ before invoking mutmut.

    mutmut's persistent work-tree only invalidates cached kill/survive verdicts
    on SOURCE changes, not TEST changes, so a reused tree yields stale results
    (a merge that added a function plus its killing tests once reported phantom
    survivors).  The gate must start each run from a clean tree — CI parity,
    since CI checks out fresh.
    """

    def fake_tools() -> tuple[Path, Path]:
        return (tmp_path / "mutmut", tmp_path / "lib.so")

    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "_check_python_tools", fake_tools)

    stale = tmp_path / "python" / "mutants"
    stale.mkdir(parents=True)
    (stale / "poisoned.txt").write_text("verdict cached from a prior tree")

    def fake_run(cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
        # The stale tree must already be gone before mutmut is ever invoked.
        assert not stale.exists(), "run_python invoked mutmut without erasing mutants/"
        return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")

    monkeypatch.setattr(mutation_run.subprocess, "run", fake_run)
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()

    mutation_run.run_python(artifacts)

    assert not stale.exists()
