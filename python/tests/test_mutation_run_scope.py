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
* the GLOBAL set (the shared ``.so`` / this harness / the Mull build / the baselines) and the
  empty-diff / git-error / escape-hatch cases all fail SAFE to ``None`` (run
  everything);
* a docs-only diff scopes to the empty set (run nothing) — and the public
  ``main`` must still exit 0 there so the REQUIRED ``mutation testing`` check
  stays green (the orchestrator's own end-to-end validation).

Mirrors ``test_check_changelog``: the pure decision function is unit-tested, the
orchestration is covered through a ``main`` end-to-end with monkeypatched runners
(no private-member access — test access goes through the interface or a DI seam).
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple
from unittest.mock import Mock

import pytest

from tools import _branch_diff, mutation_run
from tools._common import RelPath, git_ls_files
from tools.mutation_report import CrashedMutant, DriftStatus, MutantCount
from tools.mutation_witness import TALLY_FILE

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable

    from tools.mutation_report import Spec


def _fake_diff(monkeypatch: pytest.MonkeyPatch, *, files: list[str], returncode: int = 0) -> None:
    """Make the branch-diff reading return a canned ``git diff`` result.

    Only the diff reading resolves ``run_capture`` through the
    ``_branch_diff`` namespace; ``short_sha`` uses ``_common``'s own reference,
    so this fake does not perturb SHA computation.
    """
    stdout = "".join(f"{f}\n" for f in files)

    def fake(cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(cmd, returncode, stdout=stdout, stderr="")

    monkeypatch.setattr(_branch_diff, "run_capture", fake)


@pytest.mark.parametrize(
    ("files", "expected"),
    [
        # per-binding source
        (["go/aletheia/check.go"], {"go"}),
        (["python/aletheia/checks.py"], {"python"}),
        (["cpp/src/client.cpp"], {"cpp"}),
        (["rust/src/backend.rs"], {"rust"}),
        # per-binding TESTS — the under-scoping regression witnesses
        (["python/tests/test_checks.py"], {"python"}),
        (["cpp/tests/test_client.cpp"], {"cpp"}),
        (["rust/tests/frame_ops.rs"], {"rust"}),
        # per-binding config (changes what gets mutated / how tests build)
        (["python/pyproject.toml"], {"python"}),
        (["rust/.cargo/mutants.toml"], {"rust"}),
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
        ["shake/Rules/Library.hs"],  # the build graph's rules → .so
        ["aletheia.agda-lib"],  # build graph → .so
        ["docs/MUTATION_BENCH.yaml"],  # the baselines the drift gate reads
        ["tools/mutation_run.py"],  # the harness's runner
        ["tools/mutation_scope.py"],  # what a CI lane asks before installing a toolchain
        ["tools/mutation_cpp.py"],  # the C++ lane, whose merge no binding directory names
        ["tools/mutation_cpp_slices.py"],  # the partition the C++ legs are cut on
        ["tools/mutation_report.py"],  # the shapes every lane reports in
        ["tools/mutation_routes.py"],  # the kill-route census
        ["tools/cpp_scratch.py"],  # the scratch-directory reaping the C++ lane imports
        ["tools/mull/libirm-call-replacement-indirect.patch"],  # what the plugin mutates
        ["tools/build_mull.sh"],  # the Mull release and the patches the plugin is built with
        ["tools/_common.py"],  # the harness's shared helpers
        [".github/workflows/pr-heavy-lanes.yml"],  # the lane definition
        ["go/aletheia/check.go", "src/X.agda"],  # a global path wins over a binding
    ],
)
def test_global_paths_force_all_bindings(monkeypatch: pytest.MonkeyPatch, files: list[str]) -> None:
    """A change to the shared .so / harness / Mull build / baselines forces the full run."""
    _fake_diff(monkeypatch, files=files)
    assert mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) is None


# Prints the file of every module of the tools package the harness loads.
_HARNESS_MODULES = """import sys
import tools.mutation_run
import tools.mutation_scope
for name, module in sorted(sys.modules.items()):
    if (name == "tools" or name.startswith("tools.")) and getattr(module, "__file__", None):
        print(module.__file__)
"""


def _forces_all(monkeypatch: pytest.MonkeyPatch, relative: RelPath) -> bool:
    """Say whether a diff touching only ``relative`` runs every binding's lane."""
    _fake_diff(monkeypatch, files=[relative])
    return mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) is None


@pytest.mark.process(
    "a fresh interpreter binds only what the harness imports; this one holds every test's imports"
)
def test_every_module_the_harness_loads_forces_all_bindings(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The global paths cover every module the harness runs on, read from what it imports."""
    loaded = subprocess.run(
        [sys.executable, "-c", _HARNESS_MODULES],
        cwd=mutation_run.REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split()
    relatives = [
        RelPath(Path(path).relative_to(mutation_run.REPO_ROOT).as_posix()) for path in loaded
    ]
    assert RelPath("tools/mutation_run.py") in relatives
    assert not [relative for relative in relatives if not _forces_all(monkeypatch, relative)]


@pytest.mark.process(
    "which harness modules the live tree tracks is git's own answer, not a glob of the work tree"
)
def test_every_tracked_harness_module_forces_all_bindings(monkeypatch: pytest.MonkeyPatch) -> None:
    """A harness module added later is covered the day it is tracked, not the day someone lists it.

    The parametrised cases above name the modules the harness has today; this
    one reads the tree, so a module the harness grows cannot slip past the
    scope the way one would past a list.
    """
    tracked = git_ls_files(mutation_run.REPO_ROOT, "tools/mutation_*.py")
    assert len(tracked) >= 2, tracked  # the runner and the scope question at least
    for module in tracked:
        _fake_diff(monkeypatch, files=[module])
        assert mutation_run.bindings_in_scope(mutation_run.REPO_ROOT) is None, module


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

    monkeypatch.setattr(_branch_diff, "find_executable", _no_git)
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


def _unrecorded_spec() -> Spec:
    """Stand in for the record with every binding and no baseline, so a run is a first run."""
    return {"bindings": {"python": {}, "go": {}, "cpp": {}, "rust": {}}}


def _sandbox_main(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, *, files: list[str], ran: list[str]
) -> None:
    """Point ``main``'s repo-root / artifact-base / SHA at a writable sandbox.

    The record is a stand-in that names every binding and records nothing, so
    a stand-in run is a first run and the verdict is the scope's alone; the
    artifact tree and the diff are sandboxed too, and ``main`` runs with no
    argument.
    """
    monkeypatch.setattr("sys.argv", ["mutation_run"])
    for binding in ("PYTHON", "GO", "CPP", "RUST"):
        monkeypatch.delenv(f"ALETHEIA_MUTATION_SKIP_{binding}", raising=False)
    monkeypatch.setattr(mutation_run, "load_spec", _unrecorded_spec)
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


def _one_survivor_recorded() -> Spec:
    """Stand in for the record with one Go survivor, which a stand-in run does not leave."""
    return {"bindings": {"go": {"baseline": {"survivors": 1}}}}


def test_main_fails_a_run_better_than_the_record(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A stale record fails the lane as a regression does, until the change lowers it."""
    _sandbox_main(monkeypatch, tmp_path, files=["go/aletheia/check.go"], ran=[])
    monkeypatch.setattr(mutation_run, "load_spec", _one_survivor_recorded)
    assert mutation_run.main() != 0


def test_main_docs_only_runs_nothing_and_passes(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A docs-only diff runs zero engines, yet main() exits 0 (required → green)."""
    ran: list[str] = []
    _sandbox_main(monkeypatch, tmp_path, files=["README.md"], ran=ran)
    assert mutation_run.main() == 0
    assert not ran  # no engine ran


def _nothing() -> None:
    """Check nothing before a stand-in call."""


class _Mutmut(NamedTuple):
    """Both mutmut calls: the summary they print, and a check made before each."""

    summary: Prose
    before: Callable[[], None]

    def __call__(self, cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
        self.before()
        return subprocess.CompletedProcess(cmd, 0, stdout=self.summary, stderr="")


def _witnessed_sweep(root: Path, count: MutantCount) -> Callable[[], None]:
    """Return a stand-in step leaving what a witnessed sweep of ``count`` mutants leaves.

    That is mutmut's ``.meta`` naming each, killed, and the witness's tally of each
    run, so the lane's witness check holds and the test reads what it is about.
    """

    def swept() -> None:
        names = [f"m.f__mutmut_{index}" for index in range(1, count + 1)]
        meta = root / "python" / "mutants" / "m.py.meta"
        meta.parent.mkdir(parents=True, exist_ok=True)
        _ = meta.write_text(json.dumps({"exit_code_by_key": dict.fromkeys(names, 1)}))
        tally = root / "artifacts" / mutation_run.PYTHON_WITNESS_DIR / TALLY_FILE
        tally.parent.mkdir(parents=True, exist_ok=True)
        _ = tally.write_text("".join(f"{name}\n" for name in names))

    return swept


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

    def erased() -> None:
        # The stale tree must already be gone before mutmut is ever invoked.
        assert not stale.exists(), "run_python invoked mutmut without erasing mutants/"

    fake_run = _Mutmut(Prose(""), erased)
    # Both halves are stubbed: the long ``mutmut run`` streams (so a sweep a
    # wall clock kills still leaves its log), while the fast ``mutmut results``
    # read stays captured.  Stubbing only one would let the other reach for a
    # binary that is not there.
    monkeypatch.setattr(mutation_run, "run_streaming", fake_run)
    monkeypatch.setattr(mutation_run.subprocess, "run", fake_run)
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()

    mutation_run.run_python(artifacts)

    assert not stale.exists()


def test_run_python_names_the_repository_root_and_the_library_to_mutmut(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Both mutmut calls run with the repository's root and its built library named.

    The suite runs from mutmut's copy under python/mutants/, where a test's own
    ancestors stop one level short of the root, so the tests that read the
    tree above python/ find it through ``ALETHEIA_REPO_ROOT``, and the library
    loader through ``ALETHEIA_LIB``.
    """
    lib = tmp_path / "build" / "libaletheia-ffi.so"

    def fake_tools() -> tuple[Path, Path]:
        return (tmp_path / "mutmut", lib)

    mutmut = Mock(return_value=subprocess.CompletedProcess(["mutmut"], 0, stdout="", stderr=""))
    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "_check_python_tools", fake_tools)
    monkeypatch.setattr(mutation_run, "run_streaming", mutmut)
    monkeypatch.setattr(mutation_run.subprocess, "run", mutmut)
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()

    mutation_run.run_python(artifacts)

    assert mutmut.call_count == 2
    for call in mutmut.call_args_list:
        assert call.kwargs["env"]["ALETHEIA_REPO_ROOT"] == str(tmp_path)
        assert call.kwargs["env"]["ALETHEIA_LIB"] == str(lib)


def test_run_python_reports_the_mutants_mutmut_timed_out(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A mutant mutmut ended at its timeout reaches the report, where the drift gate refuses it.

    A timed-out mutant is neither killed nor survived, and the Python baseline
    records a ceiling of 0, so a sweep in which mutmut's cap fired fails the
    lane rather than passing on its survivor count alone.
    """

    def fake_tools() -> tuple[Path, Path]:
        return (tmp_path / "mutmut", tmp_path / "lib.so")

    fake_run = _Mutmut(
        Prose("⠴ 10/10  🎉 9 🫥 0  ⏰ 1  🤔 0  🙁 0  🔇 0  🧙 0\n"),
        _witnessed_sweep(tmp_path, MutantCount(10)),
    )
    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "_check_python_tools", fake_tools)
    monkeypatch.setattr(mutation_run, "run_streaming", fake_run)
    monkeypatch.setattr(mutation_run.subprocess, "run", fake_run)
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()

    report = mutation_run.run_python(artifacts)

    assert (report.killed, report.survived, report.observed.timeouts) == (9, 0, 1)
    verdict = mutation_run.drift_for(
        report, {"python": {"baseline": {"survivors": 0, "timeout_ceiling": 0}}}
    )
    assert verdict["status"] == "regression"


# Two mutants whose process a signal or an unknown exit ended, as ``mutmut results`` lists them.
_CRASHED = Prose(
    "⠴ 10/10  🎉 7 🫥 0  ⏰ 0  🤔 1  🙁 0  🔇 0  🧙 0\n"
    + "    aletheia.client._ffi.x_take__mutmut_6: segfault\n"
    + "    aletheia.client._ffi.x_configure__mutmut_43: suspicious\n"
)


@pytest.mark.parametrize(
    ("ceiling", "status"),
    [(MutantCount(0), "regression"), (MutantCount(2), "ok")],
    ids=["over", "at the ceiling"],
)
def test_run_python_reports_the_mutants_that_ended_their_process(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, ceiling: MutantCount, status: DriftStatus
) -> None:
    """A mutant whose process ended on a signal reaches the report, named, and the ceiling holds it.

    mutmut files a process a signal ended as ``segfault`` and one an exit it
    does not know ended as ``suspicious``, beside its kills: no test observed
    either, so a sweep past the baseline's ceiling fails the lane naming each.
    """

    def fake_tools() -> tuple[Path, Path]:
        return (tmp_path / "mutmut", tmp_path / "lib.so")

    fake_run = _Mutmut(_CRASHED, _witnessed_sweep(tmp_path, MutantCount(10)))
    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "_check_python_tools", fake_tools)
    monkeypatch.setattr(mutation_run, "run_streaming", fake_run)
    monkeypatch.setattr(mutation_run.subprocess, "run", fake_run)
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()

    report = mutation_run.run_python(artifacts)

    named = [
        CrashedMutant("aletheia.client._ffi.x_configure__mutmut_43: suspicious"),
        CrashedMutant("aletheia.client._ffi.x_take__mutmut_6: segfault"),
    ]
    assert report.observed.crashes == tuple(named)
    verdict = mutation_run.drift_for(
        report,
        {"python": {"baseline": {"survivors": 0, "timeout_ceiling": 0, "crash_ceiling": ceiling}}},
    )
    assert verdict["status"] == status
    if status == "regression":
        assert (verdict.get("observed_crashes"), verdict.get("crash_ceiling")) == (named, ceiling)


def test_run_python_runs_mutmut_through_the_witness(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The run starts mutmut through the witness, whose children inherit it; results run alone.

    A mutmut that wrote no log and a run that raised nowhere leave nothing beside
    the report and nothing witnessed in its raw record.
    """
    mutmut_bin = tmp_path / "python" / ".venv" / "bin" / "mutmut"

    def fake_tools() -> tuple[Path, Path]:
        return (mutmut_bin, tmp_path / "lib.so")

    mutmut = Mock(return_value=subprocess.CompletedProcess(["mutmut"], 0, stdout="", stderr=""))
    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "_check_python_tools", fake_tools)
    monkeypatch.setattr(mutation_run, "run_streaming", mutmut)
    monkeypatch.setattr(mutation_run.subprocess, "run", mutmut)
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()

    _ = mutation_run.run_python(artifacts)

    run_call, results_call = mutmut.call_args_list
    assert run_call.args[0] == [
        str(mutmut_bin.with_name("python3")),
        str(mutation_run.WITNESS_SCRIPT),
        "--witness-dir",
        str(artifacts / mutation_run.PYTHON_WITNESS_DIR),
        "run",
    ]
    assert results_call.args[0] == [str(mutmut_bin), "results"]
    assert mutation_run.WITNESS_SCRIPT.is_file()
    assert not (artifacts / f"python.{mutation_run.MUTMUT_LOG}").exists()
    assert "=== raised:" not in (artifacts / "python.raw.txt").read_text()


def test_run_python_keeps_each_witness_and_mutmuts_log(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Each witness lands in the raw record and on stderr, and mutmut's log beside the report.

    A ``.txt`` witness is a run that raised, a ``.running`` one a run that ended
    its process before returning; the record says which each was.
    """
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    raised = artifacts / mutation_run.PYTHON_WITNESS_DIR / "m__mutmut_9.txt"
    ended = artifacts / mutation_run.PYTHON_WITNESS_DIR / "m__mutmut_4.running"
    log = tmp_path / "python" / "mutants" / mutation_run.MUTMUT_LOG

    def ran() -> None:
        # What witnessed runs leave: two witnesses, and mutmut's log under mutants/.
        _witnessed_sweep(tmp_path, MutantCount(10))()
        raised.parent.mkdir(exist_ok=True)
        _ = raised.write_text("m__mutmut_9\nERROR: not found\n")
        _ = ended.write_text("m__mutmut_4\nstarted tests/test_a.py::test_one\n")
        log.parent.mkdir(parents=True, exist_ok=True)
        _ = log.write_text("Completed m__mutmut_9: exit=255\n")

    def fake_tools() -> tuple[Path, Path]:
        return (tmp_path / "mutmut", tmp_path / "lib.so")

    fake_run = _Mutmut(Prose("⠴ 10/10  🎉 9 🫥 0  ⏰ 1  🤔 0  🙁 0  🔇 0  🧙 0\n"), ran)
    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "_check_python_tools", fake_tools)
    monkeypatch.setattr(mutation_run, "run_streaming", fake_run)
    monkeypatch.setattr(mutation_run.subprocess, "run", fake_run)

    report = mutation_run.run_python(artifacts)

    assert report.observed.timeouts == 1
    raw = (artifacts / "python.raw.txt").read_text()
    assert "=== raised: m__mutmut_9.txt ===\nm__mutmut_9\nERROR: not found\n" in raw
    assert (
        "=== ended its process before returning: m__mutmut_4.running ===\n"
        + "m__mutmut_4\nstarted tests/test_a.py::test_one\n"
    ) in raw
    kept = artifacts / f"python.{mutation_run.MUTMUT_LOG}"
    assert kept.read_text() == "Completed m__mutmut_9: exit=255\n"
    err = capsys.readouterr().err
    assert f"[mutation] python: a mutant's run raised, witnessed in {raised}\n" in err
    assert (
        "[mutation] python: a mutant's run ended its process before returning, "
        + f"witnessed in {ended}\n"
    ) in err


# Each mutant's exit as mutmut's .meta records it: two killed or survived, one
# timed out, one with no tests (never run) and one never checked.
_EXITS = {
    "m.a__mutmut_1": 1,
    "m.b__mutmut_2": 0,
    "m.c__mutmut_3": 33,
    "m.d__mutmut_4": 255,
    "m.e__mutmut_5": None,
}


@pytest.mark.parametrize(
    ("tallied", "error"),
    [
        (["m.a__mutmut_1", "m.b__mutmut_2", "m.d__mutmut_4"], None),
        (
            ["m.a__mutmut_1"],
            "the witness tallied no run of 2 mutants mutmut ran, so it is off "
            + "(tools/mutation_witness.py), first m.b__mutmut_2, m.d__mutmut_4",
        ),
    ],
    ids=["every run tallied", "two runs missing"],
)
def test_run_python_refuses_a_sweep_whose_runs_the_witness_did_not_see(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, tallied: list[Prose], error: Prose | None
) -> None:
    """Every mutant mutmut ran a child for is in the witness's tally, or the lane fails.

    A mutant with no tests, or never checked, has no child and is not expected.
    """
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()

    def ran() -> None:
        # What the run leaves: mutmut's .meta under mutants/, the witness's tally.
        meta = tmp_path / "python" / "mutants" / "m.py.meta"
        meta.parent.mkdir(parents=True, exist_ok=True)
        _ = meta.write_text(json.dumps({"exit_code_by_key": _EXITS}))
        tally = artifacts / mutation_run.PYTHON_WITNESS_DIR / TALLY_FILE
        tally.parent.mkdir(exist_ok=True)
        _ = tally.write_text("".join(f"{name}\n" for name in tallied))

    def fake_tools() -> tuple[Path, Path]:
        return (tmp_path / "mutmut", tmp_path / "lib.so")

    fake_run = _Mutmut(Prose("⠴ 5/5  🎉 1 🫥 1  ⏰ 1  🤔 0  🙁 1  🔇 0  🧙 0\n"), ran)
    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "_check_python_tools", fake_tools)
    monkeypatch.setattr(mutation_run, "run_streaming", fake_run)
    monkeypatch.setattr(mutation_run.subprocess, "run", fake_run)

    assert mutation_run.run_python(artifacts).error == error


@pytest.mark.parametrize(
    ("named", "summary", "error"),
    [
        (
            MutantCount(4),
            Prose("⠴ 5/5  🎉 5 🫥 0  ⏰ 0  🤔 0  🙁 0  🔇 0  🧙 0\n"),
            "mutmut's .meta files name 4 of the 5 mutants its summary counts, so the witness's "
            + "tally was held to no run of the others",
        ),
        (
            MutantCount(0),
            Prose("⠴ 5/5  🎉 5 🫥 0  ⏰ 0  🤔 0  🙁 0  🔇 0  🧙 0\n"),
            "mutmut's .meta files name 0 of the 5 mutants its summary counts, so the witness's "
            + "tally was held to no run of the others",
        ),
        (
            MutantCount(5),
            Prose(""),
            "mutmut printed no count to hold its .meta files to, so no run was checked",
        ),
    ],
    ids=["fewer than counted", "none found", "no count printed"],
)
def test_run_python_refuses_a_tally_check_with_nothing_to_hold_it_to(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    named: MutantCount,
    summary: Prose,
    error: Prose,
) -> None:
    """The .meta files are held to mutmut's own count, so a reading that finds fewer fails.

    A mutmut that moved or renamed them would otherwise leave the tally held to
    no run at all, and the check would pass on nothing.
    """
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()

    def fake_tools() -> tuple[Path, Path]:
        return (tmp_path / "mutmut", tmp_path / "lib.so")

    swept = _witnessed_sweep(tmp_path, named) if named else _nothing
    fake_run = _Mutmut(summary, swept)
    monkeypatch.setattr(mutation_run, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mutation_run, "_check_python_tools", fake_tools)
    monkeypatch.setattr(mutation_run, "run_streaming", fake_run)
    monkeypatch.setattr(mutation_run.subprocess, "run", fake_run)

    assert mutation_run.run_python(artifacts).error == error
