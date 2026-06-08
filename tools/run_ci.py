# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/run_ci.py — Offline CI orchestrator.

Chains the full gate sweep that commit messages have historically asserted
"all gates clean / green" against, plus the offline enforcers
(check-changelog, check-gate-claim).  Captures all output to a timestamped log
under ``tools/ci-output/`` so the gate-claim-integrity enforcer can point at
it as falsifiable evidence (v1+ artifact-based design).

Invoked from:
  * ``tools/run_ci.py`` (direct, manual or scripted)
  * ``.git/hooks/pre-push`` (auto-installed by tools/install_hooks.py)

Deliberately NOT exposed as a Shake ``phony "ci"`` target — the runner's
inner ``cabal run shake -- build`` invocation fails to acquire
cabal-install's ``dist-newstyle/`` flock when the parent process is itself
``cabal run``.  Direct invocation avoids the flock-recursion entirely.  See
Shakefile.hs comment block where the ``ci`` phony would otherwise live.

═══ ALWAYS-ON STEPS (33 total) ═══

  Agda gates (8):
     1. build           — produces libaletheia-ffi.so
     2. check-properties     (longest, ~8-10 min)
     3. check-invariants
     4. check-no-properties-in-runtime
     5. check-erasure
     6. check-fidelity       (~2 min — runs ConstructorTest binary)
     7. check-ffi-exports
     8. count-modules
  Branch-scoped IWYU gates (2):
     9. iwyu — `tools/iwyu.py --check --diff` (or `--all` under --iwyu-all,
        the merge-gate scope) on .agda files.  The single `.agdai`-reader tool
        judges BOTH named imports (`using`/`renaming` → USED/DEAD/UNRESOLVED)
        and wildcard `open import M` (DEAD/REDUNDANT/NARROWABLE) in one warm
        process; fails on any finding.  Empty diff ⇒ no-op.  Reference:
        memory/project_agda_iwyu.md.
    10. iwyu-self-test — `tools/iwyu.py --self-test`
        validates the reader against the synthetic fixture matrix (the
        reader's correctness gate; it replaced the retired recompile oracle).
  Offline enforcers (6):
    11. check-changelog
    12. check-gate-claim
    13. check-runbook
    14. check-limits-parity      (Agda Limits SSOT vs go/aletheia/limits.go
                                  mirror)
    15. check-stability-bench    (static gate)
    16. check-mutation-setup     (static gate)
  Binding tests (6):
    17. Python pytest (deterministic lane)
    18. Python pytest --markdown-docs (Cat 32 doc-example harness)
    19. Python pytest -X dev (Cat 34a; surfaces ResourceWarning, debug
        asyncio, deprecation noise)
    20. Python pytest --random-order (Cat 14f test-isolation; AGENTS.md
        "both lanes must stay green")
    21. Go test -race
    22. C++ ctest
  Lints (7):
    23. ruff check + format --check (Python — `select=["ALL"]`, whole tree
        incl tools/: tools examples python conftest.py)
    24. basedpyright (Python — aletheia/ benchmarks/ tests/ + ../tools/)
    25. pylint 10/10 (Python — SCORE gate per AGENTS.md L611; + ../tools/)
    26. gofmt -l + go vet (Go)
    27. clang-format --dry-run --Werror (C++)
    28. clang-tidy -p build (C++ — mandatory per AGENTS.md L494)
    29. ubsan ctest (C++ — full ctest against -DALETHEIA_SANITIZER=undefined;
        always-on after UB in Rational::from_double shipped undetected
        exactly because the lane was opt-in)
  GHA meta-checks (3):
    30. actionlint (workflow YAML lint, skipped if not installed)
    31. check-action-pins
    32. check-workflow-permissions
  Source-hygiene gate (1):
    33. check-spdx-headers (SPDX license header on every source/build file)

═══ OPT-IN LANES (3 total) ═══

Each opt-in lane is gated on EITHER a command-line flag OR an environment
variable.  Precedence: CLI flag overrides env var; env var overrides default
(off).  ``--full`` enables every opt-in lane.  ``--no-<lane>`` disables a
lane that env vars would otherwise enable (useful when the pre-push hook is
running in a context where one lane is too slow).

  ──────────────────────────────────────────────────────────────────────
  Flag           Env var                       Cost  Wires which step?
  ──────────────────────────────────────────────────────────────────────
  --repro        ALETHEIA_REPRO_CHECK=1        ~10m  34: check-reproducible-build
  --stability    ALETHEIA_STABILITY_CHECK=1    ~5m   35: stability bench
  --mutation     ALETHEIA_MUTATION_CHECK=1     ~30m+ 36: mutation testing lane
  ──────────────────────────────────────────────────────────────────────
  --full         (all three above)             ~45m+ all opt-ins

Total wall-time: ~22-27 min always-on (incl. ubsan ctest ~5 min), plus
enabled opt-ins.  ``--full`` on a warm host typically lands in 45-85 min;
cold (no test cache, no Mull build-mutation tree) closer to 55-115 min.

═══ Python venv pinning ═══

The Python lanes (steps 17-22) prefer ``python/.venv/bin/python3`` over
the system ``python3`` so dev extras (``pytest-markdown-docs``,
``pytest-random-order``, ``hypothesis``, ``mutmut``) resolve.  Bootstrap
the venv once via:

  python3 -m venv python/.venv
  python/.venv/bin/pip install -e python/.[dev,mutation]

Without it the new lanes hard-fail with a precise ``ModuleNotFoundError``
rather than silently skipping.

═══ Exit codes ═══

  0 — all enabled steps passed (or skipped where allowed).
  1 — at least one step failed; tail of log printed to stderr.
  2 — usage error (e.g., not in a git repo, missing dependency, bad flag).

═══ See also ═══

  - docs/development/CI_LOCAL.md       — three-layer CI architecture
  - docs/operations/STABILITY.md       — opt-in stability lane
  - docs/operations/MUTATION.md        — opt-in mutation lane
  - memory/feedback_gate_claim_integrity.md
  - memory/feedback_orchestrator_end_to_end_validation.md
"""

from __future__ import annotations

import argparse
import datetime
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, TextIO

from tools._common import emit, find_executable, git_toplevel

if TYPE_CHECKING:
    from collections.abc import Sequence

# ``shell=True`` runs the command through ``/bin/sh -c`` on POSIX; we invoke
# that interpreter explicitly so the call site shows exactly which process is
# spawned (ruff S602/S604 warn about the opaque ``shell=True`` form).  The path
# is absolute, matching what CPython's ``shell=True`` uses verbatim.
POSIX_SHELL = "/bin/sh"

# Number of trailing log lines echoed to stderr when a step fails.
FAILURE_TAIL_LINES = 50

# Always-on step count (includes promoted UBSan lane + the two branch-scoped
# IWYU gates + the ruff lint gate + SPDX-header gate).
BASE_STEPS = 33

_INVALID_BRANCH_CHAR = re.compile(r"[^A-Za-z0-9_.-]")


def _open_log(path: Path) -> TextIO:
    """Open ``path`` for UTF-8 writing as the run's long-lived log handle.

    The handle outlives any single step — it is teed to throughout the sweep
    and closed explicitly in ``Runner.finalize`` — so a ``with`` block does not
    fit; ownership lives with the ``Runner`` instance.
    """
    return path.open("w", encoding="utf-8")


def _git_root() -> Path:
    """Return the enclosing git work-tree root, exiting 2 if outside one."""
    try:
        return git_toplevel(Path.cwd())
    except RuntimeError:
        _ = sys.stderr.write("run-ci: not inside a git repo\n")
        sys.exit(2)


def _git_value(repo_root: Path, *args: str) -> str:
    """Return the stripped stdout of ``git <args>`` run in ``repo_root``."""
    result = subprocess.run(
        [find_executable("git"), *args],
        capture_output=True,
        text=True,
        cwd=repo_root,
        check=True,
    )
    return result.stdout.strip()


@dataclass
class OptInOptions:
    """Resolved opt-in lane state.  CLI > env > default-off precedence."""

    repro: bool
    stability: bool
    mutation: bool
    # Mode flag, NOT a timing lane: switches the IWYU gate (step 9) from
    # `--diff` (branch-scoped, fast — local pre-push-hook parity) to `--all`
    # (whole-tree, airtight against cross-file deadness — the server-side
    # merge gate).  Deliberately excluded from any_enabled / enabled_count:
    # it adds no step and does not change total_steps.
    iwyu_all: bool = False

    @property
    def any_enabled(self) -> bool:
        """Report whether at least one opt-in lane is enabled."""
        return self.repro or self.stability or self.mutation

    def enabled_count(self) -> int:
        """Count how many opt-in lanes are enabled."""
        return sum([self.repro, self.stability, self.mutation])


def _resolve_flag(*, cli_value: bool | None, env_var: str) -> bool:
    """Resolve a tri-state CLI flag against an env-var fallback.

    The flag is ``--lane`` / ``--no-lane`` / unset; returns True iff the lane
    should run.
    """
    if cli_value is not None:
        return cli_value
    return os.environ.get(env_var) == "1"


def parse_args(argv: list[str] | None = None) -> OptInOptions:
    """Parse argv into resolved opt-in lane state (CLI > env > default-off)."""
    parser = argparse.ArgumentParser(
        prog="tools/run_ci.py",
        description="Offline CI orchestrator.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Opt-in lanes can be enabled via CLI flags, env vars, or `--full`.\n"
            "CLI flags override env vars; env vars override the default (off).\n"
            "\n"
            "Examples:\n"
            "  tools/run_ci.py                       # always-on steps only "
            "(incl. UBSan; ~22-27 min)\n"
            "  tools/run_ci.py --full                # everything (45-85 min)\n"
            "  tools/run_ci.py --stability --repro   # two specific opt-in lanes\n"
            "  tools/run_ci.py --full --no-mutation  # all opt-ins except mutation\n"
            "  ALETHEIA_REPRO_CHECK=1 tools/run_ci.py  # legacy env-var trigger\n"
            "\n"
            "See also docs/development/CI_LOCAL.md.\n"
        ),
    )

    def _add_lane(flag: str, env: str, help_msg: str) -> None:
        # argparse `--name / --no-name` pattern: action=BooleanOptionalAction
        # gives us both forms with paired help + None-default for "not set".
        parser.add_argument(
            f"--{flag}",
            action=argparse.BooleanOptionalAction,
            default=None,
            help=f"{help_msg} (env: {env}=1)",
        )

    _add_lane(
        "repro",
        "ALETHEIA_REPRO_CHECK",
        "reproducible-build hash gate (~10 min cold)",
    )
    _add_lane(
        "stability",
        "ALETHEIA_STABILITY_CHECK",
        "long-run stability bench (~5 min cold)",
    )
    _add_lane(
        "mutation",
        "ALETHEIA_MUTATION_CHECK",
        "mutation testing across 3 bindings (~30 min+)",
    )

    parser.add_argument(
        "--full",
        action="store_true",
        help=(
            "Enable every opt-in lane (equivalent to --repro --stability "
            "--mutation).  Individual --no-<lane> flags can still subtract from "
            "the --full set (e.g. --full --no-mutation runs everything except "
            "mutation testing)."
        ),
    )

    parser.add_argument(
        "--iwyu-all",
        action="store_true",
        default=False,
        help=(
            "Run the IWYU import gate (step 9) over the WHOLE tree (`--all`) "
            "instead of the branch diff (`--diff`).  Airtight against "
            "cross-file deadness; this is what the server-side PR merge gate "
            "uses.  (env: ALETHEIA_IWYU_ALL=1)"
        ),
    )

    args = parser.parse_args(argv)

    # --full sets every unset CLI flag to True; explicit --no-<lane> keeps False.
    # The order matters: apply --full BEFORE _resolve_flag so the env var still
    # gets to enable a lane that --full + --no-<other> didn't touch.
    if args.full:
        for lane in ("repro", "stability", "mutation"):
            if getattr(args, lane) is None:
                setattr(args, lane, True)

    return OptInOptions(
        repro=_resolve_flag(cli_value=args.repro, env_var="ALETHEIA_REPRO_CHECK"),
        stability=_resolve_flag(cli_value=args.stability, env_var="ALETHEIA_STABILITY_CHECK"),
        mutation=_resolve_flag(cli_value=args.mutation, env_var="ALETHEIA_MUTATION_CHECK"),
        iwyu_all=args.iwyu_all or os.environ.get("ALETHEIA_IWYU_ALL") == "1",
    )


def _now_utc() -> datetime.datetime:
    """Return the current timezone-aware UTC moment."""
    return datetime.datetime.now(datetime.UTC)


@dataclass(frozen=True)
class RunContext:
    """Immutable per-run metadata: git identity, log artifact, python interpreter."""

    repo_root: Path
    branch: str
    commit: str
    log_path: Path
    python: str

    @classmethod
    def discover(cls, repo_root: Path) -> RunContext:
        """Gather git identity, the timestamped log path, and the python interpreter."""
        log_dir = repo_root / "tools" / "ci-output"
        log_dir.mkdir(parents=True, exist_ok=True)

        branch = _git_value(repo_root, "rev-parse", "--abbrev-ref", "HEAD")
        commit = _git_value(repo_root, "rev-parse", "HEAD")
        branch_safe = _INVALID_BRANCH_CHAR.sub("_", branch)
        timestamp = _now_utc().strftime("%Y-%m-%dT%H-%M-%SZ")

        # Prefer the project's venv if present so dev-extras (markdown-docs,
        # random-order, hypothesis, mutmut) resolve.  Falls back to python3.14
        # (the project requires Python 3.14 -- PEP 758 syntax in tools/ and
        # requires-python>=3.14 -- so bare python3, often 3.12/3.13, would
        # SyntaxError on the 3.14-only tools).
        venv_python = repo_root / "python" / ".venv" / "bin" / "python3"
        python = str(venv_python) if venv_python.exists() else "python3.14"

        return cls(
            repo_root=repo_root,
            branch=branch,
            commit=commit,
            log_path=log_dir / f"ci-{branch_safe}-{timestamp}.log",
            python=python,
        )


@dataclass
class Runner:
    """Drive the ordered step sweep, tee output to a log, and tally pass/fail."""

    opts: OptInOptions
    ctx: RunContext
    total_steps: int = field(init=False)
    step_num: int = field(init=False, default=0)
    failed_step: str | None = field(init=False, default=None)
    start: float = field(init=False, default=0.0)
    log_fh: TextIO = field(init=False)

    def __post_init__(self) -> None:
        """Open the log file handle and initialise counters."""
        self.total_steps = BASE_STEPS + self.opts.enabled_count()
        self.start = time.time()
        self.log_fh = _open_log(self.ctx.log_path)

    @property
    def repo_root(self) -> Path:
        """Return the repository root for this run (proxy onto the context)."""
        return self.ctx.repo_root

    @property
    def python(self) -> str:
        """Return the python interpreter for the binding lanes (context proxy)."""
        return self.ctx.python

    def header(self) -> None:
        """Tee the run banner (branch, commit, step plan, opt-in summary)."""
        opt_in_summary: list[str] = []
        for name, enabled in (
            ("repro", self.opts.repro),
            ("stability", self.opts.stability),
            ("mutation", self.opts.mutation),
        ):
            if enabled:
                opt_in_summary.append(f"+{name}")
            else:
                opt_in_summary.append(f"-{name}")
        lines = [
            "═══ Aletheia offline CI sweep ═══",
            f"Started:  {_now_utc():%Y-%m-%d %H:%M:%S UTC}",
            f"Branch:   {self.ctx.branch}",
            f"Commit:   {self.ctx.commit}",
            f"Steps:    {self.total_steps} ({BASE_STEPS} always-on + "
            + f"{self.opts.enabled_count()} opt-in)",
            f"Opt-ins:  {' '.join(opt_in_summary)}",
            f"Log:      {self.ctx.log_path}",
            "",
        ]
        self._tee("\n".join(lines))

    def _tee(self, text: str) -> None:
        emit(text)
        _ = self.log_fh.write(text + "\n")
        self.log_fh.flush()

    def _tee_err(self, text: str) -> None:
        _ = sys.stderr.write(text + "\n")
        sys.stderr.flush()
        _ = self.log_fh.write(text + "\n")
        self.log_fh.flush()

    def _step_header(self, name: str, cmd: Sequence[str] | str) -> None:
        cmd_str = cmd if isinstance(cmd, str) else " ".join(cmd)
        lines = [
            "",
            f"─── Step {self.step_num}/{self.total_steps}: {name} ───",
            f"Cmd:    {cmd_str}",
            f"Start:  {_now_utc():%Y-%m-%d %H:%M:%S UTC}",
        ]
        self._tee("\n".join(lines))

    def _print_tail_on_failure(self, name: str, exit_code: int, duration: int) -> None:
        self._tee_err(f"  ✗ {name} FAILED (exit {exit_code}, {duration}s)")
        self._tee_err("")
        self._tee_err("─── Tail of failed step output ───")
        self.log_fh.flush()
        log_text = self.ctx.log_path.read_text(encoding="utf-8", errors="replace")
        for line in log_text.splitlines()[-FAILURE_TAIL_LINES:]:
            _ = sys.stderr.write(line + "\n")
        sys.stderr.flush()
        self._tee_err("")
        self._tee_err(
            f"═══ CI FAILED at step {self.step_num}/{self.total_steps}: {name} ═══",
        )
        self._tee_err(f"Full log: {self.ctx.log_path}")

    def step(
        self,
        name: str,
        cmd: Sequence[str] | str,
        *,
        cwd: Path | None = None,
    ) -> None:
        """Run one named step, teeing its header and recording the first failure.

        ``cmd`` is either an argv list run directly, or a string forwarded to
        ``/bin/sh -c`` for the lanes that need pipes, redirection, or globs.
        Once a step fails, subsequent calls are no-ops.
        """
        if self.failed_step is not None:
            return
        self.step_num += 1
        self._step_header(name, cmd)
        step_start = time.time()
        argv = [POSIX_SHELL, "-c", cmd] if isinstance(cmd, str) else list(cmd)
        proc = subprocess.run(
            argv,
            stdout=self.log_fh,
            stderr=subprocess.STDOUT,
            cwd=cwd,
            check=False,
        )
        duration = int(time.time() - step_start)
        if proc.returncode != 0:
            self.failed_step = name
            self._print_tail_on_failure(name, proc.returncode, duration)
            return
        _ = sys.stderr.write(f"  ✓ {name} ({duration}s)\n")
        _ = self.log_fh.write(f"  ✓ {name} ({duration}s)\n")
        self.log_fh.flush()

    def announce_skip(self, name: str, reason: str) -> None:
        """Log a skipped lane without bumping the step counter."""
        # Skipped steps don't bump the step counter — they're not part of
        # total_steps in the first place (only enabled lanes are counted).
        # We still log the skip line so the log is complete.
        msg = f"  ⊘ {name} skipped ({reason})"
        _ = sys.stderr.write(msg + "\n")
        _ = self.log_fh.write(msg + "\n")
        self.log_fh.flush()

    def finalize(self) -> int:
        """Tee the summary, close the log, and return the process exit code."""
        total = int(time.time() - self.start)
        if self.failed_step is None:
            lines = [
                "",
                "═══ CI summary ═══",
                f"Result:   ALL {self.total_steps} STEPS PASSED",
                f"Duration: {total}s ({total // 60}m{total % 60:02d}s)",
                f"Log:      {self.ctx.log_path}",
                "Use this log file as the falsifiable evidence behind any 'all "
                + "gates' claim in commit messages "
                + "(see memory/feedback_gate_claim_integrity.md).",
            ]
            self._tee("\n".join(lines))
            self.log_fh.close()
            return 0
        self.log_fh.close()
        return 1


def _run_agda_gates(runner: Runner, cabal: list[str]) -> None:
    """Run steps 1-10: the Agda gate sweep plus the two branch-scoped IWYU gates."""
    # ─── Steps 1-8: Agda gates ─────────────────────────────────────────────
    runner.step("build", [*cabal, "build"])
    runner.step("check-properties", [*cabal, "check-properties"])
    runner.step("check-invariants", [*cabal, "check-invariants"])
    runner.step("check-no-properties-in-runtime", [*cabal, "check-no-properties-in-runtime"])
    runner.step("check-erasure", [*cabal, "check-erasure"])
    runner.step("check-fidelity", [*cabal, "check-fidelity"])
    runner.step("check-ffi-exports", [*cabal, "check-ffi-exports"])
    runner.step("count-modules", [*cabal, "count-modules"])

    # ─── Steps 9-10: the IWYU gate (one tool) ───────────────────────────────
    # Step 9 (`iwyu --check`) judges BOTH named imports (DEAD/UNRESOLVED) and
    # wildcard `open import M` (DEAD/REDUNDANT/NARROWABLE) via the scope-aware
    # `.agdai` reader in one warm process — no recompile-confirm.  Scope is
    # branch-diff by default (`--diff`: git diff main...HEAD -- src/; empty diff
    # ⇒ no-op — local pre-push-hook parity), or the whole tree (`--all`) under
    # `--iwyu-all` / ALETHEIA_IWYU_ALL=1 — airtight against cross-file deadness,
    # which is what the server-side PR merge gate runs.  Step 10
    # (`iwyu --self-test`) validates that reader against the synthetic fixture
    # matrix (its correctness gate).  Reference: memory/project_agda_iwyu.md.
    iwyu_scope = "--all" if runner.opts.iwyu_all else "--diff"
    runner.step(
        "iwyu",
        [runner.python, "-m", "tools.iwyu", "--check", iwyu_scope],
        cwd=runner.repo_root,
    )
    runner.step(
        "iwyu-self-test",
        [runner.python, "-m", "tools.iwyu", "--self-test"],
        cwd=runner.repo_root,
    )


def _run_offline_enforcers(runner: Runner, cabal: list[str]) -> None:
    """Run steps 10-15: the offline enforcer Shake targets."""
    # ─── Steps 10-14: Offline enforcers ────────────────────────────────────
    runner.step("check-changelog", [*cabal, "check-changelog"])
    runner.step("check-gate-claim", [*cabal, "check-gate-claim"])
    runner.step("check-runbook", [*cabal, "check-runbook"])
    runner.step("check-limits-parity", [*cabal, "check-limits-parity"])
    runner.step("check-stability-bench", [*cabal, "check-stability-bench"])
    runner.step("check-mutation-setup", [*cabal, "check-mutation-setup"])


def _run_binding_tests(runner: Runner) -> None:
    """Run steps 16-21: the Python / Go / C++ binding test lanes."""
    # ─── Steps 14-19: Binding tests ────────────────────────────────────────
    # Step 14: deterministic pytest lane.
    runner.step(
        "pytest",
        [runner.python, "-m", "pytest", "tests/"],
        cwd=runner.repo_root / "python",
    )
    # Step 15: doc-example fence harness.
    runner.step(
        "pytest --markdown-docs",
        [
            runner.python,
            "-m",
            "pytest",
            "--markdown-docs",
            "--rootdir",
            str(runner.repo_root),
            "README.md",
            "docs/",
            "python/README.md",
            "examples/README.md",
        ],
        cwd=runner.repo_root,
    )
    # Step 16: Python -X dev mode (Cat 34a).
    runner.step(
        "pytest -X dev",
        [runner.python, "-X", "dev", "-m", "pytest", "tests/"],
        cwd=runner.repo_root / "python",
    )
    # Step 17: random-order test isolation (Cat 14f).
    runner.step(
        "pytest --random-order",
        [
            runner.python,
            "-m",
            "pytest",
            "--random-order",
            "--random-order-bucket=package",
            "tests/",
        ],
        cwd=runner.repo_root / "python",
    )
    runner.step(
        "go test -race",
        ["go", "test", "./aletheia/", "-count=1", "-race"],
        cwd=runner.repo_root / "go",
    )
    runner.step(
        "ctest",
        "cmake -B build > /dev/null && cmake --build build && ctest --test-dir build",
        cwd=runner.repo_root / "cpp",
    )


def _run_lints(runner: Runner) -> None:
    """Run steps 23-29: the Python / Go / C++ lint gates plus the UBSan ctest lane."""
    # ─── Steps 23-29: Lints ────────────────────────────────────────────────
    # ruff (`select=["ALL"]`, config in ruff.toml) over the WHOLE Python tree
    # INCLUDING tools/ (repo-root gate scripts) — both `check` and
    # `format --check`.  `python/mutants` (mutmut output) is excluded in
    # ruff.toml.  Run from the repo root so the root ruff.toml is the config.
    ruff_cmd = (
        f"{shlex.quote(runner.python)} -m ruff check tools examples python conftest.py "
        f"&& {shlex.quote(runner.python)} -m ruff format --check tools examples python conftest.py"
    )
    runner.step("ruff", ruff_cmd, cwd=runner.repo_root)

    # ``benchmarks/`` joined the basedpyright gate 2026-05-09, ``tests/`` on
    # 2026-05-31, and ``../tools/`` on 2026-06-06 (pyproject has a strict
    # executionEnvironment for ../tools); pylint covers the same set, so the
    # two stay symmetric (feedback_no_subsumption_asymmetry.md).
    #
    # Invoke via ``runner.python -m basedpyright`` (not the bare ``basedpyright``
    # console script) for the same reason as ruff/pylint: CI launches this sweep
    # as ``python/.venv/bin/python3 -m tools.run_ci``, which does NOT activate
    # the venv, so the venv's ``bin/`` is not on PATH and a bare ``basedpyright``
    # raises FileNotFoundError. ``-m`` runs the venv-installed package directly.
    runner.step(
        "basedpyright",
        [runner.python, "-m", "basedpyright", "aletheia/", "benchmarks/", "tests/", "../tools/"],
        cwd=runner.repo_root / "python",
    )

    # pylint SCORE-based gate per AGENTS.md L611 + feedback_pylint_10_mandatory.md.
    # Covers aletheia/ tests/ benchmarks/ + ../tools/ (the repo-root gate scripts,
    # held to the same 10.00 bar per feedback_tools_lint_standard.md); ``..`` is on
    # the path via python/pyproject's pylint init-hook so tools' imports resolve.
    pylint_cmd = (
        f"{shlex.quote(runner.python)} -m pylint aletheia/ tests/ benchmarks/ ../tools/ "
        "> /tmp/aletheia-pylint.out 2>&1; "
        "rc=$?; cat /tmp/aletheia-pylint.out; "
        "grep -q 'rated at 10\\.00/10' /tmp/aletheia-pylint.out"
    )
    runner.step("pylint", pylint_cmd, cwd=runner.repo_root / "python")

    # gofmt -l (LIST mode): stdout non-empty == files need reformatting.
    gofmt_cmd = (
        "gofmt -l ./aletheia/ > /tmp/aletheia-gofmt.out 2>&1; rc=$?; "
        "cat /tmp/aletheia-gofmt.out; "
        "test $rc -eq 0 && test ! -s /tmp/aletheia-gofmt.out && go vet ./aletheia/"
    )
    runner.step("gofmt + go vet", gofmt_cmd, cwd=runner.repo_root / "go")

    # clang-format: exclude generated / third-party trees + sanitizer/mutation
    # build trees.
    #
    # Route through the venv-pinned clang-format (the ``clang-format`` pip pkg in
    # [dev]) instead of a bare PATH lookup.  clang-format output is
    # version-specific (trailing-return signatures wrap differently across
    # 18/19), and the system clang-format on a CI runner is whatever
    # update-alternatives selected — often NOT the version apt installs — so an
    # unpinned binary makes the gate non-reproducible.  The venv binary is
    # byte-identical on every contributor + CI; fall back to a PATH lookup only
    # if the venv lacks it (e.g. a non-[dev] environment).
    _clang_format = Path(runner.python).parent / "clang-format"
    clang_format_bin = str(_clang_format) if _clang_format.exists() else "clang-format"
    clang_format_cmd = (
        "find . \\( -path ./build -o -path ./build-tidy "
        "-o -path ./build-asan -o -path ./build-ubsan "
        "-o -path ./build-mutation "
        "-o -path ./_deps -o -path './*/_deps' \\) -prune -o "
        "\\( -name '*.cpp' -o -name '*.hpp' \\) -print | "
        f"xargs {shlex.quote(clang_format_bin)} --dry-run --Werror"
    )
    runner.step("clang-format", clang_format_cmd, cwd=runner.repo_root / "cpp")

    # clang-tidy: AGENTS.md L580 canonical scope (src/*.cpp).
    runner.step(
        "clang-tidy",
        "clang-tidy -p build src/*.cpp",
        cwd=runner.repo_root / "cpp",
    )


def _run_gha_checks(runner: Runner) -> None:
    """Run steps 28-30: the GitHub-Actions workflow meta-checks."""
    # ─── Steps 25-27: GHA meta-checks ──────────────────────────────────────
    if shutil.which("actionlint"):
        if (runner.repo_root / ".github" / "workflows").is_dir():
            runner.step("actionlint", ["actionlint", "-color"])
        else:
            runner.announce_skip("actionlint", "no .github/workflows/ directory")
    else:
        runner.announce_skip(
            "actionlint",
            "binary not installed; see docs/development/CI_LOCAL.md",
        )

    runner.step(
        "check-action-pins",
        [runner.python, "-m", "tools.check_action_pins"],
        cwd=runner.repo_root,
    )
    runner.step(
        "check-workflow-permissions",
        [runner.python, "-m", "tools.check_workflow_permissions"],
        cwd=runner.repo_root,
    )
    runner.step(
        "check-spdx-headers",
        [runner.python, "-m", "tools.check_spdx_headers"],
        cwd=runner.repo_root,
    )


def _run_opt_in_lanes(runner: Runner, opts: OptInOptions) -> None:
    """Run the always-on UBSan lane then the enabled repro / stability / mutation lanes."""
    # ─── Opt-in lanes (numbered 34+ when enabled) ──────────────────────────
    # Each lane is appended to total_steps in __init__ via opts.enabled_count();
    # they share the same step counter as always-on steps so the "ALL N STEPS
    # PASSED" line in finalize() matches the actual count.

    # Step 29 (always-on): UBSan lane (Cat 33a; promoted from opt-in to
    # always-on after UB in Rational::from_double had previously shipped
    # undetected exactly because the lane was opt-in).  Builds the full
    # ctest battery against -DALETHEIA_SANITIZER=undefined and asserts
    # every test passes.  Vendored zippy.hpp UB filtered via
    # cpp/sanitizer-ignorelist.txt; clang required (g++ has no equivalent).
    runner.step(
        "ubsan ctest",
        "cmake -B build-ubsan -DALETHEIA_SANITIZER=undefined "
        + "-DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ > /dev/null"
        + " && cmake --build build-ubsan && ctest --test-dir build-ubsan",
        cwd=runner.repo_root / "cpp",
    )

    # Step 34 (opt-in): reproducible-build gate ────────────────────────────
    if opts.repro:
        runner.step(
            "check-reproducible-build",
            [runner.python, "-m", "tools.check_reproducible_build"],
            cwd=runner.repo_root,
        )
    else:
        runner.announce_skip(
            "check-reproducible-build",
            "set ALETHEIA_REPRO_CHECK=1 or pass --repro to enable",
        )

    # Step 35 (opt-in): long-run stability bench ───────────────────────────
    # Agda cat 16 + Python cat 25 + C++ cat 26 + Go cat 27.
    if opts.stability:
        runner.step(
            "stability bench",
            [runner.python, "-m", "tools.stability_run"],
            cwd=runner.repo_root,
        )
    else:
        runner.announce_skip(
            "stability bench",
            "set ALETHEIA_STABILITY_CHECK=1 or pass --stability to enable",
        )

    # Step 36 (opt-in): mutation testing across all 3 bindings ─────────────
    # Cat 14g.  AGENTS.md: "Mutation testing runs as a separate CI lane
    # (cost is high) — once per PR is sufficient; per-commit is overkill."
    # Default OFF.  See docs/operations/MUTATION.md.
    if opts.mutation:
        runner.step(
            "mutation testing",
            [runner.python, "-m", "tools.mutation_run"],
            cwd=runner.repo_root,
        )
    else:
        runner.announce_skip(
            "mutation testing",
            "set ALETHEIA_MUTATION_CHECK=1 or pass --mutation to enable",
        )


def main(argv: list[str] | None = None) -> int:
    """Run the full offline CI sweep, returning the process exit code."""
    opts = parse_args(argv)
    repo_root = _git_root()
    os.chdir(repo_root)
    runner = Runner(opts, RunContext.discover(repo_root))
    runner.header()

    cabal = ["cabal", "run", "shake", "--"]

    _run_agda_gates(runner, cabal)
    _run_offline_enforcers(runner, cabal)
    _run_binding_tests(runner)
    _run_lints(runner)
    _run_gha_checks(runner)
    _run_opt_in_lanes(runner, opts)

    return runner.finalize()


if __name__ == "__main__":
    sys.exit(main())
