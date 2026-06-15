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

═══ ALWAYS-ON STEPS ═══

Steps register into per-toolchain lanes; ``build`` runs first (every lane needs
its ``.so`` / ``.agdai``), then the lanes run serially (default) or concurrently
(``--parallel`` — see ``tools/_scheduler.py``).  The always-on steps, by lane:

  Agda gates:
    - build           — produces libaletheia-ffi.so (separate prereq; a build
      failure short-circuits the whole sweep before the lanes spawn)
    - agda gates      — every remaining cabal-shake gate folded into ONE
      `cabal run shake -- <targets>` call (AGDA_SHAKE_TARGETS).  Shake runs the
      independent phony rules concurrently (shakeThreads=0) — the two heavy proof
      checks overlap at ~2.3 GiB peak — and pays the per-process cabal/shake
      startup + build-graph re-validation once instead of once per gate.  Covers:
      check-properties, check-invariants, check-no-properties-in-runtime,
      check-erasure, check-fidelity, check-ffi-exports, count-modules,
      check-changelog, check-gate-claim, check-runbook, check-limits-parity,
      check-stability-bench, check-mutation-setup.  Shake fails fast on the first
      failing target and names it on stderr (surfaced in the failure tail).
  Branch-scoped IWYU gates (separate — they read the .agdai the gates write):
    - iwyu — `tools/iwyu.py --check --diff` (or `--all` under --iwyu-all, the
      merge-gate scope) on .agda files.  The single `.agdai`-reader tool judges
      BOTH named imports (`using`/`renaming` → USED/DEAD/UNRESOLVED) and wildcard
      `open import M` (DEAD/REDUNDANT/NARROWABLE) in one warm process; fails on
      any finding.  Empty diff ⇒ no-op.  Reference: memory/project_agda_iwyu.md.
    - iwyu-self-test — `tools/iwyu.py --self-test` validates the reader against
      the synthetic fixture matrix (it replaced the retired recompile oracle).
  Binding tests:
    - Python pytest (deterministic lane)
    - Python pytest --markdown-docs (Cat 32 doc-example harness)
    - Python pytest -X dev (Cat 34a; surfaces ResourceWarning, debug asyncio,
      deprecation noise)
    - Python pytest --random-order (Cat 14f test-isolation; AGENTS.md "both
      lanes must stay green")
    - Go test -race
    - C++ ctest
    - Rust cargo test (tracer-bullet FFI lifecycle; ALETHEIA_LIB → built .so)
  Lints:
    - ruff check + format --check (Python — `select=["ALL"]`, whole tree incl
      tools/: tools examples python conftest.py)
    - basedpyright (Python — aletheia/ benchmarks/ tests/ + ../tools/)
    - pylint 10/10 (Python — SCORE gate per AGENTS.md L611; + ../tools/)
    - gofmt -l + go vet (Go)
    - clang-format --dry-run --Werror (C++)
    - clang-tidy -p build (C++ — mandatory per AGENTS.md L494)
    - Rust cargo fmt --check + clippy -D warnings
  GHA meta-checks:
    - actionlint (workflow YAML lint, skipped if not installed)
    - check-action-pins
    - check-workflow-permissions
  Source-hygiene gate:
    - check-spdx-headers (SPDX license header on every source/build file)
    - check-venv-convention (exactly one venv, at python/.venv)
  C++ sanitizer lane (runs last):
    - ubsan ctest (full ctest against -DALETHEIA_SANITIZER=undefined; always-on
      after UB in Rational::from_double shipped undetected as an opt-in lane)

═══ OPT-IN LANES (3 total) ═══

Each opt-in lane is gated on EITHER a command-line flag OR an environment
variable.  Precedence: CLI flag overrides env var; env var overrides default
(off).  ``--full`` enables every opt-in lane.  ``--no-<lane>`` disables a
lane that env vars would otherwise enable (useful when the pre-push hook is
running in a context where one lane is too slow).

  ──────────────────────────────────────────────────────────────────────
  Flag           Env var                       Cost  Wires which lane
  ──────────────────────────────────────────────────────────────────────
  --repro        ALETHEIA_REPRO_CHECK=1        ~10m  check-reproducible-build
  --stability    ALETHEIA_STABILITY_CHECK=1    ~5m   stability bench
  --mutation     ALETHEIA_MUTATION_CHECK=1     ~30m+ mutation testing lane
  ──────────────────────────────────────────────────────────────────────
  --full         (all three above)             ~45m+ all opt-ins

Total wall-time: ~22-27 min always-on (incl. ubsan ctest ~5 min), plus
enabled opt-ins.  ``--full`` on a warm host typically lands in 45-85 min;
cold (no test cache, no Mull build-mutation tree) closer to 55-115 min.

═══ Python venv pinning ═══

The Python lanes prefer ``python/.venv/bin/python3`` over
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
from tools._resources import cpu_budget
from tools._scheduler import Step, StepResult, run_lanes

if TYPE_CHECKING:
    from collections.abc import Sequence

# Number of trailing log lines echoed to stderr when a step fails.
FAILURE_TAIL_LINES = 50

# The combined Agda-gate step: every cabal-shake gate folded into ONE
# `cabal run shake -- <targets>` invocation.  Shake (shakeThreads=0, all-core)
# overlaps the two heavy proof checks — measured concurrent peak ~2.3 GiB, ~14%
# of a 16 GB GHA runner, so memory does not bind and no Shake-internal gate is
# needed — and the single process pays cabal/shake startup + build-graph
# re-validation ONCE instead of once per gate (the dominant GHA cost).  `build`
# stays a separate prereq (preserves the build-fail short-circuit); `iwyu` stays
# separate (it reads the .agdai that check-properties writes).  Pinned as a
# tuple so the regression test can assert no gate is silently dropped on edit.
AGDA_GATES_STEP = "agda gates"
AGDA_SHAKE_TARGETS: tuple[str, ...] = (
    "check-properties",
    "check-invariants",
    "check-no-properties-in-runtime",
    "check-erasure",
    "check-fidelity",
    "check-ffi-exports",
    "count-modules",
    "check-changelog",
    "check-gate-claim",
    "check-runbook",
    "check-limits-parity",
    "check-stability-bench",
    "check-mutation-setup",
)

# Big-memory steps gated by the OOM semaphore in --parallel mode.  Centralizing
# the classification (vs. a heavy= flag on every step() call) keeps it reviewable
# in one place.  Chosen from real GHA timings: the combined Agda gates (folds the
# -M16G warm proc + the cabal-test fidelity build), the C++ clang builds, the
# race detector, the FFI pytest lane, and the opt-in lanes.  See .session-state
# Stage B notes.
HEAVY_STEPS: frozenset[str] = frozenset(
    {
        "build",
        AGDA_GATES_STEP,
        "pytest",
        "go test -race",
        "ctest",
        "ubsan ctest",
        "check-reproducible-build",
        "stability bench",
        "mutation testing",
    }
)

# Toolchain lane inferred from a step's cwd directory name.  Binding/lint steps
# run under python/ go/ cpp/ rust/, so their cwd unambiguously names their lane
# (steps sharing a toolchain dir — pytest+lints, ctest+clang-tidy, cargo
# test+clippy — must run serially within one lane).  Shake steps (cwd=None,
# shared build-dir lock) are tagged explicitly "agda"; light meta/opt-in steps
# fall to "misc".  "misc" never holds a `cabal run shake` step, so two Shake
# invocations can never land in different lanes and deadlock on the build lock.
_LANE_BY_DIR: dict[str, str] = {"python": "python", "go": "go", "cpp": "cpp", "rust": "rust"}

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
    # Lane-parallel gate execution + the heavy-step concurrency cap.  Default
    # serial (run_lanes serial=True): exit-code-identical to today.  --parallel
    # opts into the lane scheduler; heavy_limit bounds concurrent big-memory
    # steps (the OOM guard) and is only consulted in parallel mode.
    parallel: bool = False
    heavy_limit: int = 2

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


def _resolve_heavy_limit(cli_value: int | None) -> int:
    """Resolve the OOM heavy-step limit: CLI > env > default, clamped to >= 1.

    A non-integer ``ALETHEIA_CI_HEAVY_LIMIT`` falls back to the default rather
    than crashing the sweep, and a non-positive value is clamped to 1 so the
    startup banner and the scheduler's ``Semaphore(max(1, n))`` agree on the
    effective limit (no misleading "heavy-limit 0").
    """
    default = 2
    if cli_value is not None:
        return max(1, cli_value)
    try:
        return max(1, int(os.environ.get("ALETHEIA_CI_HEAVY_LIMIT", str(default))))
    except ValueError:
        return default


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

    parser.add_argument(
        "--parallel",
        action=argparse.BooleanOptionalAction,
        default=None,
        help=(
            "Run independent toolchain lanes concurrently (Agda / Python / Go / "
            "C++ / Rust / meta) rather than serially.  Default off — serial is "
            "exit-code-identical to the historic sweep.  (env: ALETHEIA_CI_PARALLEL=1)"
        ),
    )
    parser.add_argument(
        "--ci-heavy-limit",
        type=int,
        default=None,
        help=(
            "Max big-memory steps run at once in --parallel mode (the OOM guard); "
            "default 2.  (env: ALETHEIA_CI_HEAVY_LIMIT)"
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
        parallel=_resolve_flag(cli_value=args.parallel, env_var="ALETHEIA_CI_PARALLEL"),
        heavy_limit=_resolve_heavy_limit(args.ci_heavy_limit),
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
    """Collect gate steps into toolchain lanes, then run them serial or lane-parallel."""

    opts: OptInOptions
    ctx: RunContext
    start: float = field(init=False, default=0.0)
    log_fh: TextIO = field(init=False)
    _registry: list[Step] = field(init=False, default_factory=list)
    _skips: list[tuple[str, str]] = field(init=False, default_factory=list)

    def __post_init__(self) -> None:
        """Open the log file handle and start the clock."""
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

    def _header(self, total: int) -> None:
        """Tee the run banner (branch, commit, step count, mode, opt-ins)."""
        opt_in = " ".join(
            f"+{name}" if enabled else f"-{name}"
            for name, enabled in (
                ("repro", self.opts.repro),
                ("stability", self.opts.stability),
                ("mutation", self.opts.mutation),
            )
        )
        mode = (
            f"parallel (heavy-limit {self.opts.heavy_limit}, {cpu_budget()} workers)"
            if self.opts.parallel
            else "serial"
        )
        self._tee(
            "\n".join(
                [
                    "═══ Aletheia offline CI sweep ═══",
                    f"Started:  {_now_utc():%Y-%m-%d %H:%M:%S UTC}",
                    f"Branch:   {self.ctx.branch}",
                    f"Commit:   {self.ctx.commit}",
                    f"Steps:    {total}",
                    f"Mode:     {mode}",
                    f"Opt-ins:  {opt_in}",
                    f"Log:      {self.ctx.log_path}",
                    "",
                ]
            ),
        )

    def _tee(self, text: str) -> None:
        emit(text)
        _ = self.log_fh.write(text + "\n")
        self.log_fh.flush()

    def _tee_err(self, text: str) -> None:
        _ = sys.stderr.write(text + "\n")
        sys.stderr.flush()
        _ = self.log_fh.write(text + "\n")
        self.log_fh.flush()

    def step(
        self,
        name: str,
        cmd: Sequence[str] | str,
        *,
        cwd: Path | None = None,
        lane: str = "misc",
    ) -> None:
        """Register a step in its toolchain lane (executed later by :meth:`run`).

        ``cmd`` is an argv list (run directly) or a string (via ``/bin/sh -c``
        for lanes that need pipes / globs / redirection).  ``lane`` groups steps
        that share mutable toolchain state — serial within a lane, concurrent
        across lanes.  Left default, ``lane`` is inferred from the cwd toolchain
        dir (``_LANE_BY_DIR``); pass it explicitly for Shake steps (cwd=None).
        "heavy" (OOM-gated in parallel mode) is derived from ``HEAVY_STEPS``.
        """
        if lane == "misc" and cwd is not None:
            lane = _LANE_BY_DIR.get(cwd.name, "misc")
        self._registry.append(
            Step(name=name, cmd=cmd, cwd=cwd, heavy=name in HEAVY_STEPS, lane=lane),
        )

    def announce_skip(self, name: str, reason: str) -> None:
        """Record a skipped lane for the banner / log."""
        self._skips.append((name, reason))

    @staticmethod
    def _group_lanes(steps: list[Step]) -> list[list[Step]]:
        """Bucket steps by lane, preserving first-seen lane order and step order."""
        lanes: dict[str, list[Step]] = {}
        for entry in steps:
            lanes.setdefault(entry.lane, []).append(entry)
        return list(lanes.values())

    def _emit(self, result: StepResult) -> None:
        """Tee one step's captured output and its ✓/✗ summary line."""
        self._tee(f"\n─── {result.name} ({int(result.duration)}s) ───")
        _ = self.log_fh.write(result.output)
        if not result.output.endswith("\n"):
            _ = self.log_fh.write("\n")
        self.log_fh.flush()
        if result.returncode == 0:
            self._tee_err(f"  ✓ {result.name} ({int(result.duration)}s)")
            return
        self._tee_err(
            f"  ✗ {result.name} FAILED (exit {result.returncode}, {int(result.duration)}s)",
        )
        self._tee_err("─── tail of failed step output ───")
        for line in result.output.splitlines()[-FAILURE_TAIL_LINES:]:
            _ = sys.stderr.write(line + "\n")
        sys.stderr.flush()

    def run(self) -> int:
        """Execute build first, then the lanes (serial or parallel); return exit code."""
        total = len(self._registry)
        self._header(total)
        for name, reason in self._skips:
            self._tee_err(f"  ⊘ {name} skipped ({reason})")

        results: list[StepResult] = []
        # `build` produces the .so / .agdai every other lane needs, so it runs
        # first and alone; a build failure short-circuits the whole sweep.
        build = next((s for s in self._registry if s.name == "build"), None)
        rest = [s for s in self._registry if s.name != "build"]
        if build is not None:
            (built,) = run_lanes([[build]], max_workers=1, heavy_limit=1, serial=True)
            self._emit(built)
            results.append(built)
            if built.returncode != 0:
                return self._finalize(results, total)

        lane_results = run_lanes(
            self._group_lanes(rest),
            max_workers=cpu_budget(),
            heavy_limit=self.opts.heavy_limit,
            serial=not self.opts.parallel,
        )
        for result in lane_results:
            self._emit(result)
        results.extend(lane_results)
        return self._finalize(results, total)

    def _finalize(self, results: list[StepResult], total: int) -> int:
        """Tee the summary, close the log, return 0 iff every step passed."""
        elapsed = int(time.time() - self.start)
        failures = [r.name for r in results if r.returncode != 0]
        if not failures:
            self._tee(
                "\n".join(
                    [
                        "",
                        "═══ CI summary ═══",
                        f"Result:   ALL {total} STEPS PASSED",
                        f"Duration: {elapsed}s ({elapsed // 60}m{elapsed % 60:02d}s)",
                        f"Log:      {self.ctx.log_path}",
                        "Use this log as the falsifiable evidence behind any 'all "
                        + "gates' claim (see memory/feedback_gate_claim_integrity.md).",
                    ]
                ),
            )
            self.log_fh.close()
            return 0
        self._tee_err("")
        self._tee_err(
            f"═══ CI FAILED — {len(failures)} step(s) failed: {', '.join(failures)} ═══",
        )
        self._tee_err(f"Full log: {self.ctx.log_path}")
        self.log_fh.close()
        return 1


def build_prereq_cmd(python: str) -> list[str]:
    """Return the ``build`` prereq command (staleness-verifying build, not bare cabal build)."""
    return [python, "-m", "tools.check_build_incremental"]


def _run_agda_gates(runner: Runner, cabal: list[str]) -> None:
    """Run the Agda gate sweep plus the two branch-scoped IWYU gates."""
    # ─── Agda gates ─────────────────────────────────────────────
    # `build` first as a separate prereq: it produces the .so / .agdai every
    # other lane needs, and a build failure short-circuits the whole sweep
    # before the parallel lanes spawn (run() special-cases the "build" step).
    # `build` is the sole build prereq AND the staleness gate: it builds, then
    # proves the .so reflects every source change (never stale — the failure the
    # old `rm -rf` sledgehammer masked).  Runs first and ALONE (run() special-cases
    # "build"; it transiently mutates a source + the artifact and restores both).
    # Detail: tools/check_build_incremental.py, memory/project_build_so_idempotency.md.
    runner.step(
        "build",
        build_prereq_cmd(runner.python),
        cwd=runner.repo_root,
        lane="agda",
    )
    # All remaining cabal-shake gates fold into ONE invocation (the Agda-gate
    # fan-in): Shake
    # parallelizes the independent phony rules internally (shakeThreads=0) and
    # the per-process cabal/shake startup + build-graph re-validation is paid
    # once, not once per gate.  Shake fails fast on the first failing target and
    # names it on stderr — surfaced in the failure tail — so attribution
    # survives the fan-in.  AGDA_SHAKE_TARGETS is the single source of truth.
    runner.step(AGDA_GATES_STEP, [*cabal, *AGDA_SHAKE_TARGETS], lane="agda")

    # ─── IWYU gate (one tool) ───────────────────────────────
    # iwyu --check judges BOTH named imports (DEAD/UNRESOLVED) and
    # wildcard `open import M` (DEAD/REDUNDANT/NARROWABLE) via the scope-aware
    # `.agdai` reader in one warm process — no recompile-confirm.  Scope is
    # branch-diff by default (`--diff`: git diff main...HEAD -- src/; empty diff
    # ⇒ no-op — local pre-push-hook parity), or the whole tree (`--all`) under
    # `--iwyu-all` / ALETHEIA_IWYU_ALL=1 — airtight against cross-file deadness,
    # which is what the server-side PR merge gate runs.  iwyu-self-test
    # (`iwyu --self-test`) validates that reader against the synthetic fixture
    # matrix (its correctness gate).  Reference: memory/project_agda_iwyu.md.
    iwyu_scope = "--all" if runner.opts.iwyu_all else "--diff"
    runner.step(
        "iwyu",
        [runner.python, "-m", "tools.iwyu", "--check", iwyu_scope],
        cwd=runner.repo_root,
        lane="agda",
    )
    runner.step(
        "iwyu-self-test",
        [runner.python, "-m", "tools.iwyu", "--self-test"],
        cwd=runner.repo_root,
        lane="agda",
    )


def _run_binding_tests(runner: Runner) -> None:
    """Run the Python / Go / C++ / Rust binding test lanes."""
    # ─── Binding tests ────────────────────────────────────────
    # Deterministic pytest lane.
    runner.step(
        "pytest",
        [runner.python, "-m", "pytest", "tests/"],
        cwd=runner.repo_root / "python",
    )
    # Doc-example fence harness.  Runs from the repo root (cwd=repo_root → would
    # infer the "misc" lane), but it is a pytest invocation sharing the Python
    # toolchain, so pin it to the "python" lane explicitly to keep all pytest
    # runs serial within one lane (the lane invariant; cwd-based inference can't
    # see that a repo-root `python -m pytest` belongs with the python/ steps).
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
        lane="python",
    )
    # Python -X dev mode (Cat 34a).
    runner.step(
        "pytest -X dev",
        [runner.python, "-X", "dev", "-m", "pytest", "tests/"],
        cwd=runner.repo_root / "python",
    )
    # Random-order test isolation (Cat 14f).
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
        # Pin to clang-22 — the supported toolchain (latest stable), the SAME
        # compiler the sanitizer + mutation lanes use, so unit tests sanitize the
        # same compilation we ship. Bare `clang`/default cc resolves to the
        # runner's clang-18 / g++ (clang < 19 mis-handles libstdc++-14's C++23
        # <expected>); clang-22 is version-pinned + installed by the workflow via
        # apt.llvm.org (no update-alternatives roulette).
        "cmake -B build -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22 "
        + "> /dev/null && cmake --build build && ctest --test-dir build",
        cwd=runner.repo_root / "cpp",
    )
    # Rust binding — loads libaletheia-ffi.so at runtime (like Go / C++). The
    # tracer-bullet slice proves the FFI lifecycle + GHC-allocated-memory
    # ownership; ALETHEIA_LIB points cargo's test at the freshly built .so.
    rust_lib = shlex.quote(str(runner.repo_root / "build" / "libaletheia-ffi.so"))
    runner.step(
        "cargo test",
        f"ALETHEIA_LIB={rust_lib} cargo test",
        cwd=runner.repo_root / "rust",
    )


def _run_lints(runner: Runner) -> None:
    """Run the Python / Go / C++ / Rust lint gates."""
    # ─── Lints ────────────────────────────────────────────────
    # ruff (`select=["ALL"]`, config in ruff.toml) over the WHOLE Python tree
    # INCLUDING tools/ (repo-root gate scripts) — both `check` and
    # `format --check`.  `python/mutants` (mutmut output) is excluded in
    # ruff.toml.  Run from the repo root so the root ruff.toml is the config.
    # `--no-cache`: ruff's result cache is keyed on mtime, not file mode, so a
    # cached run silently passes file-mode rules like EXE001 ("shebang present
    # but file not executable") that a fresh CI run catches — making the local
    # sweep / pre-push hook give a false green.  ruff is sub-second, so running
    # cache-free here costs nothing and keeps local == CI.  See
    # memory/feedback_no_shebang_in_tools.md.
    ruff_cmd = (
        f"{shlex.quote(runner.python)} -m ruff check --no-cache tools examples python conftest.py "
        f"&& {shlex.quote(runner.python)} -m ruff format --check tools examples python conftest.py"
    )
    runner.step("ruff", ruff_cmd, cwd=runner.repo_root)

    # ``benchmarks/`` joined the basedpyright gate 2026-05-09, ``tests/`` on
    # 2026-05-31, and ``../tools/`` on 2026-06-06 (pyproject has a strict
    # executionEnvironment for ../tools); pylint covers the same set, so the
    # two stay symmetric (feedback_no_subsumption_asymmetry.md).
    #
    # Invoke via ``runner.python -m basedpyright`` (not the bare ``basedpyright``
    # console script) for the same reason as ruff/pylint — CI launches this sweep
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

    # clang-tidy (AGENTS.md § lint gates, mandatory): the C++ sources —
    # src/*.cpp plus the CLI sources under src/cli/ (the aletheia-cli host
    # binary + aletheia::run_cli), which the top-level glob does not match.
    runner.step(
        "clang-tidy",
        "clang-tidy-22 -p build src/*.cpp src/cli/*.cpp",
        cwd=runner.repo_root / "cpp",
    )

    # Rust lints: rustfmt (check) + clippy (deny warnings) — the cargo
    # equivalents of gofmt+vet / clang-format+clang-tidy.
    runner.step(
        "cargo fmt + clippy",
        "cargo fmt --check && cargo clippy --all-targets -- -D warnings",
        cwd=runner.repo_root / "rust",
    )


def _run_gha_checks(runner: Runner) -> None:
    """Run the GitHub-Actions workflow meta-checks plus the SPDX-header gate."""
    # ─── GHA meta-checks + SPDX header gate ──────────────────────────────────────
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
    runner.step(
        "check-venv-convention",
        [runner.python, "-m", "tools.check_venv_convention"],
        cwd=runner.repo_root,
    )


def _run_opt_in_lanes(runner: Runner, opts: OptInOptions) -> None:
    """Run the always-on UBSan lane then the enabled repro / stability / mutation lanes."""
    # ─── Opt-in lanes (off by default) ──────────────────────────
    # The opt-in lanes share the same step counter as the always-on steps and are
    # tallied by main()'s counting pass too (step() runs in both passes), so
    # total_steps and the "ALL N STEPS PASSED" line in finalize() already reflect
    # whichever lanes are enabled — no separate per-lane bookkeeping here.

    # Always-on UBSan lane (Cat 33a; promoted from opt-in to
    # always-on after UB in Rational::from_double had previously shipped
    # undetected exactly because the lane was opt-in).  Builds the full
    # ctest battery against -DALETHEIA_SANITIZER=undefined and asserts
    # every test passes.  Vendored zippy.hpp UB filtered via
    # cpp/sanitizer-ignorelist.txt; clang required (g++ has no equivalent).
    runner.step(
        "ubsan ctest",
        # clang-22 (the supported toolchain — matches the regular ctest + mutation
        # lanes).  UB can differ between compiler versions, so the sanitizer lane
        # MUST exercise the shipped compiler's codegen, not an older clang; bare
        # `clang++` also resolves to the runner's clang-18, which fails to compile
        # libstdc++-14's <expected> (std::expected, C++23).
        "cmake -B build-ubsan -DALETHEIA_SANITIZER=undefined "
        + "-DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22 > /dev/null"
        + " && cmake --build build-ubsan && ctest --test-dir build-ubsan",
        cwd=runner.repo_root / "cpp",
        # Own lane (not "cpp"): ubsan uses a SEPARATE build-ubsan/ dir, so it runs
        # concurrently with the cpp lane's ctest→clang-tidy on build/ — splitting
        # the local C++ bottleneck (~305s → ~180s, measured 2026-06-14).
        lane="ubsan",
    )

    # Opt-in: reproducible-build gate ────────────────────────────
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

    # Opt-in: long-run stability bench ───────────────────────────
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

    # Opt-in: mutation testing across all 3 bindings ─────────────
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


def _run_all_phases(runner: Runner, cabal: list[str], opts: OptInOptions) -> None:
    """Register every phase's steps into the runner (no execution; run() drives them)."""
    _run_agda_gates(runner, cabal)
    _run_binding_tests(runner)
    _run_lints(runner)
    _run_gha_checks(runner)
    _run_opt_in_lanes(runner, opts)


def main(argv: list[str] | None = None) -> int:
    """Run the full offline CI sweep, returning the process exit code."""
    opts = parse_args(argv)
    repo_root = _git_root()
    os.chdir(repo_root)
    runner = Runner(opts, RunContext.discover(repo_root))
    cabal = ["cabal", "run", "shake", "--"]

    # Register every step into its toolchain lane (no execution yet), then run:
    # build first, then the lanes — serial by default, concurrently under
    # --parallel — with deterministic teeing and fail-loud aggregation.
    _run_all_phases(runner, cabal, opts)
    return runner.run()


if __name__ == "__main__":
    sys.exit(main())
