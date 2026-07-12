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
      failure short-circuits the whole sweep before the lanes spawn).  Runs the
      staleness gate (tools/check_build_incremental.py — ~2 .so relinks) only
      when a build-graph file changed (--build-staleness=auto, the default) or
      always on push:main (--build-staleness=always); otherwise a plain
      `cabal run shake -- build` (warm-cache no-op).
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
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, TextIO

from tools._ci_steps import FAST_STEPS, HEAVY_STEPS, register_all_steps
from tools._common import emit, find_executable, git_toplevel
from tools._resources import cpu_budget
from tools._scheduler import Step, StepResult, run_lanes

if TYPE_CHECKING:
    from collections.abc import Sequence

# Number of trailing log lines echoed to stderr when a step fails.
FAILURE_TAIL_LINES = 50

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
    # Build-staleness scheduling for the `build` step (see tools/_ci_steps
    # should_run_staleness): "auto" (default) runs the staleness gate
    # (check_build_incremental, ~2 .so relinks) only when a build-graph file
    # changed; "always" is the push:main backstop, "never" an escape hatch.
    # Not a lane — it picks the build COMMAND, not the step count.
    build_staleness: str = "auto"
    # Pre-commit FAST tier: restrict the sweep to the compile-free static gates
    # (tools._ci_steps.FAST_STEPS) and skip the `build` prereq.  Used by the
    # pre-commit hook to block non-conforming commits in seconds; pre-push still
    # runs the full sweep.  A no-op subset filter, so it never changes a step's
    # command — no gate drift between commit-time and push-time definitions.
    fast: bool = False

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


_BUILD_STALENESS_MODES = ("auto", "always", "never")


def _resolve_build_staleness(cli_value: str | None) -> str:
    """Resolve build-staleness mode: CLI > env > "auto" default; invalid env → "auto"."""
    if cli_value in _BUILD_STALENESS_MODES:
        return cli_value
    env = os.environ.get("ALETHEIA_BUILD_STALENESS")
    return env if env in _BUILD_STALENESS_MODES else "auto"


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
        "--fast",
        action="store_true",
        default=False,
        help=(
            "Pre-commit FAST tier: run ONLY the compile-free static gates "
            "(format checks, SPDX/review-mark/venv hygiene, ruff, pylint) and "
            "skip the build prereq.  Seconds, not minutes; no build artifacts "
            "needed.  Used by the pre-commit hook; pre-push runs the full sweep."
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
    parser.add_argument(
        "--build-staleness",
        choices=_BUILD_STALENESS_MODES,
        default=None,
        help=(
            "When the `build` step runs the staleness gate (check_build_incremental, "
            "~2 .so relinks) vs a plain incremental build.  `auto` (default) runs it "
            "only when the diff vs `main` touches a build-graph file (Shakefile.hs, "
            "shake.cabal, the haskell-shim/, aletheia.agda-lib); `always` is the "
            "push:main backstop, `never` an escape hatch.  (env: ALETHEIA_BUILD_STALENESS)"
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
        build_staleness=_resolve_build_staleness(args.build_staleness),
        fast=args.fast or os.environ.get("ALETHEIA_CI_FAST") == "1",
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

    @property
    def registered_step_names(self) -> tuple[str, ...]:
        """Names of the steps registered so far, in registration order.

        A read-only view over the internal registry so a test can assert that
        ``register_all_steps`` (in ``tools/_ci_steps.py``) populated the catalog
        without reaching into ``_registry``.  The registration path is otherwise
        only exercised at real push time, where a moved helper referencing a name
        that no longer resolves after the run_ci/_ci_steps split would surface too
        late.
        """
        return tuple(entry.name for entry in self._registry)

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

    def restrict_to(self, names: frozenset[str]) -> list[str]:
        """Keep only registered steps whose name is in *names*; drop the rest.

        Used by the FAST tier (``--fast``): a pure subset filter that never
        alters a step's command, so a commit-time gate can't drift from its
        pre-push definition.  Returns the sorted list of *names* that did NOT
        resolve to a registered step (rename drift) and leaves the registry
        UNCHANGED in that case, so the caller can fail loud rather than silently
        run a smaller sweep.
        """
        kept = [s for s in self._registry if s.name in names]
        missing = sorted(names - {s.name for s in kept})
        if not missing:
            self._registry = kept
        return missing

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


def main(argv: list[str] | None = None) -> int:
    """Run the full offline CI sweep, returning the process exit code."""
    opts = parse_args(argv)
    repo_root = _git_root()
    os.chdir(repo_root)
    runner = Runner(opts, RunContext.discover(repo_root))
    cabal = ["cabal", "run", "shake", "--"]

    # Register every step into its toolchain lane (no execution yet), then run:
    # build first, then the lanes — serial by default, concurrently under
    # --parallel — with deterministic teeing and fail-loud aggregation.  The
    # step catalog lives in tools/_ci_steps.py (the part of the sweep that grows).
    register_all_steps(runner, cabal, opts)
    if opts.fast:
        # Restrict to the compile-free static allowlist and drop everything else
        # (including the `build` prereq — no FAST step needs it).  A pure subset
        # filter: no step's command changes, so the commit-time gate can never
        # drift from the pre-push definition of the same check.
        missing = runner.restrict_to(FAST_STEPS)
        if missing:
            # A FAST_STEPS name that no longer resolves to a registered step is a
            # rename drift — fail loudly rather than silently skip a gate.
            drift = ", ".join(missing)
            msg = f"run_ci --fast: FAST_STEPS names not in the registry (rename drift?): {drift}\n"
            sys.stderr.write(msg)
            return 2
    return runner.run()


if __name__ == "__main__":
    sys.exit(main())
