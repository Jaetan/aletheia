#!/usr/bin/env python3
"""tools/run_ci.py — Offline CI orchestrator (R18 cluster 1 phase 3 + cluster 7).

Chains the full gate sweep that commit messages have historically asserted
"all gates clean / green" against, plus the cluster 1 phase 1+2 enforcers
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

═══ ALWAYS-ON STEPS (27 total) ═══

  Agda gates (8):
     1. build           — produces libaletheia-ffi.so
     2. check-properties     (longest, ~8-10 min)
     3. check-invariants
     4. check-no-properties-in-runtime
     5. check-erasure
     6. check-fidelity       (~2 min — runs ConstructorTest binary)
     7. check-ffi-exports
     8. count-modules
  Offline enforcers (5):
     9. check-changelog
    10. check-gate-claim
    11. check-runbook            (R18 cluster 4)
    12. check-stability-bench    (R18 cluster 6 static gate)
    13. check-mutation-setup     (R18 cluster 7 static gate)
  Binding tests (6):
    14. Python pytest (deterministic lane)
    15. Python pytest --markdown-docs (R18 cluster 5 — Cat 32 doc-example
        harness; was silently absent from the orchestrator before C5)
    16. Python pytest -X dev (R18 cluster 5 — Cat 34a; surfaces
        ResourceWarning, debug asyncio, deprecation noise)
    17. Python pytest --random-order (R18 cluster 5 — Cat 14f
        test-isolation; AGENTS.md "both lanes must stay green")
    18. Go test -race
    19. C++ ctest
  Lints (5):
    20. basedpyright (Python)
    21. pylint 10/10 (Python — SCORE-based gate per AGENTS.md L611)
    22. gofmt -l + go vet (Go)
    23. clang-format --dry-run --Werror (C++)
    24. clang-tidy -p build (C++ — mandatory per AGENTS.md L494)
  GHA meta-checks (3):
    25. actionlint (workflow YAML lint, skipped if not installed)
    26. check-action-pins
    27. check-workflow-permissions

═══ OPT-IN LANES (4 total) ═══

Each opt-in lane is gated on EITHER a command-line flag OR an environment
variable.  Precedence: CLI flag overrides env var; env var overrides default
(off).  ``--full`` enables every opt-in lane.  ``--no-<lane>`` disables a
lane that env vars would otherwise enable (useful when the pre-push hook is
running in a context where one lane is too slow).

  ──────────────────────────────────────────────────────────────────────
  Flag           Env var                       Cost  Wires which step?
  ──────────────────────────────────────────────────────────────────────
  --san          ALETHEIA_SAN_CHECK=1          ~5m   28: ubsan ctest
  --repro        ALETHEIA_REPRO_CHECK=1        ~10m  29: check-reproducible-build
  --stability    ALETHEIA_STABILITY_CHECK=1    ~5m   30: stability bench
  --mutation     ALETHEIA_MUTATION_CHECK=1     ~30m+ 31: mutation testing lane
  ──────────────────────────────────────────────────────────────────────
  --full         (all four above)              ~50m+ all opt-ins

Total wall-time: ~17-22 min always-on, plus enabled opt-ins.  ``--full`` on
a warm host typically lands in 50-90 min; cold (no test cache, no Mull
build-mutation tree) closer to 60-120 min.

═══ Python venv pinning ═══

The Python lanes (steps 14-21) prefer ``python/.venv/bin/python3`` over
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
# pylint: disable=too-many-instance-attributes,too-many-locals,too-many-statements

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
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path


def _git_root() -> Path:
    rc = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=False,
    )
    if rc.returncode != 0:
        sys.stderr.write("run-ci: not inside a git repo\n")
        sys.exit(2)
    return Path(rc.stdout.strip())


_INVALID_BRANCH_CHAR = re.compile(r"[^A-Za-z0-9_.-]")


@dataclass
class OptInOptions:
    """Resolved opt-in lane state.  CLI > env > default-off precedence."""
    san: bool
    repro: bool
    stability: bool
    mutation: bool

    @property
    def any_enabled(self) -> bool:
        return self.san or self.repro or self.stability or self.mutation

    def enabled_count(self) -> int:
        return sum([self.san, self.repro, self.stability, self.mutation])


def _resolve_flag(cli_value: bool | None, env_var: str) -> bool:
    """Resolve a tri-state CLI flag (--lane / --no-lane / unset) against an
    env-var fallback.  Returns True iff the lane should run.
    """
    if cli_value is not None:
        return cli_value
    return os.environ.get(env_var) == "1"


def parse_args(argv: list[str] | None = None) -> OptInOptions:
    parser = argparse.ArgumentParser(
        prog="tools/run_ci.py",
        description="Offline CI orchestrator (R18 cluster 1 + 7).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Opt-in lanes can be enabled via CLI flags, env vars, or `--full`.\n"
            "CLI flags override env vars; env vars override the default (off).\n"
            "\n"
            "Examples:\n"
            "  tools/run_ci.py                       # always-on steps only\n"
            "  tools/run_ci.py --full                # everything (50-90 min)\n"
            "  tools/run_ci.py --san --stability     # two specific lanes\n"
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

    _add_lane("san", "ALETHEIA_SAN_CHECK",
              "UBSan ctest battery (R18 cluster 5; ~5 min cold)")
    _add_lane("repro", "ALETHEIA_REPRO_CHECK",
              "reproducible-build hash gate (R18 cluster 3; ~10 min cold)")
    _add_lane("stability", "ALETHEIA_STABILITY_CHECK",
              "long-run stability bench (R18 cluster 6; ~5 min cold)")
    _add_lane("mutation", "ALETHEIA_MUTATION_CHECK",
              "mutation testing across 3 bindings (R18 cluster 7; ~30 min+)")

    parser.add_argument(
        "--full",
        action="store_true",
        help=(
            "Enable every opt-in lane (equivalent to --san --repro --stability "
            "--mutation).  Individual --no-<lane> flags can still subtract from "
            "the --full set (e.g. --full --no-mutation runs everything except "
            "mutation testing)."
        ),
    )

    args = parser.parse_args(argv)

    # --full sets every unset CLI flag to True; explicit --no-<lane> keeps False.
    # The order matters: apply --full BEFORE _resolve_flag so the env var still
    # gets to enable a lane that --full + --no-<other> didn't touch.
    if args.full:
        for lane in ("san", "repro", "stability", "mutation"):
            if getattr(args, lane) is None:
                setattr(args, lane, True)

    return OptInOptions(
        san=_resolve_flag(args.san, "ALETHEIA_SAN_CHECK"),
        repro=_resolve_flag(args.repro, "ALETHEIA_REPRO_CHECK"),
        stability=_resolve_flag(args.stability, "ALETHEIA_STABILITY_CHECK"),
        mutation=_resolve_flag(args.mutation, "ALETHEIA_MUTATION_CHECK"),
    )


class Runner:
    BASE_STEPS = 27  # always-on steps after the cluster-7 + offline-enforcers expansion

    def __init__(self, opts: OptInOptions) -> None:
        self.opts = opts
        self.repo_root = _git_root()
        os.chdir(self.repo_root)

        log_dir = self.repo_root / "tools" / "ci-output"
        log_dir.mkdir(parents=True, exist_ok=True)

        branch = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
        branch_safe = _INVALID_BRANCH_CHAR.sub("_", branch)
        timestamp = datetime.datetime.now(datetime.timezone.utc).strftime(
            "%Y-%m-%dT%H-%M-%SZ"
        )

        self.branch = branch
        self.commit = commit
        self.log_path = log_dir / f"ci-{branch_safe}-{timestamp}.log"
        self.log_fh = self.log_path.open("w", encoding="utf-8")
        self.step_num = 0
        self.total_steps = self.BASE_STEPS + self.opts.enabled_count()
        self.failed_step: str | None = None
        self.start = time.time()
        # Prefer the project's venv if present so dev-extras (markdown-docs,
        # random-order, hypothesis, mutmut) resolve.  Falls back to system
        # python3 for systems where the lanes are intentionally exercised
        # against the global env (e.g. release builds).
        venv_python = self.repo_root / "python" / ".venv" / "bin" / "python3"
        self.python = str(venv_python) if venv_python.exists() else "python3"

    def header(self) -> None:
        opt_in_summary = []
        for name, enabled in (
            ("san", self.opts.san),
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
            f"Started:  {datetime.datetime.now(datetime.timezone.utc):%Y-%m-%d %H:%M:%S UTC}",
            f"Branch:   {self.branch}",
            f"Commit:   {self.commit}",
            f"Steps:    {self.total_steps} ({self.BASE_STEPS} always-on + "
            f"{self.opts.enabled_count()} opt-in)",
            f"Opt-ins:  {' '.join(opt_in_summary)}",
            f"Log:      {self.log_path}",
            "",
        ]
        self._tee("\n".join(lines))

    def _tee(self, text: str) -> None:
        sys.stdout.write(text + "\n")
        sys.stdout.flush()
        self.log_fh.write(text + "\n")
        self.log_fh.flush()

    def _tee_err(self, text: str) -> None:
        sys.stderr.write(text + "\n")
        sys.stderr.flush()
        self.log_fh.write(text + "\n")
        self.log_fh.flush()

    def _step_header(self, name: str, cmd: Sequence[str] | str) -> None:
        cmd_str = cmd if isinstance(cmd, str) else " ".join(cmd)
        lines = [
            "",
            f"─── Step {self.step_num}/{self.total_steps}: {name} ───",
            f"Cmd:    {cmd_str}",
            f"Start:  {datetime.datetime.now(datetime.timezone.utc):%Y-%m-%d %H:%M:%S UTC}",
        ]
        self._tee("\n".join(lines))

    def _print_tail_on_failure(self, name: str, exit_code: int, duration: int) -> None:
        self._tee_err(f"  ✗ {name} FAILED (exit {exit_code}, {duration}s)")
        self._tee_err("")
        self._tee_err("─── Tail of failed step output ───")
        self.log_fh.flush()
        log_text = self.log_path.read_text(encoding="utf-8", errors="replace")
        for line in log_text.splitlines()[-50:]:
            sys.stderr.write(line + "\n")
        sys.stderr.flush()
        self._tee_err("")
        self._tee_err(
            f"═══ CI FAILED at step {self.step_num}/{self.total_steps}: {name} ═══"
        )
        self._tee_err(f"Full log: {self.log_path}")

    def step(
        self,
        name: str,
        cmd: Sequence[str] | str,
        *,
        cwd: Path | None = None,
        shell: bool = False,
    ) -> None:
        if self.failed_step is not None:
            return
        self.step_num += 1
        self._step_header(name, cmd)
        step_start = time.time()
        if shell:
            assert isinstance(cmd, str)
            proc = subprocess.run(
                cmd, shell=True,
                stdout=self.log_fh, stderr=subprocess.STDOUT,
                cwd=cwd, check=False,
            )
        else:
            proc = subprocess.run(
                list(cmd),
                stdout=self.log_fh, stderr=subprocess.STDOUT,
                cwd=cwd, check=False,
            )
        duration = int(time.time() - step_start)
        if proc.returncode != 0:
            self.failed_step = name
            self._print_tail_on_failure(name, proc.returncode, duration)
            return
        sys.stderr.write(f"  ✓ {name} ({duration}s)\n")
        self.log_fh.write(f"  ✓ {name} ({duration}s)\n")
        self.log_fh.flush()

    def announce_skip(self, name: str, reason: str) -> None:
        # Skipped steps don't bump the step counter — they're not part of
        # total_steps in the first place (only enabled lanes are counted).
        # We still log the skip line so the log is complete.
        msg = f"  ⊘ {name} skipped ({reason})"
        sys.stderr.write(msg + "\n")
        self.log_fh.write(msg + "\n")
        self.log_fh.flush()

    def finalize(self) -> int:
        total = int(time.time() - self.start)
        if self.failed_step is None:
            lines = [
                "",
                "═══ CI summary ═══",
                f"Result:   ALL {self.total_steps} STEPS PASSED",
                f"Duration: {total}s ({total // 60}m{total % 60:02d}s)",
                f"Log:      {self.log_path}",
                "Use this log file as the falsifiable evidence behind any 'all "
                "gates' claim in commit messages "
                "(see memory/feedback_gate_claim_integrity.md).",
            ]
            self._tee("\n".join(lines))
            self.log_fh.close()
            return 0
        self.log_fh.close()
        return 1


def main(argv: list[str] | None = None) -> int:
    opts = parse_args(argv)
    r = Runner(opts)
    r.header()

    cabal = ["cabal", "run", "shake", "--"]

    # ─── Steps 1-8: Agda gates ─────────────────────────────────────────────
    r.step("build", [*cabal, "build"])
    r.step("check-properties", [*cabal, "check-properties"])
    r.step("check-invariants", [*cabal, "check-invariants"])
    r.step("check-no-properties-in-runtime", [*cabal, "check-no-properties-in-runtime"])
    r.step("check-erasure", [*cabal, "check-erasure"])
    r.step("check-fidelity", [*cabal, "check-fidelity"])
    r.step("check-ffi-exports", [*cabal, "check-ffi-exports"])
    r.step("count-modules", [*cabal, "count-modules"])

    # ─── Steps 9-13: Offline enforcers ─────────────────────────────────────
    r.step("check-changelog", [*cabal, "check-changelog"])
    r.step("check-gate-claim", [*cabal, "check-gate-claim"])
    r.step("check-runbook", [*cabal, "check-runbook"])
    r.step("check-stability-bench", [*cabal, "check-stability-bench"])
    r.step("check-mutation-setup", [*cabal, "check-mutation-setup"])

    # ─── Steps 14-19: Binding tests ────────────────────────────────────────
    # Step 14: deterministic pytest lane.
    r.step("pytest", [r.python, "-m", "pytest", "tests/"], cwd=r.repo_root / "python")
    # Step 15: doc-example fence harness (R18 cluster 5).
    r.step(
        "pytest --markdown-docs",
        [r.python, "-m", "pytest", "--markdown-docs", "README.md", "docs/"],
        cwd=r.repo_root,
    )
    # Step 16: Python -X dev mode (R18 cluster 5 — Cat 34a).
    r.step(
        "pytest -X dev",
        [r.python, "-X", "dev", "-m", "pytest", "tests/"],
        cwd=r.repo_root / "python",
    )
    # Step 17: random-order test isolation (R18 cluster 5 — Cat 14f).
    r.step(
        "pytest --random-order",
        [
            r.python, "-m", "pytest", "--random-order",
            "--random-order-bucket=package", "tests/",
        ],
        cwd=r.repo_root / "python",
    )
    r.step(
        "go test -race",
        ["go", "test", "./aletheia/", "-count=1", "-race"],
        cwd=r.repo_root / "go",
    )
    r.step(
        "ctest",
        "cmake -B build > /dev/null && cmake --build build && ctest --test-dir build",
        cwd=r.repo_root / "cpp", shell=True,
    )

    # ─── Steps 20-24: Lints ────────────────────────────────────────────────
    r.step("basedpyright", ["basedpyright", "aletheia/"], cwd=r.repo_root / "python")

    # pylint SCORE-based gate per AGENTS.md L611 + feedback_pylint_10_mandatory.md.
    pylint_cmd = (
        f"{shlex.quote(r.python)} -m pylint aletheia/ tests/ "
        "> /tmp/aletheia-pylint.out 2>&1; "
        "rc=$?; cat /tmp/aletheia-pylint.out; "
        "grep -q 'rated at 10\\.00/10' /tmp/aletheia-pylint.out"
    )
    r.step("pylint", pylint_cmd, cwd=r.repo_root / "python", shell=True)

    # gofmt -l (LIST mode): stdout non-empty == files need reformatting.
    gofmt_cmd = (
        "gofmt -l ./aletheia/ > /tmp/aletheia-gofmt.out 2>&1; rc=$?; "
        "cat /tmp/aletheia-gofmt.out; "
        "test $rc -eq 0 && test ! -s /tmp/aletheia-gofmt.out && go vet ./aletheia/"
    )
    r.step("gofmt + go vet", gofmt_cmd, cwd=r.repo_root / "go", shell=True)

    # clang-format: exclude generated / third-party trees + sanitizer/mutation
    # build trees.
    clang_format_cmd = (
        "find . \\( -path ./build -o -path ./build-tidy "
        "-o -path ./build-asan -o -path ./build-ubsan "
        "-o -path ./build-mutation "
        "-o -path ./_deps -o -path './*/_deps' \\) -prune -o "
        "\\( -name '*.cpp' -o -name '*.hpp' \\) -print | "
        "xargs clang-format --dry-run --Werror"
    )
    r.step("clang-format", clang_format_cmd, cwd=r.repo_root / "cpp", shell=True)

    # clang-tidy: AGENTS.md L580 canonical scope (src/*.cpp).
    r.step(
        "clang-tidy",
        "clang-tidy -p build src/*.cpp",
        cwd=r.repo_root / "cpp", shell=True,
    )

    # ─── Steps 25-27: GHA meta-checks ──────────────────────────────────────

    if shutil.which("actionlint"):
        if (r.repo_root / ".github" / "workflows").is_dir():
            r.step("actionlint", ["actionlint", "-color"])
        else:
            r.announce_skip("actionlint", "no .github/workflows/ directory")
    else:
        r.announce_skip(
            "actionlint",
            "binary not installed; see docs/development/CI_LOCAL.md",
        )

    r.step(
        "check-action-pins",
        [sys.executable, str(r.repo_root / "tools" / "check_action_pins.py")],
    )
    r.step(
        "check-workflow-permissions",
        [
            sys.executable,
            str(r.repo_root / "tools" / "check_workflow_permissions.py"),
        ],
    )

    # ─── Opt-in lanes (numbered 28+ when enabled) ──────────────────────────
    # Each lane is appended to total_steps in __init__ via opts.enabled_count();
    # they share the same step counter as always-on steps so the "ALL N STEPS
    # PASSED" line in finalize() matches the actual count.

    # Step 28 (opt-in): UBSan lane (R18 cluster 5 — Cat 33a) ───────────────
    # Builds the full ctest battery against -DALETHEIA_SANITIZER=undefined and
    # asserts every test passes.  Vendored zippy.hpp UB filtered via
    # cpp/sanitizer-ignorelist.txt; clang required (g++ has no equivalent).
    if opts.san:
        r.step(
            "ubsan ctest",
            "cmake -B build-ubsan -DALETHEIA_SANITIZER=undefined "
            "-DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ > /dev/null"
            " && cmake --build build-ubsan && ctest --test-dir build-ubsan",
            cwd=r.repo_root / "cpp", shell=True,
        )
    else:
        r.announce_skip(
            "ubsan ctest",
            "set ALETHEIA_SAN_CHECK=1 or pass --san to enable",
        )

    # Step 29 (opt-in): reproducible-build gate ────────────────────────────
    if opts.repro:
        r.step(
            "check-reproducible-build",
            [
                sys.executable,
                str(r.repo_root / "tools" / "check_reproducible_build.py"),
            ],
        )
    else:
        r.announce_skip(
            "check-reproducible-build",
            "set ALETHEIA_REPRO_CHECK=1 or pass --repro to enable",
        )

    # Step 30 (opt-in): long-run stability bench ───────────────────────────
    # R18 cluster 6 (Agda cat 16 + Python cat 25 + C++ cat 26 + Go cat 27).
    if opts.stability:
        r.step(
            "stability bench",
            [sys.executable, str(r.repo_root / "tools" / "stability_run.py")],
        )
    else:
        r.announce_skip(
            "stability bench",
            "set ALETHEIA_STABILITY_CHECK=1 or pass --stability to enable",
        )

    # Step 31 (opt-in): mutation testing across all 3 bindings ─────────────
    # R18 cluster 7 (Cat 14g).  AGENTS.md: "Mutation testing runs as a
    # separate CI lane (cost is high) — once per PR is sufficient; per-commit
    # is overkill."  Default OFF.  See docs/operations/MUTATION.md.
    if opts.mutation:
        r.step(
            "mutation testing",
            [sys.executable, str(r.repo_root / "tools" / "mutation_run.py")],
        )
    else:
        r.announce_skip(
            "mutation testing",
            "set ALETHEIA_MUTATION_CHECK=1 or pass --mutation to enable",
        )

    return r.finalize()


if __name__ == "__main__":
    sys.exit(main())
