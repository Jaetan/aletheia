#!/usr/bin/env python3
"""tools/run_ci.py — Offline CI orchestrator (R18 cluster 1 phase 3).

Chains the full gate sweep that commit messages have historically
asserted "all gates clean / green" against, plus the cluster 1 phase 1+2
enforcers (check-changelog, check-gate-claim).  Captures all output to
a timestamped log under ``tools/ci-output/`` so the gate-claim-integrity
enforcer can point at it as falsifiable evidence (v1+ artifact-based
design).

Invoked from:
  * ``tools/run_ci.py`` (direct, manual or scripted)
  * ``.git/hooks/pre-push`` (auto-installed by tools/install_hooks.py)

Deliberately NOT exposed as a Shake ``phony "ci"`` target — the runner's
inner ``cabal run shake -- build`` invocation fails to acquire
cabal-install's ``dist-newstyle/`` flock when the parent process is
itself ``cabal run``.  Direct invocation avoids the flock-recursion
entirely.  See Shakefile.hs comment block where the ``ci`` phony would
otherwise live.

Sequence (sequential — fast-fail on any non-zero exit)::

    Agda gates (8):
       1. build           — produces libaletheia-ffi.so
       2. check-properties     (longest, ~8-10 min)
       3. check-invariants
       4. check-no-properties-in-runtime
       5. check-erasure
       6. check-fidelity       (~2 min — runs ConstructorTest binary)
       7. check-ffi-exports
       8. count-modules
    Offline enforcers (3):
       9. check-changelog
      10. check-gate-claim
      11. check-runbook       (R18 cluster 4)
    Binding tests (3):
      12. Python pytest
      13. Go test -race
      14. C++ ctest
    Lints (5):
      15. basedpyright (Python)
      16. pylint 10/10 (Python — SCORE-based gate per AGENTS.md L611)
      17. gofmt -l + go vet (Go)
      18. clang-format --dry-run --Werror (C++)
      19. clang-tidy -p build (C++ — mandatory per AGENTS.md L494)
    GHA meta-checks (3):
      20. actionlint (workflow YAML lint, skipped if not installed)
      21. check-action-pins
      22. check-workflow-permissions
    Opt-in (1, set ALETHEIA_REPRO_CHECK=1):
      23. check-reproducible-build (~10 min cold; two clean builds)

Total ~15-20 min on a warm system.  Step 23 (opt-in) costs another ~10 min.

Exit codes:
  0 — all 22 steps passed (or skipped where allowed).
  1 — at least one step failed; tail of log printed to stderr.
  2 — usage error (e.g., not in a git repo, missing dependency).
"""
from __future__ import annotations

import datetime
import os
import re
import shutil
import subprocess
import sys
import time
from collections.abc import Sequence
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


class Runner:
    def __init__(self) -> None:
        self.repo_root = _git_root()
        os.chdir(self.repo_root)

        log_dir = self.repo_root / "tools" / "ci-output"
        log_dir.mkdir(parents=True, exist_ok=True)

        branch = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=True,
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
        self.total_steps = 22
        self.failed_step: str | None = None
        self.start = time.time()

    def header(self) -> None:
        lines = [
            "═══ Aletheia offline CI sweep ═══",
            f"Started:  {datetime.datetime.now(datetime.timezone.utc):%Y-%m-%d %H:%M:%S UTC}",
            f"Branch:   {self.branch}",
            f"Commit:   {self.commit}",
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
        # Read the log file's tail and print to stderr.
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
                cmd,
                shell=True,
                stdout=self.log_fh,
                stderr=subprocess.STDOUT,
                cwd=cwd,
                check=False,
            )
        else:
            proc = subprocess.run(
                list(cmd),
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
        sys.stderr.write(f"  ✓ {name} ({duration}s)\n")
        self.log_fh.write(f"  ✓ {name} ({duration}s)\n")
        self.log_fh.flush()

    def announce_skip(self, name: str, reason: str) -> None:
        if self.failed_step is not None:
            return
        self.step_num += 1
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


def main() -> int:
    r = Runner()
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

    # ─── Steps 9-11: Offline enforcers ─────────────────────────────────────
    r.step("check-changelog", [*cabal, "check-changelog"])
    r.step("check-gate-claim", [*cabal, "check-gate-claim"])
    r.step("check-runbook", [*cabal, "check-runbook"])

    # ─── Steps 12-14: Binding tests ────────────────────────────────────────
    r.step("pytest", ["python3", "-m", "pytest", "tests/"], cwd=r.repo_root / "python")
    r.step(
        "go test -race",
        ["go", "test", "./aletheia/", "-count=1", "-race"],
        cwd=r.repo_root / "go",
    )
    # ctest needs the build dir freshly configured + built.
    r.step(
        "ctest",
        "cmake -B build > /dev/null && cmake --build build && ctest --test-dir build",
        cwd=r.repo_root / "cpp",
        shell=True,
    )

    # ─── Steps 15-19: Lints ────────────────────────────────────────────────
    r.step("basedpyright", ["basedpyright", "aletheia/"], cwd=r.repo_root / "python")

    # pylint: SCORE-based gate per AGENTS.md L611 + feedback_pylint_10_mandatory.md.
    # Pylint's exit code is a bit-flag (8=refactor); R0801 fires exit 8 even at
    # 10/10 score.  The score-pattern check matches the established policy.
    pylint_cmd = (
        "pylint aletheia/ tests/ > /tmp/aletheia-pylint.out 2>&1; "
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

    # clang-format: exclude generated / third-party trees.
    clang_format_cmd = (
        "find . \\( -path ./build -o -path ./build-tidy -o -path ./_deps "
        "-o -path './*/_deps' \\) -prune -o "
        "\\( -name '*.cpp' -o -name '*.hpp' \\) -print | "
        "xargs clang-format --dry-run --Werror"
    )
    r.step(
        "clang-format",
        clang_format_cmd,
        cwd=r.repo_root / "cpp",
        shell=True,
    )

    # clang-tidy: AGENTS.md L580 canonical scope (src/*.cpp).
    r.step(
        "clang-tidy",
        "clang-tidy -p build src/*.cpp",
        cwd=r.repo_root / "cpp",
        shell=True,
    )

    # ─── Steps 20-22: GHA meta-checks ──────────────────────────────────────

    if shutil.which("actionlint"):
        if (r.repo_root / ".github" / "workflows").is_dir():
            r.step("actionlint", ["actionlint", "-color"])
        else:
            r.announce_skip(
                "actionlint", "no .github/workflows/ directory"
            )
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

    # ─── Step 23 (opt-in): reproducible-build gate ─────────────────────────
    if os.environ.get("ALETHEIA_REPRO_CHECK") == "1":
        r.total_steps = 23
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
            "set ALETHEIA_REPRO_CHECK=1 to enable",
        )

    return r.finalize()


if __name__ == "__main__":
    sys.exit(main())
