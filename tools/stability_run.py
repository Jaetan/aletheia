#!/usr/bin/env python3
"""Dynamic stability-bench runner.

Invokes each binding's stability harness in turn (Python, Go, C++), captures
per-sub-check verdicts as JSON in ``benchmarks/stability/<commit>/<binding>.json``,
and additionally archives the GHC RTS heap profile (Agda cat 16 sub-check) by
running one harness with ``ALETHEIA_RTS_OPTS=-hT`` set so the RTS emits
``aletheia.hp``.

Exits non-zero if any binding's drift gate fails.

Per-binding env contract:

  - ALETHEIA_STABILITY_CYCLES   default 10
  - ALETHEIA_STABILITY_FRAMES   default 100_000
  - ALETHEIA_STABILITY_CHECK    set to anything truthy by run_ci.py to enable
                                this lane (run_ci.py only invokes us when the
                                env var is truthy, so this script does NOT
                                re-check it)

Artifacts written:

  benchmarks/stability/<short_sha>/
    python.json
    go.json
    cpp.json
    aletheia-ffi.hp      (renamed from aletheia.hp emitted by the GHC RTS in cwd)
    summary.json

The <short_sha> directory is read from `git rev-parse --short HEAD`, which
makes per-commit comparisons natural while keeping the local artifact tree
small.

Usage:
  ALETHEIA_STABILITY_CHECK=1 python3 tools/stability_run.py

The static counterpart is ``tools/check_stability_bench.py``, which gates on
each binding's harness *containing* the required sub-check markers per
``docs/STABILITY_BENCH.yaml``.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TypedDict, cast

from tools._common import (
    find_executable,
    prepare_artifact_dir,
    short_sha,
    write_and_report_summary,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
ARTIFACT_BASE = REPO_ROOT / "benchmarks" / "stability"

# A harness exits 0 (gate passed) or 1 (drift gate failed, verdict in JSON);
# any other code is an environment failure that did not produce a verdict.
_VERDICT_EXIT_CODES = (0, 1)
# Cap on harness stderr echoed into an error string, to keep summaries small.
_STDERR_SNIPPET_LEN = 300


class _HarnessReport(TypedDict, total=False):
    """The single field this runner reads from a harness's JSON verdict."""

    passed: bool


@dataclass
class Run:
    """Outcome of one binding's stability harness, archived into ``summary.json``."""

    binding: str
    artifact_path: Path
    passed: bool
    error: str | None = None


def find_lib() -> Path:
    """Return the path to the built FFI shared library, raising if it is absent."""
    lib_path = REPO_ROOT / "build" / "libaletheia-ffi.so"
    if not lib_path.is_file():
        message = (
            f"libaletheia-ffi.so not found at {lib_path}; run `cabal run shake -- build` first"
        )
        raise SystemExit(message)
    return lib_path


def _verdict_from_report(stdout: str) -> bool:
    """Return the harness's ``passed`` verdict from its JSON stdout (False if absent)."""
    report = cast("_HarnessReport", json.loads(stdout))
    return bool(report.get("passed", False))


def _finalize_lane(binding: str, proc: subprocess.CompletedProcess[str], out_path: Path) -> Run:
    """Archive a harness's stdout and turn its exit code into a :class:`Run`.

    Shared tail for every lane: writes the JSON verdict to ``out_path`` (or an
    empty object if the harness was silent), treats exit codes 0/1 as a verdict
    to parse, and any other code as an environment failure.
    """
    out_path.write_text(proc.stdout or "{}\n")
    if proc.returncode in _VERDICT_EXIT_CODES:
        try:
            passed = _verdict_from_report(proc.stdout)
        except json.JSONDecodeError:
            return Run(
                binding=binding,
                artifact_path=out_path,
                passed=False,
                error=f"{binding} harness emitted invalid JSON",
            )
        return Run(binding=binding, artifact_path=out_path, passed=passed)
    stderr_tail = proc.stderr.strip()[:_STDERR_SNIPPET_LEN]
    return Run(
        binding=binding,
        artifact_path=out_path,
        passed=False,
        error=f"{binding} harness exited {proc.returncode}: {stderr_tail}",
    )


def run_go(artifact_dir: Path, env: dict[str, str]) -> Run:
    """Run the Go stability harness and capture its verdict."""
    cmd = [find_executable("go"), "run", "./benchmarks/stability/"]
    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT / "go",
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    return _finalize_lane("go", proc, artifact_dir / "go.json")


def run_cpp(artifact_dir: Path, env: dict[str, str]) -> Run:
    """Run the C++ stability harness and capture its verdict."""
    out_path = artifact_dir / "cpp.json"
    binary = REPO_ROOT / "cpp" / "build" / "stability_bench"
    if not binary.is_file():
        return Run(
            binding="cpp",
            artifact_path=out_path,
            passed=False,
            error=f"{binary} not built; run `cmake --build cpp/build --target stability_bench`",
        )
    proc = subprocess.run(
        [str(binary)],
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    return _finalize_lane("cpp", proc, out_path)


def run_python_with_heap_profile(artifact_dir: Path, base_env: dict[str, str]) -> Run:
    """Run the Python harness from ``artifact_dir`` with ``-hT`` RTS profiling.

    The Python lane drives the GHC RTS heap profile.  Running with cwd set to
    ``artifact_dir`` lands the emitted ``aletheia.hp`` (named after the RTS
    ``argv[0]`` ``b"aletheia"``) directly in the artifact tree; ``PYTHONPATH``
    keeps the ``benchmarks`` package importable from that cwd.  The caller
    renames ``aletheia.hp`` to the cat 16 spec filename afterwards.
    """
    env = dict(base_env)
    env["ALETHEIA_RTS_OPTS"] = "-hT"
    env["PYTHONPATH"] = str(REPO_ROOT / "python")
    venv_python = REPO_ROOT / "python" / ".venv" / "bin" / "python3"
    python_exe = str(venv_python) if venv_python.is_file() else sys.executable
    proc = subprocess.run(
        [python_exe, "-m", "benchmarks.stability"],
        cwd=artifact_dir,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    return _finalize_lane("python", proc, artifact_dir / "python.json")


def _build_summary(
    sha: str,
    artifact_dir: Path,
    runs: list[Run],
    hp_target: Path,
) -> dict[str, object]:
    """Assemble the ``summary.json`` payload from the per-lane runs."""
    heap_present = hp_target.is_file()
    return {
        "commit": sha,
        "artifact_dir": str(artifact_dir.relative_to(REPO_ROOT)),
        "heap_profile": str(hp_target.relative_to(REPO_ROOT)) if heap_present else None,
        "runs": [
            {
                "binding": r.binding,
                "artifact": str(r.artifact_path.relative_to(REPO_ROOT)),
                "passed": r.passed,
                "error": r.error,
            }
            for r in runs
        ],
        "passed": all(r.passed for r in runs) and heap_present,
    }


def main() -> int:
    """Run every binding's stability harness, archive verdicts, gate on drift."""
    sha = short_sha(REPO_ROOT)
    artifact_dir = prepare_artifact_dir(ARTIFACT_BASE, sha)

    lib = find_lib()
    base_env = dict(os.environ)
    base_env["ALETHEIA_LIB"] = str(lib)

    runs: list[Run] = [run_python_with_heap_profile(artifact_dir, base_env)]

    # Rename the GHC RTS heap profile to the cat 16 spec filename.
    hp_emitted = artifact_dir / "aletheia.hp"
    hp_target = artifact_dir / "aletheia-ffi.hp"
    if hp_emitted.is_file():
        hp_emitted.rename(hp_target)

    # Go and C++ run sequentially, no -hT (the RTS init is process-once and
    # already happened in the Python lane; they only contribute their own
    # binding-level sub-checks).
    runs.append(run_go(artifact_dir, base_env))
    runs.append(run_cpp(artifact_dir, base_env))

    summary = _build_summary(sha, artifact_dir, runs, hp_target)
    return write_and_report_summary(artifact_dir, summary)


if __name__ == "__main__":
    sys.exit(main())
