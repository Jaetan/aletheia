#!/usr/bin/env python3
"""Dynamic stability-bench runner (R18 cluster 6).

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
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
ARTIFACT_BASE = REPO_ROOT / "benchmarks" / "stability"


@dataclass
class Run:
    binding: str
    artifact_path: Path
    passed: bool
    error: str | None = None


def short_sha() -> str:
    out = subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return out.stdout.strip()


def find_lib() -> Path:
    p = REPO_ROOT / "build" / "libaletheia-ffi.so"
    if not p.is_file():
        raise SystemExit(
            f"libaletheia-ffi.so not found at {p}; run `cabal run shake -- build` first"
        )
    return p


def run_python(artifact_dir: Path, env: dict[str, str]) -> Run:
    """Run the Python stability harness.  Optionally enables -hT RTS profiling
    via the env passed in, in which case the runner expects ``aletheia.hp``
    in cwd and renames it to ``aletheia-ffi.hp`` in the artifact dir.
    """
    venv_python = REPO_ROOT / "python" / ".venv" / "bin" / "python3"
    python_exe = str(venv_python) if venv_python.is_file() else sys.executable
    cmd = [python_exe, "-m", "benchmarks.stability"]
    out_path = artifact_dir / "python.json"
    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT / "python",
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    out_path.write_text(proc.stdout if proc.stdout else "{}\n")
    if proc.returncode == 1:
        # Stability harness exited 1 = drift gate failure (verdict in JSON).
        try:
            report = json.loads(proc.stdout)
            passed = bool(report.get("passed", False))
        except json.JSONDecodeError:
            return Run("python", out_path, False, "Python harness emitted invalid JSON")
        return Run("python", out_path, passed)
    if proc.returncode != 0:
        return Run(
            "python",
            out_path,
            False,
            f"Python harness exited {proc.returncode}: {proc.stderr.strip()[:300]}",
        )
    # Successful exit; report MUST exist and pass.
    try:
        report = json.loads(proc.stdout)
        passed = bool(report.get("passed", False))
    except json.JSONDecodeError:
        return Run("python", out_path, False, "Python harness emitted invalid JSON")
    return Run("python", out_path, passed)


def run_go(artifact_dir: Path, env: dict[str, str]) -> Run:
    cmd = ["go", "run", "./benchmarks/stability/"]
    out_path = artifact_dir / "go.json"
    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT / "go",
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    out_path.write_text(proc.stdout if proc.stdout else "{}\n")
    if proc.returncode in (0, 1):
        try:
            report = json.loads(proc.stdout)
            return Run("go", out_path, bool(report.get("passed", False)))
        except json.JSONDecodeError:
            return Run("go", out_path, False, "Go harness emitted invalid JSON")
    return Run(
        "go", out_path, False, f"Go harness exited {proc.returncode}: {proc.stderr.strip()[:300]}"
    )


def run_cpp(artifact_dir: Path, env: dict[str, str]) -> Run:
    binary = REPO_ROOT / "cpp" / "build" / "stability_bench"
    if not binary.is_file():
        return Run(
            "cpp",
            artifact_dir / "cpp.json",
            False,
            f"{binary} not built; run `cmake --build cpp/build --target stability_bench`",
        )
    out_path = artifact_dir / "cpp.json"
    proc = subprocess.run(
        [str(binary)],
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    out_path.write_text(proc.stdout if proc.stdout else "{}\n")
    if proc.returncode in (0, 1):
        try:
            report = json.loads(proc.stdout)
            return Run("cpp", out_path, bool(report.get("passed", False)))
        except json.JSONDecodeError:
            return Run("cpp", out_path, False, "C++ harness emitted invalid JSON")
    return Run(
        "cpp", out_path, False, f"C++ harness exited {proc.returncode}: {proc.stderr.strip()[:300]}"
    )


def main() -> int:
    sha = short_sha()
    artifact_dir = ARTIFACT_BASE / sha
    if artifact_dir.exists():
        # Avoid stale-merge across re-runs of the same commit.
        shutil.rmtree(artifact_dir)
    artifact_dir.mkdir(parents=True)

    lib = find_lib()
    base_env = dict(os.environ)
    base_env["ALETHEIA_LIB"] = str(lib)

    # Python lane drives the GHC RTS heap profile (-hT).  Cwd = artifact_dir
    # so the .hp lands in the right place; we rename it to the cat 16 spec
    # filename after the run.
    py_env = dict(base_env)
    py_env["ALETHEIA_RTS_OPTS"] = "-hT"
    # The Python harness chdir's away from REPO_ROOT/python via cwd argument
    # below, so the .hp cwd is artifact_dir.
    # ↑ actually the harness is run with cwd=REPO_ROOT/python so the .hp lands
    #   there.  We want it in artifact_dir; tweak by tee'ing the cwd via env
    #   instead — simplest: run from artifact_dir and use PYTHONPATH.
    py_env["PYTHONPATH"] = str(REPO_ROOT / "python")

    # Override run_python's cwd by issuing the call inline here.
    venv_python = REPO_ROOT / "python" / ".venv" / "bin" / "python3"
    python_exe = str(venv_python) if venv_python.is_file() else sys.executable
    py_proc = subprocess.run(
        [python_exe, "-m", "benchmarks.stability"],
        cwd=artifact_dir,
        env=py_env,
        capture_output=True,
        text=True,
        check=False,
    )
    py_out = artifact_dir / "python.json"
    py_out.write_text(py_proc.stdout if py_proc.stdout else "{}\n")
    py_passed = False
    py_error: str | None = None
    if py_proc.returncode in (0, 1):
        try:
            py_passed = bool(json.loads(py_proc.stdout).get("passed", False))
        except json.JSONDecodeError:
            py_error = "Python harness emitted invalid JSON"
    else:
        py_error = f"Python harness exited {py_proc.returncode}: {py_proc.stderr.strip()[:300]}"
    runs: list[Run] = [Run("python", py_out, py_passed, py_error)]

    # Rename the GHC RTS heap profile to the cat 16 spec filename.  argv[0]
    # in _ffi.RTSState is set to b"aletheia" so the file lands as aletheia.hp.
    hp_emitted = artifact_dir / "aletheia.hp"
    hp_target = artifact_dir / "aletheia-ffi.hp"
    if hp_emitted.is_file():
        hp_emitted.rename(hp_target)

    # Go and C++ run sequentially, no -hT (the RTS init is process-once and
    # already happened in the Python lane; they only contribute their own
    # binding-level sub-checks).
    runs.append(run_go(artifact_dir, base_env))
    runs.append(run_cpp(artifact_dir, base_env))

    summary = {
        "commit": sha,
        "artifact_dir": str(artifact_dir.relative_to(REPO_ROOT)),
        "heap_profile": str(hp_target.relative_to(REPO_ROOT)) if hp_target.is_file() else None,
        "runs": [
            {
                "binding": r.binding,
                "artifact": str(r.artifact_path.relative_to(REPO_ROOT)),
                "passed": r.passed,
                "error": r.error,
            }
            for r in runs
        ],
        "passed": all(r.passed for r in runs) and hp_target.is_file(),
    }
    (artifact_dir / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n",
    )

    print(json.dumps(summary, indent=2))
    return 0 if summary["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
