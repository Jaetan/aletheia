#!/usr/bin/env python3
"""Dynamic mutation-testing runner (R18 cluster 7).

Drives each binding's mutation tool in turn (mutmut for Python, go-mutesting
for Go, Mull for C++), parses tool-specific output into a normalized
``MutationReport`` shape, and archives per-binding JSON to
``benchmarks/mutation/<short_sha>/``.

Drift gate: each binding's report is compared against the baseline survivor
count recorded in ``docs/MUTATION_BENCH.yaml``.  ``observed > baseline + 0``
fails the lane (allow exact equality only — any new survivor is a finding
per AGENTS.md cat 14(g) "an unjustified survivor is a test gap").

Per-binding env contract:

  - ALETHEIA_MUTATION_CHECK    set to anything truthy by run_ci.py to enable
                               this lane (run_ci.py only invokes us when the
                               env var or `--mutation` flag is set; this
                               script does NOT re-check the env var).

Optional per-binding skip (useful for partial runs in CI lanes):

  - ALETHEIA_MUTATION_SKIP_PYTHON=1
  - ALETHEIA_MUTATION_SKIP_GO=1
  - ALETHEIA_MUTATION_SKIP_CPP=1

Artifacts written:

  benchmarks/mutation/<short_sha>/
    python.json    {tool, total_mutants, killed, survived, score_pct, raw_log}
    go.json        same shape
    cpp.json       same shape
    summary.json   {commit, runs: [...], passed: bool, baseline_drift: {...}}

Usage:
  ALETHEIA_MUTATION_CHECK=1 python3 tools/mutation_run.py

The static counterpart is ``tools/check_mutation_setup.py``, which gates on
each binding's hot-path source files existing per ``docs/MUTATION_BENCH.yaml``.
"""
# pylint: disable=too-many-locals,too-many-branches,too-many-statements

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"
ARTIFACT_BASE = REPO_ROOT / "benchmarks" / "mutation"


@dataclass
class MutationReport:
    """Per-binding mutation result; serialized to ``<binding>.json``."""

    binding: str
    tool: str
    killed: int
    survived: int
    raw_log: str
    error: str | None = None

    @property
    def total_mutants(self) -> int:
        """Killed + survived (excludes not-covered / skipped per tool semantics)."""
        return self.killed + self.survived

    @property
    def score_pct(self) -> float:
        """Mutation score: killed / (killed + survived) * 100, or 0 if total is 0."""
        total = self.killed + self.survived
        return 100.0 * self.killed / total if total > 0 else 0.0

    def to_dict(self) -> dict[str, object]:
        """Materialize for JSON archival; truncates raw_log to last 2000 chars."""
        return {
            "binding": self.binding,
            "tool": self.tool,
            "total_mutants": self.total_mutants,
            "killed": self.killed,
            "survived": self.survived,
            "score_pct": self.score_pct,
            "raw_log_tail": self.raw_log[-2000:],
            "error": self.error,
        }


def short_sha() -> str:
    """Return the current commit's short sha for artifact-dir naming."""
    out = subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
    )
    return out.stdout.strip()


def load_spec() -> dict[str, object]:
    """Load docs/MUTATION_BENCH.yaml as a dict (per-binding tool / hot_path / baseline)."""
    return yaml.safe_load(SPEC_PATH.read_text())


def run_python(artifact_dir: Path) -> MutationReport:
    """mutmut run on Python hot-path; parses ``mutmut results`` summary."""
    venv_python = REPO_ROOT / "python" / ".venv" / "bin" / "python3"
    if not venv_python.is_file():
        return MutationReport(
            "python", "mutmut", 0, 0, "",
            error=(
                "python/.venv not found; run `python3 -m venv python/.venv && "
                "python/.venv/bin/pip install -e python/.[dev,mutation]`"
            )
        )
    mutmut_bin = REPO_ROOT / "python" / ".venv" / "bin" / "mutmut"
    if not mutmut_bin.is_file():
        return MutationReport(
            "python", "mutmut", 0, 0, "",
            error="mutmut not installed in venv; run "
                  "`python/.venv/bin/pip install 'mutmut>=3.5,<4'`"
        )
    lib = REPO_ROOT / "build" / "libaletheia-ffi.so"
    if not lib.is_file():
        return MutationReport(
            "python", "mutmut", 0, 0, "",
            error=f"libaletheia-ffi.so not found at {lib}; "
                  "run `cabal run shake -- build` first"
        )
    cwd = REPO_ROOT / "python"
    # ALETHEIA_LIB is required because mutmut copies the source tree into
    # python/mutants/ and runs pytest from there; the FFI library auto-
    # discovery (`_ffi.find_ffi_library`) walks `Path(__file__).parent ↑↑↑`
    # which from `python/mutants/aletheia/client/_ffi.py` only reaches
    # `python/mutants/`, not the repo root where `build/` lives.  Setting
    # ALETHEIA_LIB short-circuits the lookup.
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(lib)
    raw = ""
    # mutmut 3.x writes its mutation cache to .mutmut/ in cwd.  Run produces
    # the cache; results parses it.  Both write to stdout; we capture both.
    run_proc = subprocess.run(
        [str(mutmut_bin), "run"], cwd=cwd, env=env,
        capture_output=True, text=True, check=False,
    )
    raw += "=== mutmut run ===\n" + run_proc.stdout + run_proc.stderr + "\n"
    # Even on non-zero exit, mutants may have been generated; capture results.
    results_proc = subprocess.run(
        [str(mutmut_bin), "results"], cwd=cwd, env=env,
        capture_output=True, text=True, check=False,
    )
    raw += "=== mutmut results ===\n" + results_proc.stdout + results_proc.stderr + "\n"
    out_path = artifact_dir / "python.raw.txt"
    out_path.write_text(raw)

    # Parse: mutmut 3.x prints sections per status (killed/survived/timeout/...)
    # Each section header is e.g. "survived: N items" or with a colon-separated
    # newline-list following.  We count by scanning for section headers.
    sections: dict[str, int] = {}
    section_re = re.compile(
        r"^(killed|survived|timeout|suspicious|skipped)\s*\(\s*(\d+)",
        re.MULTILINE,
    )
    for m in section_re.finditer(raw):
        sections[m.group(1)] = int(m.group(2))
    # Fallback parse: the older "X/Y mutants" line.
    if not sections:
        m = re.search(r"(\d+)\s*/\s*(\d+)\s*mutants?", raw)
        if m:
            killed = int(m.group(1))
            total = int(m.group(2))
            sections = {"killed": killed, "survived": total - killed}

    killed = sections.get("killed", 0)
    survived = sections.get("survived", 0)
    timeout = sections.get("timeout", 0)
    skipped = sections.get("skipped", 0)
    total = killed + survived + timeout + skipped

    if total == 0 and (run_proc.returncode != 0 or results_proc.returncode != 0):
        run_rc = run_proc.returncode
        res_rc = results_proc.returncode
        return MutationReport(
            "python", "mutmut", 0, 0, raw,
            error=(
                f"mutmut run/results failed: exit {run_rc}/{res_rc} "
                "(see python.raw.txt)"
            )
        )

    return MutationReport("python", "mutmut", killed, survived, raw)


def run_go(artifact_dir: Path) -> MutationReport:
    """gremlins unleash on the Go aletheia/ package.  Output: text summary
    with `Killed`, `Lived` (= survived), `Not covered`, `Mutator coverage` lines.

    AGENTS.md cat 14(g) names go-mutesting / gomut / mutate; `gremlins`
    is the actively-maintained successor (zimmski's repo is unmaintained
    since 2021 and panics on Go 1.26 internals).  Same operator set, same
    intent, just a different implementation.
    """
    if not shutil.which("gremlins"):
        return MutationReport(
            "go", "gremlins", 0, 0, "",
            error="gremlins not in PATH; run "
                  "`go install github.com/go-gremlins/gremlins/cmd/gremlins@latest`"
        )

    cwd = REPO_ROOT / "go"
    # gremlins targets the package directory; runs the package's tests
    # against each mutant.  We pass the canonical aletheia/ subpackage
    # (the only Go module that holds runtime code; benchmarks and tests
    # are excluded automatically by virtue of *_test.go convention).
    cmd = ["gremlins", "unleash", "./aletheia"]
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    raw = proc.stdout + "\n=== STDERR ===\n" + proc.stderr
    out_path = artifact_dir / "go.raw.txt"
    out_path.write_text(raw)

    # gremlins tail summary lines (observed empirically):
    #   Killed: N, Lived: N, Not covered: N
    #   Timed out: N, Not viable: N, Skipped: N
    #   Test efficacy: P.PP%
    #   Mutator coverage: P.PP%
    killed_m = re.search(r"Killed:\s*(\d+)", raw)
    survived_m = re.search(r"Lived:\s*(\d+)", raw)
    if not (killed_m and survived_m):
        return MutationReport(
            "go", "gremlins", 0, 0, raw,
            error=(
                "could not parse gremlins summary "
                f"(see go.raw.txt; exit {proc.returncode})"
            )
        )
    killed = int(killed_m.group(1))
    survived = int(survived_m.group(1))
    # Note: gremlins' "Not covered" mutants are on lines without test
    # coverage; they don't contribute to the killed/lived split per
    # gremlins semantics, so total_mutants = killed + survived in the
    # MutationReport.
    return MutationReport("go", "gremlins", killed, survived, raw)


def _check_cpp_tools() -> str | None:
    """Return error string if any C++ mutation prereq is missing, else None."""
    if not shutil.which("mull-runner-19"):
        return ("mull-runner-19 not in PATH; install Mull-19 from "
                "https://github.com/mull-project/mull/releases (see "
                "docs/operations/MUTATION.md § Installation)")
    if not shutil.which("clang++-19"):
        return "clang++-19 not in PATH; install via apt: `sudo apt install clang-19`"
    plugin = Path.home() / ".local" / "bin" / "mull-ir-frontend-19"
    if not plugin.is_file():
        return (f"mull-ir-frontend-19 plugin not found at {plugin}; "
                "see docs/operations/MUTATION.md § Installation")
    return None


def run_cpp(artifact_dir: Path) -> MutationReport:
    """Mull pass via dedicated build tree; runs unit_tests under mull-runner-19."""
    err = _check_cpp_tools()
    if err is not None:
        return MutationReport("cpp", "mull", 0, 0, "", error=err)

    cpp_root = REPO_ROOT / "cpp"
    build_dir = cpp_root / "build-mutation"
    cmake_proc = subprocess.run(
        [
            "cmake", "-B", str(build_dir), "-DALETHEIA_MUTATION=ON",
            "-DCMAKE_C_COMPILER=clang-19", "-DCMAKE_CXX_COMPILER=clang++-19",
        ],
        cwd=cpp_root, capture_output=True, text=True, check=False,
    )
    raw = "=== cmake configure ===\n" + cmake_proc.stdout + cmake_proc.stderr + "\n"
    if cmake_proc.returncode != 0:
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(
            "cpp", "mull", 0, 0, raw,
            error=f"cmake configure failed (exit {cmake_proc.returncode}; see cpp.raw.txt)"
        )

    build_proc = subprocess.run(
        ["cmake", "--build", str(build_dir), "--target", "unit_tests"],
        cwd=cpp_root, capture_output=True, text=True, check=False,
    )
    raw += "=== cmake build ===\n" + build_proc.stdout + build_proc.stderr + "\n"
    if build_proc.returncode != 0:
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(
            "cpp", "mull", 0, 0, raw,
            error=f"cmake build failed (exit {build_proc.returncode}; see cpp.raw.txt)"
        )

    unit_tests = build_dir / "unit_tests"
    runner_proc = subprocess.run(
        ["mull-runner-19", str(unit_tests)],
        cwd=cpp_root, capture_output=True, text=True, check=False,
    )
    raw += "=== mull-runner-19 ===\n" + runner_proc.stdout + runner_proc.stderr + "\n"
    out_path = artifact_dir / "cpp.raw.txt"
    out_path.write_text(raw)

    # Mull-19 tail summary lines (the actual format observed empirically):
    #   [info] Mutation score: 56%
    #   [info] Surviving mutants: 17
    #   [info] Total execution time: 273ms
    # Older / other Mull versions also emit "Killed: N" / "Skipped: N";
    # try both shapes.  When only score+survived are present, compute killed
    # from killed = round(survived * score_pct / (100 - score_pct)).
    survived_m = re.search(r"Surviving mutants:\s*(\d+)", raw) or \
                 re.search(r"Survived[^:\n]*:\s*(\d+)", raw)
    killed_m = re.search(r"Killed[^:\n]*:\s*(\d+)", raw)
    score_m = re.search(r"Mutation score:\s*(\d+)\s*%", raw)

    if not survived_m:
        return MutationReport(
            "cpp", "mull", 0, 0, raw,
            error=(
                "could not parse mull-runner-19 summary "
                f"(see cpp.raw.txt; exit {runner_proc.returncode})"
            )
        )
    survived = int(survived_m.group(1))
    if killed_m:
        killed = int(killed_m.group(1))
    elif score_m:
        score_pct_in = int(score_m.group(1))
        if score_pct_in >= 100:
            killed = survived  # impossible to compute exactly; pick a reasonable proxy
        else:
            killed = round(survived * score_pct_in / (100 - score_pct_in))
    else:
        # Score not parsed either; fall back to "everything killed" guess.
        killed = 0
    return MutationReport("cpp", "mull", killed, survived, raw)


def main() -> int:
    """Drive every binding's mutation tool, archive reports, gate on baseline drift."""
    if not SPEC_PATH.is_file():
        print(f"ERROR: spec missing at {SPEC_PATH}", file=sys.stderr)
        return 2

    spec = load_spec()
    bindings = spec.get("bindings", {}) if isinstance(spec, dict) else {}
    if not bindings:
        print("ERROR: no bindings in spec", file=sys.stderr)
        return 2

    sha = short_sha()
    artifact_dir = ARTIFACT_BASE / sha
    if artifact_dir.exists():
        shutil.rmtree(artifact_dir)
    artifact_dir.mkdir(parents=True)

    reports: list[MutationReport] = []

    if os.environ.get("ALETHEIA_MUTATION_SKIP_PYTHON") != "1":
        rep = run_python(artifact_dir)
        (artifact_dir / "python.json").write_text(json.dumps(rep.to_dict(), indent=2))
        reports.append(rep)

    if os.environ.get("ALETHEIA_MUTATION_SKIP_GO") != "1":
        rep = run_go(artifact_dir)
        (artifact_dir / "go.json").write_text(json.dumps(rep.to_dict(), indent=2))
        reports.append(rep)

    if os.environ.get("ALETHEIA_MUTATION_SKIP_CPP") != "1":
        rep = run_cpp(artifact_dir)
        (artifact_dir / "cpp.json").write_text(json.dumps(rep.to_dict(), indent=2))
        reports.append(rep)

    # Drift gate: compare each binding's survived count to the baseline in
    # the YAML spec.  null baseline = first run, no gating yet.  Otherwise,
    # observed > baseline = lane fails.
    drift: dict[str, dict[str, object]] = {}
    any_drift = False
    for rep in reports:
        if rep.error:
            drift[rep.binding] = {"status": "error", "error": rep.error}
            any_drift = True
            continue
        baseline = bindings.get(rep.binding, {}).get("baseline", {}).get("survivors")
        if baseline is None:
            drift[rep.binding] = {
                "status": "first_run",
                "observed_survivors": rep.survived,
            }
            continue
        if rep.survived > baseline:
            drift[rep.binding] = {
                "status": "regression",
                "observed_survivors": rep.survived,
                "baseline_survivors": baseline,
                "delta": rep.survived - baseline,
            }
            any_drift = True
        else:
            drift[rep.binding] = {
                "status": "ok",
                "observed_survivors": rep.survived,
                "baseline_survivors": baseline,
            }

    summary = {
        "commit": sha,
        "artifact_dir": str(artifact_dir.relative_to(REPO_ROOT)),
        "runs": [r.to_dict() for r in reports],
        "drift": drift,
        "passed": not any_drift,
    }
    (artifact_dir / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n",
    )

    print(json.dumps(summary, indent=2))
    return 0 if summary["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
