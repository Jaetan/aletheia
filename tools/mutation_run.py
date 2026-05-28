#!/usr/bin/env python3
"""Dynamic mutation-testing runner.

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

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, NotRequired, TypedDict, cast

import yaml

from tools._common import (
    prepare_artifact_dir,
    run_capture,
    short_sha,
    write_and_report_summary,
)

if TYPE_CHECKING:
    from collections.abc import Callable

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"
ARTIFACT_BASE = REPO_ROOT / "benchmarks" / "mutation"

# Exit codes (mirrors the CHANGELOG / stability runners' convention).
SPEC_ERROR_EXIT = 2

# Last ``raw_log`` characters kept in the archived JSON (full log lands in the
# per-binding ``<binding>.raw.txt`` artifact alongside it).
RAW_LOG_TAIL_CHARS = 2000

# A mutation score of 100% leaves the killed-from-score formula undefined
# (division by ``100 - score``); the C++ parser special-cases it.
FULL_SCORE_PCT = 100


class Baseline(TypedDict):
    """The per-binding baseline block in ``docs/MUTATION_BENCH.yaml``."""

    survivors: NotRequired[int]
    total_mutants: NotRequired[int]
    score_pct: NotRequired[int]
    run_at: NotRequired[str]


class BindingSpec(TypedDict):
    """One binding's entry under the YAML ``bindings`` mapping."""

    tool: NotRequired[str]
    baseline: NotRequired[Baseline]


class Spec(TypedDict):
    """The top-level shape of ``docs/MUTATION_BENCH.yaml``."""

    bindings: NotRequired[dict[str, BindingSpec]]


class DriftEntry(TypedDict):
    """One binding's drift verdict, serialized into ``summary.json``."""

    status: str
    error: NotRequired[str]
    observed_survivors: NotRequired[int]
    baseline_survivors: NotRequired[int]
    delta: NotRequired[int]


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
            "raw_log_tail": self.raw_log[-RAW_LOG_TAIL_CHARS:],
            "error": self.error,
        }


@dataclass
class MutmutCounts:
    """Per-status mutant tallies parsed from ``mutmut`` output."""

    killed: int
    survived: int
    timeout: int
    skipped: int

    @property
    def total(self) -> int:
        """Sum across every parsed status section."""
        return self.killed + self.survived + self.timeout + self.skipped


def load_spec() -> Spec:
    """Load docs/MUTATION_BENCH.yaml (per-binding tool / hot_path / baseline)."""
    return cast("Spec", yaml.safe_load(SPEC_PATH.read_text()))


def _parse_mutmut(raw: str) -> MutmutCounts:
    """Tally per-status mutant counts from ``mutmut run`` / ``results`` output."""
    sections: dict[str, int] = {}
    # mutmut 3.x prints sections per status (killed/survived/timeout/...).
    # Each section header is e.g. "survived: N items" or with a colon-separated
    # newline-list following.  We count by scanning for section headers.
    section_re = re.compile(
        r"^(killed|survived|timeout|suspicious|skipped)\s*\(\s*(\d+)",
        re.MULTILINE,
    )
    for match in section_re.finditer(raw):
        sections[match.group(1)] = int(match.group(2))
    # Fallback parse: the older "X/Y mutants" line.
    if not sections:
        legacy = re.search(r"(\d+)\s*/\s*(\d+)\s*mutants?", raw)
        if legacy:
            killed = int(legacy.group(1))
            total = int(legacy.group(2))
            sections = {"killed": killed, "survived": total - killed}
    return MutmutCounts(
        killed=sections.get("killed", 0),
        survived=sections.get("survived", 0),
        timeout=sections.get("timeout", 0),
        skipped=sections.get("skipped", 0),
    )


def _check_python_tools() -> tuple[Path, Path] | str:
    """Return ``(mutmut_bin, lib)`` when the Python lane can run, else an error string."""
    venv_python = REPO_ROOT / "python" / ".venv" / "bin" / "python3"
    if not venv_python.is_file():
        return (
            "python/.venv not found; run `python3 -m venv python/.venv && "
            + "python/.venv/bin/pip install -e python/.[dev,mutation]`"
        )
    mutmut_bin = REPO_ROOT / "python" / ".venv" / "bin" / "mutmut"
    if not mutmut_bin.is_file():
        return (
            "mutmut not installed in venv; run " + "`python/.venv/bin/pip install 'mutmut>=3.5,<4'`"
        )
    lib = REPO_ROOT / "build" / "libaletheia-ffi.so"
    if not lib.is_file():
        return f"libaletheia-ffi.so not found at {lib}; run `cabal run shake -- build` first"
    return (mutmut_bin, lib)


def run_python(artifact_dir: Path) -> MutationReport:
    """Mutmut run on Python hot-path; parses ``mutmut results`` summary."""
    checked = _check_python_tools()
    if isinstance(checked, str):
        return MutationReport("python", "mutmut", 0, 0, "", error=checked)
    mutmut_bin, lib = checked
    cwd = REPO_ROOT / "python"
    # ALETHEIA_LIB is required because mutmut copies the source tree into
    # python/mutants/ and runs pytest from there; the FFI library auto-
    # discovery (`_ffi.find_ffi_library`) walks `Path(__file__).parent ↑↑↑`
    # which from `python/mutants/aletheia/client/_ffi.py` only reaches
    # `python/mutants/`, not the repo root where `build/` lives.  Setting
    # ALETHEIA_LIB short-circuits the lookup.
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(lib)
    # mutmut 3.x writes its mutation cache to .mutmut/ in cwd.  Run produces
    # the cache; results parses it.  Both write to stdout; we capture both.
    # These two calls carry a custom ``env`` (ALETHEIA_LIB), which the shared
    # ``run_capture`` helper does not thread through, so they go direct to
    # ``subprocess.run``; ``str(mutmut_bin)`` is an absolute path (no S607).
    run_proc = subprocess.run(
        [str(mutmut_bin), "run"], cwd=cwd, env=env, capture_output=True, text=True, check=False
    )
    raw = "=== mutmut run ===\n" + run_proc.stdout + run_proc.stderr + "\n"
    # Even on non-zero exit, mutants may have been generated; capture results.
    results_proc = subprocess.run(
        [str(mutmut_bin), "results"], cwd=cwd, env=env, capture_output=True, text=True, check=False
    )
    raw += "=== mutmut results ===\n" + results_proc.stdout + results_proc.stderr + "\n"
    (artifact_dir / "python.raw.txt").write_text(raw)

    counts = _parse_mutmut(raw)
    if counts.total == 0 and (run_proc.returncode != 0 or results_proc.returncode != 0):
        return MutationReport(
            "python",
            "mutmut",
            0,
            0,
            raw,
            error=(
                f"mutmut run/results failed: exit "
                f"{run_proc.returncode}/{results_proc.returncode} (see python.raw.txt)"
            ),
        )
    return MutationReport("python", "mutmut", counts.killed, counts.survived, raw)


def run_go(artifact_dir: Path) -> MutationReport:
    """Run gremlins on the Go aletheia/ package and parse its tail summary.

    Output is a text summary with ``Killed``, ``Lived`` (= survived),
    ``Not covered`` and ``Mutator coverage`` lines.

    AGENTS.md cat 14(g) names go-mutesting / gomut / mutate; ``gremlins``
    is the actively-maintained successor (zimmski's repo is unmaintained
    since 2021 and panics on Go 1.26 internals).  Same operator set, same
    intent, just a different implementation.
    """
    gremlins = shutil.which("gremlins")
    if gremlins is None:
        return MutationReport(
            "go",
            "gremlins",
            0,
            0,
            "",
            error="gremlins not in PATH; run "
            + "`go install github.com/go-gremlins/gremlins/cmd/gremlins@latest`",
        )

    cwd = REPO_ROOT / "go"
    # gremlins targets the package directory; runs the package's tests
    # against each mutant.  We pass the canonical aletheia/ subpackage
    # (the only Go module that holds runtime code; benchmarks and tests
    # are excluded automatically by virtue of *_test.go convention).
    proc = run_capture([gremlins, "unleash", "./aletheia"], cwd=cwd)
    raw = proc.stdout + "\n=== STDERR ===\n" + proc.stderr
    (artifact_dir / "go.raw.txt").write_text(raw)

    # gremlins tail summary lines (observed empirically):
    #   Killed: N, Lived: N, Not covered: N
    #   Timed out: N, Not viable: N, Skipped: N
    #   Test efficacy: P.PP%
    #   Mutator coverage: P.PP%
    killed_m = re.search(r"Killed:\s*(\d+)", raw)
    survived_m = re.search(r"Lived:\s*(\d+)", raw)
    if not (killed_m and survived_m):
        return MutationReport(
            "go",
            "gremlins",
            0,
            0,
            raw,
            error=(f"could not parse gremlins summary (see go.raw.txt; exit {proc.returncode})"),
        )
    # Note: gremlins' "Not covered" mutants are on lines without test
    # coverage; they don't contribute to the killed/lived split per
    # gremlins semantics, so total_mutants = killed + survived in the
    # MutationReport.
    return MutationReport("go", "gremlins", int(killed_m.group(1)), int(survived_m.group(1)), raw)


def _check_cpp_tools() -> tuple[str, str] | str:
    """Return ``(cmake, mull_runner)`` paths when C++ can run, else an error string."""
    cmake = shutil.which("cmake")
    if cmake is None:
        return "cmake not in PATH; install CMake 3.25+ to run the C++ mutation lane"
    mull_runner = shutil.which("mull-runner-19")
    if mull_runner is None:
        return (
            "mull-runner-19 not in PATH; install Mull-19 from "
            "https://github.com/mull-project/mull/releases (see "
            "docs/operations/MUTATION.md § Installation)"
        )
    if shutil.which("clang++-19") is None:
        return "clang++-19 not in PATH; install via apt: `sudo apt install clang-19`"
    plugin = Path.home() / ".local" / "bin" / "mull-ir-frontend-19"
    if not plugin.is_file():
        return (
            f"mull-ir-frontend-19 plugin not found at {plugin}; "
            "see docs/operations/MUTATION.md § Installation"
        )
    return (cmake, mull_runner)


def _killed_from_mull(raw: str, survived: int) -> int:
    """Derive the killed count from a Mull summary, falling back through its shapes."""
    killed_m = re.search(r"Killed[^:\n]*:\s*(\d+)", raw)
    if killed_m:
        return int(killed_m.group(1))
    score_m = re.search(r"Mutation score:\s*(\d+)\s*%", raw)
    if score_m:
        score_pct_in = int(score_m.group(1))
        if score_pct_in >= FULL_SCORE_PCT:
            return survived  # impossible to compute exactly; pick a reasonable proxy
        return round(survived * score_pct_in / (FULL_SCORE_PCT - score_pct_in))
    # Score not parsed either; fall back to "everything killed" guess.
    return 0


def _build_cpp_mutation_tree(
    cmake: str,
    cpp_root: Path,
    build_dir: Path,
    artifact_dir: Path,
) -> str | MutationReport:
    """Configure + build the mutation build tree, returning the raw log or a failure report."""
    cmake_proc = run_capture(
        [
            cmake,
            "-B",
            str(build_dir),
            "-DALETHEIA_MUTATION=ON",
            "-DCMAKE_C_COMPILER=clang-19",
            "-DCMAKE_CXX_COMPILER=clang++-19",
        ],
        cwd=cpp_root,
    )
    raw = "=== cmake configure ===\n" + cmake_proc.stdout + cmake_proc.stderr + "\n"
    if cmake_proc.returncode != 0:
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(
            "cpp",
            "mull",
            0,
            0,
            raw,
            error=f"cmake configure failed (exit {cmake_proc.returncode}; see cpp.raw.txt)",
        )

    build_proc = run_capture(
        [cmake, "--build", str(build_dir), "--target", "unit_tests"],
        cwd=cpp_root,
    )
    raw += "=== cmake build ===\n" + build_proc.stdout + build_proc.stderr + "\n"
    if build_proc.returncode != 0:
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(
            "cpp",
            "mull",
            0,
            0,
            raw,
            error=f"cmake build failed (exit {build_proc.returncode}; see cpp.raw.txt)",
        )
    return raw


def run_cpp(artifact_dir: Path) -> MutationReport:
    """Mull pass via dedicated build tree; runs unit_tests under mull-runner-19."""
    checked = _check_cpp_tools()
    if isinstance(checked, str):
        return MutationReport("cpp", "mull", 0, 0, "", error=checked)
    cmake, mull_runner = checked

    cpp_root = REPO_ROOT / "cpp"
    build_dir = cpp_root / "build-mutation"
    built = _build_cpp_mutation_tree(cmake, cpp_root, build_dir, artifact_dir)
    if isinstance(built, MutationReport):
        return built
    raw = built

    unit_tests = build_dir / "unit_tests"
    runner_proc = run_capture([mull_runner, str(unit_tests)], cwd=cpp_root)
    raw += "=== mull-runner-19 ===\n" + runner_proc.stdout + runner_proc.stderr + "\n"
    (artifact_dir / "cpp.raw.txt").write_text(raw)

    # Mull-19 tail summary lines (the actual format observed empirically):
    #   [info] Mutation score: 56%
    #   [info] Surviving mutants: 17
    #   [info] Total execution time: 273ms
    # Older / other Mull versions also emit "Killed: N" / "Skipped: N";
    # try both shapes.  When only score+survived are present, compute killed
    # from killed = round(survived * score_pct / (100 - score_pct)).
    survived_m = re.search(r"Surviving mutants:\s*(\d+)", raw) or re.search(
        r"Survived[^:\n]*:\s*(\d+)", raw
    )
    if not survived_m:
        return MutationReport(
            "cpp",
            "mull",
            0,
            0,
            raw,
            error=(
                "could not parse mull-runner-19 summary "
                f"(see cpp.raw.txt; exit {runner_proc.returncode})"
            ),
        )
    survived = int(survived_m.group(1))
    return MutationReport("cpp", "mull", _killed_from_mull(raw, survived), survived, raw)


# (skip-env-var, runner) per binding, in the order reports are produced.
RUNNERS: list[tuple[str, Callable[[Path], MutationReport]]] = [
    ("ALETHEIA_MUTATION_SKIP_PYTHON", run_python),
    ("ALETHEIA_MUTATION_SKIP_GO", run_go),
    ("ALETHEIA_MUTATION_SKIP_CPP", run_cpp),
]


def _run_enabled_bindings(artifact_dir: Path) -> list[MutationReport]:
    """Run each non-skipped binding, archive its JSON, and collect the reports."""
    reports: list[MutationReport] = []
    for skip_var, runner in RUNNERS:
        if os.environ.get(skip_var) == "1":
            continue
        rep = runner(artifact_dir)
        (artifact_dir / f"{rep.binding}.json").write_text(json.dumps(rep.to_dict(), indent=2))
        reports.append(rep)
    return reports


def _drift_for(rep: MutationReport, bindings: dict[str, BindingSpec]) -> DriftEntry:
    """Compute one binding's drift verdict against its YAML baseline."""
    if rep.error:
        return {"status": "error", "error": rep.error}
    baseline = bindings.get(rep.binding, {}).get("baseline", {}).get("survivors")
    if baseline is None:
        return {"status": "first_run", "observed_survivors": rep.survived}
    if rep.survived > baseline:
        return {
            "status": "regression",
            "observed_survivors": rep.survived,
            "baseline_survivors": baseline,
            "delta": rep.survived - baseline,
        }
    return {
        "status": "ok",
        "observed_survivors": rep.survived,
        "baseline_survivors": baseline,
    }


def main() -> int:
    """Drive every binding's mutation tool, archive reports, gate on baseline drift."""
    if not SPEC_PATH.is_file():
        _ = sys.stderr.write(f"ERROR: spec missing at {SPEC_PATH}\n")
        return SPEC_ERROR_EXIT

    spec = load_spec()
    bindings = spec.get("bindings", {})
    if not bindings:
        _ = sys.stderr.write("ERROR: no bindings in spec\n")
        return SPEC_ERROR_EXIT

    sha = short_sha(REPO_ROOT)
    artifact_dir = prepare_artifact_dir(ARTIFACT_BASE, sha)

    reports = _run_enabled_bindings(artifact_dir)

    # Drift gate: compare each binding's survived count to the baseline in
    # the YAML spec.  null baseline = first run, no gating yet.  Otherwise,
    # observed > baseline = lane fails.
    drift: dict[str, DriftEntry] = {}
    for rep in reports:
        drift[rep.binding] = _drift_for(rep, bindings)
    any_drift = any(entry["status"] in ("error", "regression") for entry in drift.values())

    summary = {
        "commit": sha,
        "artifact_dir": str(artifact_dir.relative_to(REPO_ROOT)),
        "runs": [r.to_dict() for r in reports],
        "drift": drift,
        "passed": not any_drift,
    }
    return write_and_report_summary(artifact_dir, summary)


if __name__ == "__main__":
    sys.exit(main())
