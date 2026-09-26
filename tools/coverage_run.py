# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The coverage lane: every binding's suite measured by its own tool, held to floors.

AGENTS.md § Universal Rules asks of each API binding that its suite cover at
least 80 percent of its lines and 60 percent of its branches, measured by the
binding's own coverage tool, beside the mutation lane over the same code.
This runner is that measurement.  For each binding it runs the suite under
the tool, reads the tool's own report into one shape, archives it under
``benchmarks/coverage/<short_sha>/``, and refuses a figure under the floor
``docs/COVERAGE_BENCH.yaml`` records.

Two figures per binding.  The first is lines everywhere.  The second is the
finest unit the tool itself counts short of a line: coverage.py's branch arcs
for Python, llvm-cov's branches for C++, the profile's blocks for Go (its
tool has no branch metric, and a block is the body of one arm), and llvm-cov's
regions for Rust (its branch instrumentation is nightly-only).  The record
names each binding's second figure, so a reader never mistakes one for a
branch count it is not.

The floors are the gate.  A recorded figure is what the last recorded run
produced, kept so a run reports its distance from it; a run under the
recorded figure but over the floor passes, and the record is re-taken when a
change moves it.  A run under a floor fails, as does a tool that will not
run, a report the runner cannot read, and a total of zero, which is a
measurement of nothing.

Per-binding env contract:

  - ALETHEIA_LIB is set by this runner to the built kernel for every suite,
    so the Go, C++ and Rust suites resolve it the way the always-on steps do.
  - ALETHEIA_COVERAGE_NO_DIFF_SCOPE=1 runs every binding whatever the diff.

Diff scoping: on a pull request only the bindings whose directory the diff
vs ``main`` touches are measured, the same decision the mutation lane takes
and read from the same function, with this lane's own tables.  A shared path
(the kernel's sources, the build, this runner, the record) measures all four.

Usage:
  python -m tools.coverage_run                      # every binding in scope
  python -m tools.coverage_run --binding go         # one binding
  python -m tools.coverage_run --scope              # LANE_MEASURES=1|0, no run

Exit 0 when every measured binding is over its floors, 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, cast

import yaml

from tools._common import (
    emit,
    find_executable,
    prepare_artifact_dir,
    run_capture,
    run_streaming,
    short_sha,
    write_workflow_line,
)
from tools.mutation_run import KERNEL_PATHS, bindings_in_scope

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "COVERAGE_BENCH.yaml"
ARTIFACT_BASE = REPO_ROOT / "benchmarks" / "coverage"
FFI_LIB = REPO_ROOT / "build" / "libaletheia-ffi.so"
VENV_PYTHON = REPO_ROOT / "python" / ".venv" / "bin" / "python"
CPP_BUILD_DIR = REPO_ROOT / "cpp" / "build-coverage"

SPEC_ERROR_EXIT = 2

# The variable the workflow's toolchain steps read, written by ``--scope``.
# Their condition is `!= '0'`, never `== '1'`: an answer that did not arrive
# must install.
MEASURES_VAR = "LANE_MEASURES"

# This lane's scope tables.  A binding's figure moves when its sources or its
# tests move, so the whole directory is the prefix, as the mutation lane's is.
_BINDING_DIRS: dict[str, str] = {
    "python": "python/",
    "go": "go/",
    "cpp": "cpp/",
    "rust": "rust/",
}
# A change here can move every binding's figure: the kernel every suite loads,
# the build that makes it, this runner, and the record it reads.
_GLOBAL_COVERAGE_PATHS: tuple[str, ...] = (
    *KERNEL_PATHS,
    "tools/coverage_run.py",
    "tools/mutation_run.py",  # the scope function this lane reads
    "tools/_common.py",
    "docs/COVERAGE_BENCH.yaml",
    ".github/workflows/pr-build-lanes.yml",
)
_NO_DIFF_SCOPE_ENV = "ALETHEIA_COVERAGE_NO_DIFF_SCOPE"

# What the C++ export leaves out: the suites, the harnesses, the fuzz targets
# and the fetched libraries, whose headers compile into every unit.
_CPP_IGNORE_REGEX = r"/(tests|benchmarks|fuzz|_deps)/"
# The Go packages the figure leaves out: the benchmark harness is not the
# binding.
_GO_HARNESS_PREFIX = "go/benchmarks/"

type Spec = dict[str, object]


@dataclass(frozen=True)
class Figure:
    """One coverage figure: the unit counted, how many were hit, how many there are."""

    unit: str
    covered: int
    total: int

    @property
    def pct(self) -> float:
        """The percentage, exact from the counts; zero of nothing is zero."""
        return 100.0 * self.covered / self.total if self.total else 0.0

    def to_dict(self) -> dict[str, object]:
        """Render the figure as the archived report carries it."""
        return {
            "unit": self.unit,
            "covered": self.covered,
            "total": self.total,
            "pct": round(self.pct, 2),
        }


@dataclass
class CoverageReport:
    """One binding's measurement, in the shape every binding's tool is read into."""

    binding: str
    tool: str
    lines: Figure | None = None
    second: Figure | None = None
    per_file: dict[str, dict[str, float]] = field(default_factory=dict)
    error: str | None = None
    elapsed_s: float = 0.0

    def to_dict(self) -> dict[str, object]:
        """Render the report as archived under the run's directory."""
        return {
            "binding": self.binding,
            "tool": self.tool,
            "lines": self.lines.to_dict() if self.lines else None,
            "second": self.second.to_dict() if self.second else None,
            "per_file": self.per_file,
            "error": self.error,
            "elapsed_s": round(self.elapsed_s, 1),
        }


def _suite_env() -> dict[str, str]:
    """Build the environment every suite runs under: the built kernel, named."""
    return {**os.environ, "ALETHEIA_LIB": str(FFI_LIB)}


def _rel(path: str) -> str:
    """Turn a tool's absolute path into the repository-relative one the record names."""
    root = str(REPO_ROOT) + "/"
    return path.removeprefix(root)


def _run(cmd: list[str], *, cwd: Path, label: str, env: dict[str, str] | None = None) -> str | None:
    """Run one command of a measurement, streaming its output; the error text on failure."""
    emit(f"[coverage] {label}: {' '.join(cmd)}")
    result = run_streaming(cmd, cwd=cwd, env=env or _suite_env())
    if result.returncode != 0:
        return f"{label} exited {result.returncode}"
    return None


# ── Python: coverage.py through pytest-cov ───────────────────────────────────


def parse_python_report(
    report: Mapping[str, object],
) -> tuple[Figure, Figure, dict[str, dict[str, float]]]:
    """Read coverage.py's JSON report: statements and branch arcs, whole and per file."""
    totals = cast("Mapping[str, int]", report["totals"])
    lines = Figure("lines", totals["covered_lines"], totals["num_statements"])
    branches = Figure("branches", totals["covered_branches"], totals["num_branches"])
    per_file: dict[str, dict[str, float]] = {}
    for name, entry in cast("Mapping[str, Mapping[str, object]]", report["files"]).items():
        summary = cast("Mapping[str, int]", entry["summary"])
        per_file["python/" + name] = {
            "lines_pct": round(
                100.0 * summary["covered_lines"] / max(summary["num_statements"], 1), 2
            ),
            "branches_pct": round(
                100.0 * summary["covered_branches"] / max(summary["num_branches"], 1), 2
            ),
        }
    return lines, branches, per_file


def run_python(artifact_dir: Path) -> CoverageReport:
    """Run the Python suite under coverage.py and read its JSON report."""
    rep = CoverageReport(binding="python", tool="coverage.py (pytest-cov)")
    if not VENV_PYTHON.is_file():
        rep.error = f"venv python missing at {VENV_PYTHON}"
        return rep
    out = artifact_dir / "python-coverage.json"
    # The cross-CLI parity harness needs the C++ CLI binary, so it is left out
    # here as it is in every python-lane pytest step.
    cmd = [
        str(VENV_PYTHON),
        "-m",
        "pytest",
        "tests/",
        "--ignore=tests/test_cli_parity.py",
        "-q",
        "-p",
        "no:cacheprovider",
        "--cov=aletheia",
        "--cov-branch",
        f"--cov-report=json:{out}",
    ]
    rep.error = _run(cmd, cwd=REPO_ROOT / "python", label="coverage python")
    if rep.error is None:
        report = cast("Mapping[str, object]", json.loads(out.read_text(encoding="utf-8")))
        rep.lines, rep.second, rep.per_file = parse_python_report(report)
    return rep


# ── Go: the cover profile of go test ─────────────────────────────────────────

_GO_MODULE = "github.com/Jaetan/aletheia/go/v5/"


@dataclass(frozen=True)
class GoBlock:
    """One block of a Go cover profile: its statements and whether any run reached it."""

    file: str
    statements: int
    hit: bool


def parse_go_profile(text: str, *, exclude_prefix: str = _GO_HARNESS_PREFIX) -> list[GoBlock]:
    """Read a ``go test -coverprofile`` file into blocks, one per block position.

    A block reached by any test binary is hit: the profile carries a line per
    package per block, and the same block appears again where two packages'
    tests both exercise it, so blocks are keyed on position.
    """
    blocks: dict[tuple[str, str], GoBlock] = {}
    for raw in text.splitlines():
        if not raw or raw.startswith("mode:"):
            continue
        position, statements, count = raw.split(" ")
        module_path, span = position.split(":", 1)
        file = module_path.removeprefix(_GO_MODULE)
        file = "go/" + file if not file.startswith("go/") else file
        if file.startswith(exclude_prefix):
            continue
        key = (file, span)
        previous = blocks.get(key)
        hit = int(count) > 0 or (previous is not None and previous.hit)
        blocks[key] = GoBlock(file, int(statements), hit)
    return list(blocks.values())


def go_figures(blocks: Iterable[GoBlock]) -> tuple[Figure, Figure, dict[str, dict[str, float]]]:
    """Statements and blocks, whole and per file, from the profile's blocks."""
    stmt_hit = stmt_all = block_hit = block_all = 0
    by_file: dict[str, list[int]] = {}
    for block in blocks:
        counts = by_file.setdefault(block.file, [0, 0, 0, 0])
        counts[1] += block.statements
        counts[3] += 1
        stmt_all += block.statements
        block_all += 1
        if block.hit:
            counts[0] += block.statements
            counts[2] += 1
            stmt_hit += block.statements
            block_hit += 1
    per_file = {
        file: {
            "lines_pct": round(100.0 * c[0] / max(c[1], 1), 2),
            "blocks_pct": round(100.0 * c[2] / max(c[3], 1), 2),
        }
        for file, c in sorted(by_file.items())
    }
    return (
        Figure("statements", stmt_hit, stmt_all),
        Figure("blocks", block_hit, block_all),
        per_file,
    )


def run_go(artifact_dir: Path) -> CoverageReport:
    """Run every Go module's suite with a cover profile and read the profiles."""
    rep = CoverageReport(binding="go", tool="go test -cover")
    try:
        go = find_executable("go")
    except RuntimeError as exc:
        rep.error = str(exc)
        return rep
    blocks: list[GoBlock] = []
    # The core module and the excel module, which has a go.mod of its own that
    # `./...` from go/ stops at.
    for name, module in (("core", REPO_ROOT / "go"), ("excel", REPO_ROOT / "go" / "excel")):
        profile = artifact_dir / f"go-{name}.cover"
        cmd = [go, "test", "./...", "-count=1", "-covermode=atomic", f"-coverprofile={profile}"]
        rep.error = _run(cmd, cwd=module, label=f"coverage go ({name})")
        if rep.error is not None:
            return rep
        blocks += parse_go_profile(profile.read_text(encoding="utf-8"))
    rep.lines, rep.second, rep.per_file = go_figures(blocks)
    return rep


# ── C++: clang's source-based coverage through llvm-cov ──────────────────────


def parse_llvm_export(
    report: Mapping[str, object], *, second: str
) -> tuple[Figure, Figure, dict[str, dict[str, float]]]:
    """Read an llvm-cov export (clang's or cargo-llvm-cov's): lines and one other unit."""
    data = cast("list[Mapping[str, object]]", report["data"])[0]
    totals = cast("Mapping[str, Mapping[str, int]]", data["totals"])
    lines = Figure("lines", totals["lines"]["covered"], totals["lines"]["count"])
    other = Figure(second, totals[second]["covered"], totals[second]["count"])
    per_file: dict[str, dict[str, float]] = {}
    for entry in cast("list[Mapping[str, object]]", data["files"]):
        summary = cast("Mapping[str, Mapping[str, float]]", entry["summary"])
        per_file[_rel(str(entry["filename"]))] = {
            "lines_pct": round(summary["lines"]["percent"], 2),
            f"{second}_pct": round(summary[second]["percent"], 2),
        }
    return lines, other, per_file


def ctest_objects(build_dir: Path) -> list[str]:
    """Every executable ctest would run in the tree, from ctest's own listing.

    llvm-cov reads only the objects it is handed, and a source linked into one
    test binary alone is absent from a summary that names the others; so the
    list is ctest's, never one kept by hand.
    """
    result = run_capture(["ctest", "--test-dir", str(build_dir), "--show-only=json-v1"])
    if result.returncode != 0:
        msg = f"ctest --show-only exited {result.returncode}: {result.stderr.strip()}"
        raise RuntimeError(msg)
    listing = cast("Mapping[str, object]", json.loads(result.stdout))
    tests = cast("list[Mapping[str, object]]", listing["tests"])
    return sorted({str(cast("list[str]", t["command"])[0]) for t in tests})


def shared_objects(build_dir: Path) -> list[str]:
    """List the tree's shared libraries, library under test and fixtures, real files only."""
    return sorted(str(p) for p in build_dir.glob("*.so*") if p.is_file() and not p.is_symlink())


class CoverageError(RuntimeError):
    """A step of a measurement that did not produce what the next step reads."""


def _cpp_build_tree() -> None:
    """Configure and build the instrumented tree, refusing without the toolchain or the kernel."""
    for tool in ("clang++-23", "llvm-profdata-23", "llvm-cov-23", "cmake", "ctest"):
        try:
            _ = find_executable(tool)
        except RuntimeError as exc:
            raise CoverageError(str(exc)) from exc
    if not FFI_LIB.is_file():
        msg = f"kernel missing at {FFI_LIB}: run `cabal run shake -- build` first"
        raise CoverageError(msg)
    configure = [
        "cmake",
        "-S",
        str(REPO_ROOT / "cpp"),
        "-B",
        str(CPP_BUILD_DIR),
        "-DALETHEIA_COVERAGE=ON",
        "-DCMAKE_C_COMPILER=clang-23",
        "-DCMAKE_CXX_COMPILER=clang++-23",
    ]
    build = ["cmake", "--build", str(CPP_BUILD_DIR), "--parallel"]
    for cmd, label in ((configure, "coverage cpp (configure)"), (build, "coverage cpp (build)")):
        error = _run(cmd, cwd=REPO_ROOT / "cpp", label=label)
        if error is not None:
            raise CoverageError(error)


def _cpp_profile(artifact_dir: Path) -> Path:
    """Run ctest under profiling and merge what it wrote into one profdata file."""
    raw_dir = artifact_dir / "cpp-profraw"
    if raw_dir.exists():
        shutil.rmtree(raw_dir)
    raw_dir.mkdir(parents=True)
    env = {**_suite_env(), "LLVM_PROFILE_FILE": str(raw_dir / "%p-%m.profraw")}
    error = _run(
        ["ctest", "--test-dir", str(CPP_BUILD_DIR), "--output-on-failure"],
        cwd=REPO_ROOT / "cpp",
        label="coverage cpp (ctest)",
        env=env,
    )
    if error is not None:
        raise CoverageError(error)
    raws = sorted(raw_dir.glob("*.profraw"))
    if not raws:
        msg = "ctest wrote no profile: the tree is not instrumented"
        raise CoverageError(msg)
    profdata = artifact_dir / "cpp.profdata"
    merge = ["llvm-profdata-23", "merge", "-sparse", *map(str, raws), "-o", str(profdata)]
    merged = run_capture(merge)
    if merged.returncode != 0:
        msg = f"llvm-profdata merge exited {merged.returncode}: {merged.stderr.strip()}"
        raise CoverageError(msg)
    return profdata


def _cpp_export(profdata: Path, artifact_dir: Path) -> Mapping[str, object]:
    """Export the summary over every ctest executable and every shared library of the tree."""
    try:
        objects = ctest_objects(CPP_BUILD_DIR)
    except RuntimeError as exc:
        raise CoverageError(str(exc)) from exc
    export = ["llvm-cov-23", "export", "--summary-only", f"-instr-profile={profdata}", objects[0]]
    for obj in objects[1:] + shared_objects(CPP_BUILD_DIR):
        export += ["-object", obj]
    export.append(f"-ignore-filename-regex={_CPP_IGNORE_REGEX}")
    exported = run_capture(export)
    if exported.returncode != 0:
        msg = f"llvm-cov export exited {exported.returncode}: {exported.stderr.strip()}"
        raise CoverageError(msg)
    _ = (artifact_dir / "cpp-coverage.json").write_text(exported.stdout, encoding="utf-8")
    return cast("Mapping[str, object]", json.loads(exported.stdout))


def run_cpp(artifact_dir: Path) -> CoverageReport:
    """Build the instrumented tree, run ctest under profiling, export the summary."""
    rep = CoverageReport(binding="cpp", tool="llvm-cov (clang -fprofile-instr-generate)")
    try:
        _cpp_build_tree()
        report = _cpp_export(_cpp_profile(artifact_dir), artifact_dir)
    except CoverageError as exc:
        rep.error = str(exc)
        return rep
    rep.lines, rep.second, rep.per_file = parse_llvm_export(report, second="branches")
    return rep


# ── Rust: cargo-llvm-cov over both manifests ─────────────────────────────────

_CARGO_LLVM_COV_VERSION_RE = re.compile(r"cargo-llvm-cov (\d+\.\d+\.\d+)")


def cargo_llvm_cov_version(output: str) -> str | None:
    """Read the version ``cargo llvm-cov --version`` printed, None where it printed none."""
    match = _CARGO_LLVM_COV_VERSION_RE.search(output)
    return match.group(1) if match else None


def _sum_figures(a: Figure, b: Figure) -> Figure:
    """Two crates' counts as one figure of the binding."""
    return Figure(a.unit, a.covered + b.covered, a.total + b.total)


def _cargo_llvm_cov(pinned_version: str | None) -> str:
    """Find cargo with cargo-llvm-cov at the pinned version, refusing any other."""
    try:
        cargo = find_executable("cargo")
    except RuntimeError as exc:
        raise CoverageError(str(exc)) from exc
    version = run_capture([cargo, "llvm-cov", "--version"])
    found = cargo_llvm_cov_version(version.stdout) if version.returncode == 0 else None
    if found is None:
        msg = "cargo-llvm-cov is not installed: cargo install cargo-llvm-cov --locked"
        raise CoverageError(msg)
    if pinned_version is not None and found != pinned_version:
        msg = f"cargo-llvm-cov {found} is installed where the record pins {pinned_version}"
        raise CoverageError(msg)
    return cargo


def _rust_crate(
    cargo: str, name: str, crate: Path, extra: list[str], artifact_dir: Path
) -> tuple[Figure, Figure, dict[str, dict[str, float]]]:
    """Measure one crate under cargo-llvm-cov and read its export."""
    out = artifact_dir / f"rust-{name}.json"
    cmd = [cargo, "llvm-cov", *extra, "--json", "--summary-only", "--output-path", str(out)]
    error = _run(cmd, cwd=crate, label=f"coverage rust ({name})")
    if error is not None:
        raise CoverageError(error)
    report = cast("Mapping[str, object]", json.loads(out.read_text(encoding="utf-8")))
    return parse_llvm_export(report, second="regions")


def run_rust(artifact_dir: Path, *, pinned_version: str | None = None) -> CoverageReport:
    """Run both crates' suites under cargo-llvm-cov and sum their counts."""
    rep = CoverageReport(binding="rust", tool="cargo-llvm-cov")
    # The main crate with every feature, as the always-on step runs it, and
    # the excel crate, whose manifest the main one does not reach.
    crates: tuple[tuple[str, Path, list[str]], ...] = (
        ("core", REPO_ROOT / "rust", ["--all-features"]),
        ("excel", REPO_ROOT / "rust" / "excel", []),
    )
    try:
        cargo = _cargo_llvm_cov(pinned_version)
        for name, crate, extra in crates:
            lines, regions, files = _rust_crate(cargo, name, crate, extra, artifact_dir)
            rep.lines = lines if rep.lines is None else _sum_figures(rep.lines, lines)
            rep.second = regions if rep.second is None else _sum_figures(rep.second, regions)
            rep.per_file.update(files)
    except CoverageError as exc:
        rep.error = str(exc)
    return rep


# ── The gate ─────────────────────────────────────────────────────────────────

type Verdict = dict[str, object]


def _figure_verdict(figure: Figure | None, floor: float, recorded: object) -> dict[str, object]:
    """One figure against its floor and, where there is one, the recorded figure."""
    if figure is None:
        return {"status": "missing"}
    entry: dict[str, object] = {
        "unit": figure.unit,
        "observed_pct": round(figure.pct, 2),
        "floor_pct": floor,
        "status": "ok" if figure.pct >= floor else "under_floor",
    }
    if figure.total == 0:
        entry["status"] = "empty"
    if isinstance(recorded, (int, float)):
        entry["recorded_pct"] = recorded
        entry["delta_pct"] = round(figure.pct - float(recorded), 2)
    return entry


def gate(rep: CoverageReport, spec: Spec) -> Verdict:
    """One binding's verdict: both figures over the floors, or why not."""
    if rep.error:
        return {"status": "error", "error": rep.error}
    floors = cast("Mapping[str, float]", spec.get("floors", {}))
    bindings = cast("Mapping[str, Spec]", spec.get("bindings", {}))
    binding = bindings.get(rep.binding, {})
    baseline = cast("Mapping[str, object]", binding.get("baseline", {}))
    second_name = str(cast("Mapping[str, object]", binding.get("second", {})).get("unit", ""))
    if rep.second is not None and rep.second.unit != second_name:
        return {
            "status": "error",
            "error": (
                f"the record names {second_name!r} as the second figure, "
                f"the tool gave {rep.second.unit!r}"
            ),
        }
    lines = _figure_verdict(
        rep.lines, float(floors.get("lines_pct", 80)), baseline.get("lines_pct")
    )
    second = _figure_verdict(
        rep.second, float(floors.get("branches_pct", 60)), baseline.get("second_pct")
    )
    status = "ok" if lines["status"] == "ok" and second["status"] == "ok" else "regression"
    return {"status": status, "lines": lines, "second": second}


def load_spec() -> Spec:
    """Load the record."""
    return cast("Spec", yaml.safe_load(SPEC_PATH.read_text(encoding="utf-8")))


def baseline_fragment(rep: CoverageReport, run_at: str) -> str:
    """Render the ``baseline:`` block a run measured, to paste into the record."""
    if rep.lines is None or rep.second is None:
        return ""
    return (
        "    baseline:\n"
        f"      lines_pct: {rep.lines.pct:.2f}\n"
        f"      lines_covered: {rep.lines.covered}\n"
        f"      lines_total: {rep.lines.total}\n"
        f"      second_pct: {rep.second.pct:.2f}\n"
        f"      second_covered: {rep.second.covered}\n"
        f"      second_total: {rep.second.total}\n"
        f'      run_at: "{run_at}"\n'
    )


RUNNERS: list[tuple[str, Callable[[Path, Spec], CoverageReport]]] = [
    ("python", lambda art, _spec: run_python(art)),
    ("go", lambda art, _spec: run_go(art)),
    ("cpp", lambda art, _spec: run_cpp(art)),
    (
        "rust",
        lambda art, spec: run_rust(
            art,
            pinned_version=str(
                cast("Mapping[str, Spec]", spec.get("bindings", {})).get("rust", {}).get("version")
                or ""
            )
            or None,
        ),
    ),
]


def coverage_scope(repo_root: Path) -> set[str] | None:
    """Decide which bindings this branch's diff could move, by this lane's tables."""
    return bindings_in_scope(
        repo_root,
        binding_dirs=_BINDING_DIRS,
        global_paths=_GLOBAL_COVERAGE_PATHS,
        no_scope_env=_NO_DIFF_SCOPE_ENV,
    )


def write_scope(binding: str | None, repo_root: Path) -> int:
    """Write ``LANE_MEASURES`` where the workflow reads it, for one binding or the lane."""
    in_scope = coverage_scope(repo_root)
    if binding is None:
        measures = in_scope is None or bool(in_scope)
    else:
        measures = in_scope is None or binding in in_scope
    what = binding or "the lane"
    _ = sys.stderr.write(
        f"[coverage] scope: {what} is in the diff scope, so the toolchain installs\n"
        if measures
        else f"[coverage] scope: no change reaches {what}, so nothing installs\n"
    )
    write_workflow_line(f"{MEASURES_VAR}={'1' if measures else '0'}")
    return 0


def _display(path: Path) -> str:
    """Name a path relative to the tree where it is under it, whole where it is not."""
    return str(path.relative_to(REPO_ROOT)) if path.is_relative_to(REPO_ROOT) else str(path)


def _measure(
    asked: list[str] | None, in_scope: set[str] | None, spec: Spec, artifact_dir: Path
) -> tuple[list[CoverageReport], dict[str, Verdict]]:
    """Run every binding asked for and in scope, archive each report, judge each."""
    run_at = time.strftime("%Y-%m-%d")
    reports: list[CoverageReport] = []
    verdicts: dict[str, Verdict] = {}
    for name, runner in RUNNERS:
        if asked is not None and name not in asked:
            continue
        if asked is None and in_scope is not None and name not in in_scope:
            _ = sys.stderr.write(f"[coverage] {name}: out of scope, not measured\n")
            continue
        began = time.monotonic()
        rep = runner(artifact_dir, spec)
        rep.elapsed_s = time.monotonic() - began
        reports.append(rep)
        _ = (artifact_dir / f"{name}.json").write_text(
            json.dumps(rep.to_dict(), indent=2) + "\n", encoding="utf-8"
        )
        _ = (artifact_dir / f"baseline-{name}.yaml").write_text(
            baseline_fragment(rep, run_at), encoding="utf-8"
        )
        verdicts[name] = gate(rep, spec)
    return reports, verdicts


def main(argv: list[str] | None = None) -> int:
    """Measure every binding asked for and in scope, archive, gate on the floors."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--binding",
        action="append",
        choices=[name for name, _ in RUNNERS],
        help="measure this binding only (repeatable); default: every binding in scope",
    )
    _ = parser.add_argument(
        "--scope",
        action="store_true",
        help=f"write {MEASURES_VAR}=1|0 for the lane (or --binding) and exit without measuring",
    )
    args = parser.parse_args(argv)
    asked = cast("list[str] | None", args.binding)
    if args.scope:
        return write_scope(asked[0] if asked else None, REPO_ROOT)
    if not SPEC_PATH.is_file():
        _ = sys.stderr.write(f"ERROR: record missing at {SPEC_PATH}\n")
        return SPEC_ERROR_EXIT
    spec = load_spec()
    sha = short_sha(REPO_ROOT)
    # A run over every binding starts the commit's directory afresh; a run
    # over one binding adds to it, since the four steps the CI runner
    # registers each measure one binding into the same directory, and a wipe
    # per step would leave only the last one's report.  Each one-binding run
    # names its own summary for the same reason.
    artifact_dir = (
        prepare_artifact_dir(ARTIFACT_BASE, sha) if asked is None else ARTIFACT_BASE / sha
    )
    artifact_dir.mkdir(parents=True, exist_ok=True)
    in_scope = coverage_scope(REPO_ROOT)
    _ = sys.stderr.write(
        "[coverage] diff-scope: measuring ALL bindings\n"
        if in_scope is None
        else f"[coverage] diff-scope: changed bindings only → {sorted(in_scope) or 'NONE'}\n"
    )
    started = time.monotonic()
    reports, verdicts = _measure(asked, in_scope, spec, artifact_dir)
    summary: dict[str, object] = {
        "commit": sha,
        "artifact_dir": _display(artifact_dir),
        "diff_scope": "all" if in_scope is None else sorted(in_scope),
        "elapsed_s": round(time.monotonic() - started, 1),
        "runs": [r.to_dict() for r in reports],
        "verdicts": verdicts,
        "passed": all(v["status"] == "ok" for v in verdicts.values()),
    }
    if not verdicts:
        emit("[coverage] nothing measured: no binding in scope")
    # A run over every binding writes the directory's summary; a run over one
    # binding writes its own file beside it, since the CI runner's four
    # per-binding steps run concurrently and one file written by all four
    # would carry whichever finished last.
    rendered = json.dumps(summary, indent=2)
    _ = (artifact_dir / _summary_name(asked)).write_text(rendered + "\n", encoding="utf-8")
    emit(rendered)
    return 0 if summary["passed"] else 1


def _summary_name(asked: list[str] | None) -> str:
    """Name the summary a run writes: the directory's, or one per binding asked for."""
    return "summary.json" if asked is None else f"summary-{'-'.join(sorted(set(asked)))}.json"


if __name__ == "__main__":
    sys.exit(main())
