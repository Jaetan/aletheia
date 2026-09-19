# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Dynamic mutation-testing runner.

Drives each binding's mutation tool in turn (mutmut for Python, go-mutesting
for Go, Mull for C++), parses tool-specific output into a normalized
``MutationReport`` shape, and archives per-binding JSON to
``benchmarks/mutation/<short_sha>/``.

Drift gate: each binding's report is compared against the baseline survivor
count recorded in ``docs/MUTATION_BENCH.yaml``.  ``observed > baseline + 0``
fails the lane (allow exact equality only — any new survivor is a finding
per AGENTS.md cat 14(g) "an unjustified survivor is a test gap").  Where the
baseline also carries a ``survivors_ledger``, every survivor must be one of
its rows, by mutator, repository-relative file and source-line text, up to
the count the row records: a survivor traded for another leaves the count
unchanged and fails the lane all the same.  A ledger row that no longer
survives is reported as stale and does not fail the lane, the way a lower
count does not; the record is lowered by the change that made it stale.

Per-binding env contract:

  - ALETHEIA_MUTATION_CHECK    set to anything truthy by run_ci.py to enable
                               this lane (run_ci.py only invokes us when the
                               env var or `--mutation` flag is set; this
                               script does NOT re-check the env var).

Optional per-binding skip (useful for partial runs in CI lanes):

  - ALETHEIA_MUTATION_SKIP_PYTHON=1
  - ALETHEIA_MUTATION_SKIP_GO=1
  - ALETHEIA_MUTATION_SKIP_CPP=1

Diff scoping (automatic): on a PR branch only the binding(s) whose directory the
diff vs ``main`` touches are run; the rest are skipped, since an unchanged
binding's survivor count is unchanged from its baseline by construction.  A
change to a shared artifact (the Agda ``src/`` → ``.so``, this harness, or
``docs/MUTATION_BENCH.yaml``) forces ALL bindings, as does push:main / an empty
diff (the post-merge backstop).  Set ``ALETHEIA_MUTATION_NO_DIFF_SCOPE=1`` to
force the full run regardless.  See ``bindings_in_scope``.

Artifacts written:

  benchmarks/mutation/<short_sha>/
    python.json    {tool, total_mutants, killed, survived, score_pct, raw_log}
    go.json        same shape
    cpp.json       same shape
    cpp-mull.json  Mull's Elements report: every C++ mutant with its status
                   and site, which the ledger check reads
    summary.json   {commit, runs: [...], passed: bool, baseline_drift: {...}}

Usage:
  ALETHEIA_MUTATION_CHECK=1 python3 tools/mutation_run.py

The static counterpart is ``tools/check_mutation_setup.py``, which gates on
each binding's hot-path source files existing per ``docs/MUTATION_BENCH.yaml``.
"""

from __future__ import annotations

import collections
import copy
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, NotRequired, TypedDict, cast

import yaml

from tools._common import (
    find_executable,
    prepare_artifact_dir,
    run_capture,
    run_streaming,
    short_sha,
    write_and_report_summary,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

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


class LedgerRow(TypedDict):
    """One recorded survivor: its mutator, file, source line and multiplicity."""

    mutator: str
    file: str
    text: str
    count: int


class Baseline(TypedDict):
    """The per-binding baseline block in ``docs/MUTATION_BENCH.yaml``."""

    survivors: NotRequired[int]
    timeout_ceiling: NotRequired[int]
    total_mutants: NotRequired[int]
    score_pct: NotRequired[int]
    run_at: NotRequired[str]
    survivors_ledger: NotRequired[list[LedgerRow]]


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
    observed_timeouts: NotRequired[int]
    timeout_ceiling: NotRequired[int]
    unrecorded_survivors: NotRequired[list[LedgerRow]]
    stale_ledger: NotRequired[list[LedgerRow]]


# A survivor's identity in the ledger: mutator, repository-relative file and
# the text of its source line.  Keyed on the text and not the line number, so
# an edit above the site does not move it, and an edit of the site does.
SurvivorKey = tuple[str, str, str]


@dataclass
class MutationReport:
    """Per-binding mutation result; serialized to ``<binding>.json``."""

    binding: str
    tool: str
    killed: int
    survived: int
    raw_log: str
    error: str | None = None
    # Mutants the tool started and could not finish, where it reports them.
    # They are neither killed nor survived, so a run that timed out on nearly
    # everything reports no survivors and full efficacy; the drift gate reads
    # this to refuse such a run.  ``None`` where the tool has no such bucket.
    timeouts: int | None = None

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
            "timeouts": self.timeouts,
            "score_pct": self.score_pct,
            "raw_log_tail": self.raw_log[-RAW_LOG_TAIL_CHARS:],
            "error": self.error,
        }


def rows_to_ledger(rows: dict[SurvivorKey, int]) -> list[LedgerRow]:
    """Render survivor rows in the ledger's row shape, sorted by identity."""
    return [
        {"mutator": mutator, "file": file, "text": text, "count": count}
        for (mutator, file, text), count in sorted(rows.items())
    ]


def ledger_to_rows(ledger: list[LedgerRow]) -> dict[SurvivorKey, int]:
    """Read a ledger back into survivor rows keyed by identity."""
    rows: dict[SurvivorKey, int] = collections.Counter()
    for row in ledger:
        rows[(row["mutator"], row["file"], row["text"])] += row["count"]
    return rows


def elements_survivor_rows(
    report: Mapping[str, object], read_line: Callable[[str, int], str]
) -> dict[SurvivorKey, int]:
    """Collect the survivors of a Mull Elements report into rows.

    ``report`` is the parsed ``mutation-testing-elements`` JSON: ``files``
    maps an absolute path to its mutants, each with a ``status``, a
    ``mutatorName`` and a start line.  A path is made repository-relative at
    its ``cpp/`` component; ``read_line(file, line)`` supplies the source line,
    which is stripped before it keys the row.
    """
    rows: dict[SurvivorKey, int] = collections.Counter()
    files = cast("Mapping[str, Mapping[str, object]]", report.get("files", {}))
    for path, entry in files.items():
        mutants = cast("list[Mapping[str, object]]", entry.get("mutants", []))
        for mutant in mutants:
            if mutant.get("status") != "Survived":
                continue
            file = "cpp/" + path.split("/cpp/", 1)[1] if "/cpp/" in path else path
            location = cast("Mapping[str, Mapping[str, int]]", mutant["location"])
            line = location["start"]["line"]
            rows[(str(mutant["mutatorName"]), file, read_line(file, line).strip())] += 1
    return rows


def _repo_line(file: str, line: int) -> str:
    """Read the ``line``-th line (1-based) of ``file`` under the repository root."""
    with (REPO_ROOT / file).open(encoding="utf-8") as src:
        return src.read().split("\n")[line - 1]


# The Elements report the C++ runner asks Mull for, beside ``cpp.json``.
CPP_ELEMENTS_REPORT = "cpp-mull.json"


def cpp_survivor_rows(artifact_dir: Path) -> dict[SurvivorKey, int] | None:
    """Read the C++ sweep's survivor rows from its Elements report, if it wrote one."""
    path = artifact_dir / CPP_ELEMENTS_REPORT
    if not path.is_file():
        return None
    elements = cast("Mapping[str, object]", json.loads(path.read_text(encoding="utf-8")))
    return elements_survivor_rows(elements, _repo_line)


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
    """Tally per-status mutant counts from ``mutmut run`` / ``results`` output.

    mutmut 3.x's authoritative tally is the live progress line that ``mutmut
    run`` overwrites in place; its final state is emoji-keyed::

        <spinner> N/Total  🎉 <killed>  🫥 <no-tests>  ⏰ <timeout>
                           🤔 <suspicious>  🙁 <survived>  ...

    (`mutmut results` lists ONLY the non-killed mutants, one per line —
    ``module.x__mutmut_K: survived`` — so the killed count is NOT recoverable
    from ``results`` alone; the run summary is the only source for killed.)

    Primary: parse the last emoji summary.  Fallback (summary shape changed):
    count the per-mutant ``: survived`` / ``: no tests`` lines from ``results``
    — that keeps the gate-critical SURVIVOR count correct even if the killed
    count (score only) is lost.  Legacy ``X/Y mutants`` last.
    """
    summary = re.findall(
        r"🎉\s*(\d+)\s+🫥\s*(\d+)\s+⏰\s*(\d+)\s+🤔\s*(\d+)\s+🙁\s*(\d+)",
        raw,
    )
    if summary:
        killed, no_tests, timeout, _suspicious, survived = (int(x) for x in summary[-1])
        return MutmutCounts(killed=killed, survived=survived, timeout=timeout, skipped=no_tests)
    # Fallback: count per-mutant status lines emitted by `mutmut results`.
    survived = len(re.findall(r":\s*survived\s*$", raw, re.MULTILINE))
    no_tests = len(re.findall(r":\s*no tests\s*$", raw, re.MULTILINE))
    timeout = len(re.findall(r":\s*timeout\s*$", raw, re.MULTILINE))
    if survived or no_tests or timeout:
        # killed is not listed by `mutmut results`; left 0 (score-only loss).
        return MutmutCounts(killed=0, survived=survived, timeout=timeout, skipped=no_tests)
    # Legacy parse: the older "X/Y mutants" line.
    legacy = re.search(r"(\d+)\s*/\s*(\d+)\s*mutants?", raw)
    if legacy:
        killed, total = int(legacy.group(1)), int(legacy.group(2))
        return MutmutCounts(killed=killed, survived=total - killed, timeout=0, skipped=0)
    return MutmutCounts(killed=0, survived=0, timeout=0, skipped=0)


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
            "mutmut not installed in venv; run "
            + "`python/.venv/bin/pip install -e 'python/.[mutation]'`"
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
    # Erase mutmut's persistent work-tree before every run.  mutmut reuses
    # ``python/mutants/`` across invocations and only invalidates cached
    # kill/survive verdicts on SOURCE changes — NOT on TEST changes (test files
    # are not in ``source_paths``, so their content is not tracked).  A test
    # edit, or files arriving via ``git merge`` / ``checkout`` / ``pull``,
    # therefore yields stale verdicts (observed live: a merge that added a
    # function plus its killing tests reported 20 phantom survivors until the
    # tree was cleared).  Erasing it makes this local gate reproduce CI's
    # fresh-checkout semantics exactly — CI already starts from a clean checkout
    # (``mutants/`` is gitignored and uncached), so this is a no-op there.  Cost
    # is local only: ~11 s on the Python lane (warm reuse 29 s -> clean 40 s).
    shutil.rmtree(cwd / "mutants", ignore_errors=True)
    # mutmut 3.6 keeps ALL state under mutants/ — the mutated tree, the copied
    # tests/ (the piece that goes stale), and the mutmut-stats.json results —
    # with no separate .mutmut/ cache, so the erase above is complete.  Run
    # produces that state; results parses it.  Both write to stdout; we capture
    # both.
    # The run is the long half and streams, so a sweep killed by a wall clock
    # still leaves the log of how far it got; ``results`` is a fast read of the
    # state the run wrote and stays captured.  Both carry a custom ``env``
    # (ALETHEIA_LIB), and ``str(mutmut_bin)`` is an absolute path (no S607).
    run_proc = run_streaming([str(mutmut_bin), "run"], cwd=cwd, env=env)
    raw = "=== mutmut run ===\n" + run_proc.stdout + "\n"
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
    proc = run_streaming([gremlins, "unleash", "./aletheia"], cwd=cwd)
    raw = proc.stdout
    (artifact_dir / "go.raw.txt").write_text(raw)

    return parse_gremlins_summary(raw, f"exit {proc.returncode}")


def parse_gremlins_summary(raw: str, where: str) -> MutationReport:
    """Read a gremlins run's tail summary into a report.

    Separate from the run so the drift gate can be shown to refuse a recorded
    loaded-machine sweep without one having to be reproduced.  The tail is::

        Killed: N, Lived: N, Not covered: N
        Timed out: N, Not viable: N, Skipped: N
        Test efficacy: P.PP%
        Mutator coverage: P.PP%
    """
    killed_m = re.search(r"Killed:\s*(\d+)", raw)
    survived_m = re.search(r"Lived:\s*(\d+)", raw)
    timeout_m = re.search(r"Timed out:\s*(\d+)", raw)
    if not (killed_m and survived_m):
        return MutationReport(
            "go",
            "gremlins",
            0,
            0,
            raw,
            error=(f"could not parse gremlins summary (see go.raw.txt; {where})"),
        )
    # gremlins' "Not covered" mutants are on lines no test reaches; they do not
    # contribute to the killed/lived split, so total_mutants = killed + survived.
    return MutationReport(
        "go",
        "gremlins",
        int(killed_m.group(1)),
        int(survived_m.group(1)),
        raw,
        timeouts=int(timeout_m.group(1)) if timeout_m else None,
    )


def _check_cpp_tools() -> tuple[str, str] | str:
    """Return ``(cmake, mull_runner)`` paths when C++ can run, else an error string."""
    cmake = shutil.which("cmake")
    if cmake is None:
        return "cmake not in PATH; install CMake 3.25+ to run the C++ mutation lane"
    mull_runner = shutil.which("mull-runner-23")
    if mull_runner is None:
        return (
            "mull-runner-23 not in PATH; build it with tools/build_mull.sh "
            "(see docs/operations/MUTATION.md § Installation)"
        )
    if shutil.which("clang++-23") is None:
        return "clang++-23 not in PATH; install clang-23 (apt.llvm.org, or Debian apt)"
    plugin = Path.home() / ".local" / "bin" / "mull-ir-frontend-23"
    if not plugin.is_file():
        return (
            f"mull-ir-frontend-23 plugin not found at {plugin}; "
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
    sanitizer: str,
) -> str | MutationReport:
    """Configure + build one mutation build tree, returning the raw log or a failure report."""
    cmake_proc = run_streaming(
        [
            cmake,
            "-B",
            str(build_dir),
            "-DALETHEIA_MUTATION=ON",
            f"-DALETHEIA_SANITIZER={sanitizer}",
            "-DCMAKE_C_COMPILER=clang-23",
            "-DCMAKE_CXX_COMPILER=clang++-23",
        ],
        cwd=cpp_root,
    )
    raw = "=== cmake configure ===\n" + cmake_proc.stdout + "\n"
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

    build_proc = run_streaming(
        [cmake, "--build", str(build_dir), "--target", "unit_tests"],
        cwd=cpp_root,
    )
    raw += "=== cmake build ===\n" + build_proc.stdout + "\n"
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


# The two trees the C++ sweep runs, by the sanitizer each is built with and
# the directory it lives in. Under LeakSanitizer a mutant that removes a
# destructor leaks the object and fails, where a plain build cannot tell it
# from the original. The plain tree carries the allocation-fault sweeps, which
# replace the program's allocation functions to reach the cleanup a container
# runs while it throws; a sanitizer runtime defines those same functions, so
# the two cannot be linked together. A mutant survives the sweep only where it
# survived both.
CPP_LANES: tuple[tuple[str, str], ...] = (("leak", "build-mutation"), ("", "build-mutation-plain"))


def _lane_report_name(sanitizer: str) -> str:
    """Name the Elements report one lane writes, beside the merged one."""
    return f"{Path(CPP_ELEMENTS_REPORT).stem}-{sanitizer or 'plain'}"


def merge_elements(reports: list[Mapping[str, object]]) -> dict[str, object]:
    """Merge Elements reports, keeping a mutant a survivor only where every lane let it survive.

    The lanes compile the same sources with the same plugin, so they carry the
    same mutants under the same identifiers; a mutant one lane killed is
    killed, whichever instrument read it.
    """
    survived_everywhere: set[str] | None = None
    for report in reports:
        files = cast("Mapping[str, Mapping[str, object]]", report.get("files", {}))
        survivors = {
            str(mutant["id"])
            for entry in files.values()
            for mutant in cast("list[Mapping[str, object]]", entry.get("mutants", []))
            if mutant.get("status") == "Survived"
        }
        survived_everywhere = (
            survivors if survived_everywhere is None else survived_everywhere & survivors
        )
    merged = copy.deepcopy(dict(reports[0]))
    files = cast("dict[str, dict[str, object]]", merged.get("files", {}))
    for entry in files.values():
        for mutant in cast("list[dict[str, object]]", entry.get("mutants", [])):
            if mutant.get("status") != "Survived":
                continue
            if str(mutant["id"]) not in (survived_everywhere or set()):
                mutant["status"] = "Killed"
    return merged


def _run_cpp_lane(
    mull_runner: str,
    cpp_root: Path,
    build_dir: Path,
    artifact_dir: Path,
    sanitizer: str,
) -> tuple[str, tuple[int, int] | None]:
    """Run one built tree under mull-runner, returning its log and its (killed, survived)."""
    # The mutation binary folds in the real-FFI integration tests, which read
    # the repository root from the environment the way ctest passes it.  Mull
    # runs the binary directly, so nothing would set it and every mutant would
    # read killed because the test died at setup.
    #
    # ALETHEIA_LIB is dropped for the same reason in reverse: with it set the
    # library lookup returns before it reads the repository root, leaving that
    # read's mutants uncovered, so the same tree would score differently for a
    # caller who had sourced the environment script.
    mull_env = os.environ | {"ALETHEIA_REPO_ROOT": str(REPO_ROOT)}
    mull_env.pop("ALETHEIA_LIB", None)
    # The IDE reporter prints the summary the counts are read from; the
    # Elements reporter writes every mutant with its status and site, which
    # is what the ledger is checked against.
    runner_proc = run_streaming(
        [
            mull_runner,
            str(build_dir / "unit_tests"),
            "--reporters=IDE",
            "--reporters=Elements",
            f"--report-dir={artifact_dir}",
            f"--report-name={_lane_report_name(sanitizer)}",
        ],
        cwd=cpp_root,
        env=mull_env,
    )
    lane = sanitizer or "plain"
    raw = f"=== mull-runner-23 ({lane}) ===\n" + runner_proc.stdout + "\n"
    # Mull's own summary goes to the IDE report, and its stdout carries the
    # survivor count only when there is one: a lane that killed everything
    # says so in the report alone, so the report is part of the lane's log.
    ide_report = artifact_dir / f"{_lane_report_name(sanitizer)}.txt"
    if ide_report.is_file():
        raw += ide_report.read_text(encoding="utf-8") + "\n"
    return raw, mull_counts(raw)


def _sweep_cpp_lane(
    cmake: str,
    mull_runner: str,
    build_dir: Path,
    artifact_dir: Path,
    sanitizer: str,
) -> tuple[str, Mapping[str, object] | str]:
    """Build and sweep one lane, returning its log and its report or the reason it has none."""
    lane = sanitizer or "plain"
    cpp_root = build_dir.parent
    raw = f"=== {lane} lane ===\n"
    built = _build_cpp_mutation_tree(cmake, cpp_root, build_dir, artifact_dir, sanitizer)
    if isinstance(built, MutationReport):
        return raw + built.raw_log, built.error or f"the {lane} lane did not build"
    raw += built
    lane_raw, counts = _run_cpp_lane(mull_runner, cpp_root, build_dir, artifact_dir, sanitizer)
    raw += lane_raw
    if counts is None:
        return raw, f"could not parse the {lane} lane's mull-runner-23 summary (see cpp.raw.txt)"
    report_path = artifact_dir / f"{_lane_report_name(sanitizer)}.json"
    if not report_path.is_file():
        return raw, f"the {lane} lane wrote no {report_path.name}"
    return raw, cast("Mapping[str, object]", json.loads(report_path.read_text(encoding="utf-8")))


def run_cpp(artifact_dir: Path) -> MutationReport:
    """Mull pass over both mutation trees; a mutant survives only where every lane let it."""
    checked = _check_cpp_tools()
    if isinstance(checked, str):
        return MutationReport("cpp", "mull", 0, 0, "", error=checked)
    cmake, mull_runner = checked

    cpp_root = REPO_ROOT / "cpp"
    raw = ""
    reports: list[Mapping[str, object]] = []
    for sanitizer, directory in CPP_LANES:
        lane_raw, outcome = _sweep_cpp_lane(
            cmake, mull_runner, cpp_root / directory, artifact_dir, sanitizer
        )
        raw += lane_raw
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        if isinstance(outcome, str):
            return MutationReport("cpp", "mull", 0, 0, raw, error=outcome)
        reports.append(outcome)

    merged = merge_elements(reports)
    (artifact_dir / CPP_ELEMENTS_REPORT).write_text(json.dumps(merged))
    rows = elements_survivor_rows(merged, _repo_line)
    survived = sum(rows.values())
    total = sum(
        len(cast("list[object]", entry.get("mutants", [])))
        for entry in cast("Mapping[str, Mapping[str, object]]", merged.get("files", {})).values()
    )
    raw += f"=== merged ===\nkilled {total - survived}, survived {survived} of {total}\n"
    (artifact_dir / "cpp.raw.txt").write_text(raw)
    return MutationReport("cpp", "mull", total - survived, survived, raw)


def mull_counts(raw: str) -> tuple[int, int] | None:
    """Read ``(killed, survived)`` from a lane's log, or None if it carries no summary.

    The log is mull-runner's stdout followed by its IDE report.

    Mull-19 tail summary lines (the actual format observed empirically)::

        [info] Mutation score: 56%
        [info] Surviving mutants: 17
        [info] Total execution time: 273ms

    When NOTHING survives, Mull omits the "Surviving mutants:" line entirely
    and prints "All mutations have been killed" with a 100% score instead, so
    a missing survivor line is the 0-survivor case, not a parse failure.  The
    exact total comes from Mull's "<n>/<n>. Finished" progress tail (killed =
    total - survived); the score-based estimate is the fallback when the
    progress line is absent (older Mull / piped output).
    """
    survived_m = re.search(r"Surviving mutants:\s*(\d+)", raw) or re.search(
        r"Survived[^:\n]*:\s*(\d+)", raw
    )
    all_killed = bool(
        re.search(r"All mutations have been killed", raw)
        or re.search(r"Mutation score:\s*100\s*%", raw)
    )
    if survived_m:
        survived = int(survived_m.group(1))
    elif all_killed:
        survived = 0
    else:
        return None
    finished = re.findall(r"\d+/(\d+)\.\s*Finished", raw)
    killed = int(finished[-1]) - survived if finished else _killed_from_mull(raw, survived)
    return killed, survived


# ── Diff-scope ──────────────────────────────────────────────────────────────
# A binding's mutation result can only change if its own source, tests, or
# mutation config changed — OR if a shared artifact every binding depends on
# changed (the .so they all dlopen, or this harness / the baselines).  So on a
# PR we run only the affected engine(s); an unchanged binding's survivor count
# is definitionally unchanged from its baseline, so skipping it is coverage-
# neutral.  Mirrors ``tools/_ci_steps._build_graph_changed``'s fail-safe
# ``git diff main...HEAD`` precedent.
#
# Per-binding paths map to the WHOLE binding directory, not just its source:
# mutmut / Mull kill mutants by RUNNING that binding's tests, so a test-only or
# mutation-config-only edit can raise a binding's survivor count.  Under-scoping
# a binding is a correctness bug (a real regression skipped); over-scoping only
# costs time — so per-binding we scope generously.
_BINDING_DIRS: dict[str, str] = {
    "python": "python/",
    "go": "go/",
    "cpp": "cpp/",
}

# A change under any of these can alter the shared ``.so`` every binding dlopens,
# or this harness / the baselines themselves — so it forces ALL bindings.  This
# set IS precision-sensitive: a miss here under-scopes (the dangerous direction),
# unlike the generous per-binding dirs above.
_GLOBAL_MUTATION_PATHS: tuple[str, ...] = (
    "src/",  # Agda → MAlonzo → libaletheia-ffi.so (every binding dlopens it)
    "haskell-shim/",  # FFI shim → .so
    "Shakefile.hs",  # build graph → .so
    "shake.cabal",
    "aletheia.agda-lib",
    "tools/mutation_run.py",  # this harness
    "tools/_common.py",  # the harness's shared helpers
    "docs/MUTATION_BENCH.yaml",  # the per-binding baselines the drift gate reads
    ".github/workflows/pr-heavy-lanes.yml",  # the lane definition
)

# Escape hatch: force every binding to run regardless of the diff.
_NO_DIFF_SCOPE_ENV = "ALETHEIA_MUTATION_NO_DIFF_SCOPE"


def bindings_in_scope(repo_root: Path) -> set[str] | None:
    """Bindings whose mutation result the branch diff vs ``main`` could change.

    Returns ``None`` — meaning "run ALL bindings", the fail-SAFE answer — when:

      * the escape-hatch env var is set,
      * git is absent / the diff cannot be computed (no ``git`` binary, no
        ``main`` ref, git error),
      * the diff is EMPTY (push:main / on-main: ``HEAD == main`` — the
        cache-seeding + post-merge backstop run), or
      * any GLOBAL path changed (shared ``.so`` / harness / baselines).

    Otherwise returns the set of bindings whose directory the diff touched —
    possibly empty (e.g. a docs-only PR), meaning "run NONE".
    """
    if os.environ.get(_NO_DIFF_SCOPE_ENV) == "1":
        return None
    try:
        git = find_executable("git")
    except RuntimeError:
        return None  # no `git` binary on PATH — fail safe to the full run
    result = run_capture(
        [git, "-C", str(repo_root), "diff", "--name-only", "main...HEAD"],
    )
    if result.returncode != 0:
        return None  # no `main` ref / git error — fail safe to the full run
    changed = [line for line in result.stdout.splitlines() if line]
    if not changed:
        return None  # push:main / no diff — run the full backstop
    if any(line.startswith(_GLOBAL_MUTATION_PATHS) for line in changed):
        return None
    return {
        binding
        for binding, prefix in _BINDING_DIRS.items()
        if any(line.startswith(prefix) for line in changed)
    }


# (binding-name, skip-env-var, runner) per binding, in the order reports are produced.
RUNNERS: list[tuple[str, str, Callable[[Path], MutationReport]]] = [
    ("python", "ALETHEIA_MUTATION_SKIP_PYTHON", run_python),
    ("go", "ALETHEIA_MUTATION_SKIP_GO", run_go),
    ("cpp", "ALETHEIA_MUTATION_SKIP_CPP", run_cpp),
]


def _run_enabled_bindings(
    artifact_dir: Path, in_scope: set[str] | None
) -> tuple[list[MutationReport], dict[str, float]]:
    """Run each enabled, in-scope binding; archive its JSON; collect reports and wall times.

    A binding is skipped when its explicit skip env var is set, or when diff
    scoping is active (``in_scope is not None``) and the binding is out of scope.
    Each skip is logged so a scoped run is never silent about what it did not
    run — a gate's claim is only as good as its record of what it covered.
    """
    reports: list[MutationReport] = []
    # Wall seconds per binding that ran, so the budget a CI job gives a lane is
    # read off a measurement rather than guessed -- the number nobody had when
    # a lane was killed by its own wall clock.
    elapsed: dict[str, float] = {}
    for name, skip_var, runner in RUNNERS:
        if os.environ.get(skip_var) == "1":
            _ = sys.stderr.write(f"[mutation] skip {name}: {skip_var}=1\n")
            continue
        if in_scope is not None and name not in in_scope:
            _ = sys.stderr.write(
                f"[mutation] skip {name}: no change under {_BINDING_DIRS[name]} (diff-scoped)\n"
            )
            continue
        started = time.monotonic()
        rep = runner(artifact_dir)
        elapsed[name] = round(time.monotonic() - started, 1)
        _ = sys.stderr.write(f"[mutation] {name} finished in {elapsed[name]}s\n")
        sys.stderr.flush()
        (artifact_dir / f"{rep.binding}.json").write_text(json.dumps(rep.to_dict(), indent=2))
        reports.append(rep)
    return reports, elapsed


def drift_for(
    rep: MutationReport,
    bindings: dict[str, BindingSpec],
    survivor_rows: dict[SurvivorKey, int] | None = None,
) -> DriftEntry:
    """Compute one binding's drift verdict against its YAML baseline.

    ``survivor_rows`` are the run's survivors by identity where the tool
    reports them; with a ``survivors_ledger`` in the baseline, each must be a
    recorded row.
    """
    if rep.error:
        return {"status": "error", "error": rep.error}
    spec_baseline = bindings.get(rep.binding, {}).get("baseline", {})
    # A mutant that timed out is neither killed nor survived, so a sweep that
    # timed out on nearly all of them reports no survivors and full efficacy.
    # That is what a loaded machine produces, and it is indistinguishable from a
    # clean run by the survivor count alone, so the ceiling is checked first.
    ceiling = spec_baseline.get("timeout_ceiling")
    if ceiling is not None and rep.timeouts is not None and rep.timeouts > ceiling:
        return {
            "status": "regression",
            "observed_survivors": rep.survived,
            "observed_timeouts": rep.timeouts,
            "timeout_ceiling": ceiling,
        }
    baseline = spec_baseline.get("survivors")
    if baseline is None:
        return {"status": "first_run", "observed_survivors": rep.survived}
    if rep.survived > baseline:
        return {
            "status": "regression",
            "observed_survivors": rep.survived,
            "baseline_survivors": baseline,
            "delta": rep.survived - baseline,
        }
    entry: DriftEntry = {
        "status": "ok",
        "observed_survivors": rep.survived,
        "baseline_survivors": baseline,
    }
    ledger = spec_baseline.get("survivors_ledger")
    if ledger is None or survivor_rows is None:
        return entry
    recorded = ledger_to_rows(ledger)
    observed = collections.Counter(survivor_rows)
    unrecorded = rows_to_ledger(dict(observed - collections.Counter(recorded)))
    stale = rows_to_ledger(dict(collections.Counter(recorded) - observed))
    if stale:
        entry["stale_ledger"] = stale
    if unrecorded:
        entry["status"] = "regression"
        entry["unrecorded_survivors"] = unrecorded
    return entry


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

    in_scope = bindings_in_scope(REPO_ROOT)
    if in_scope is None:
        _ = sys.stderr.write("[mutation] diff-scope: running ALL bindings\n")
    else:
        _ = sys.stderr.write(
            f"[mutation] diff-scope: changed bindings only → {sorted(in_scope) or 'NONE'}\n"
        )
    reports, elapsed = _run_enabled_bindings(artifact_dir, in_scope)

    # Drift gate: compare each binding's survived count to the baseline in
    # the YAML spec.  null baseline = first run, no gating yet.  Otherwise,
    # observed > baseline = lane fails.
    drift: dict[str, DriftEntry] = {}
    for rep in reports:
        rows = cpp_survivor_rows(artifact_dir) if rep.binding == "cpp" else None
        drift[rep.binding] = drift_for(rep, bindings, rows)
    any_drift = any(entry["status"] in ("error", "regression") for entry in drift.values())

    summary = {
        "commit": sha,
        "artifact_dir": str(artifact_dir.relative_to(REPO_ROOT)),
        "diff_scope": "all" if in_scope is None else sorted(in_scope),
        "elapsed_s": elapsed,
        "runs": [r.to_dict() for r in reports],
        "drift": drift,
        "passed": not any_drift,
    }
    return write_and_report_summary(artifact_dir, summary)


if __name__ == "__main__":
    sys.exit(main())
