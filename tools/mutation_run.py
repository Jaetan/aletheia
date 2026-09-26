# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Dynamic mutation-testing runner.

Drives each binding's mutation tool in turn (mutmut for Python, gremlins for
Go, Mull for C++ in ``tools/mutation_cpp.py``, cargo-mutants for Rust in
``tools/mutation_rust.py``), parses tool-specific output
into a normalized ``MutationReport`` shape (``tools/mutation_report.py``), and
archives per-binding JSON to ``benchmarks/mutation/<short_sha>/``.

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

An ``unobserved_ledger`` is held the same way, over the kills no test observes
by behaviour: the mutants the C++ lane attributes to a check the standard
library runs in the mutation build or to a bare signal, where the suite
reports nothing before the process stops.  A row the record does not name
fails the lane, because a line whose mutation runs into an operation the
language does not define, with no test saying so, is a gap somebody has to
look at rather than a number to carry.

A ``not_covered`` count and a ``not_covered_ledger`` are held for the Go
lane, whose tool reports the mutants on lines no test executes: a run with
more of them than the record fails, and each one is keyed on its source line
as a survivor is and must be a recorded row, the rows being the lines coverage
cannot attribute to a test, a package-level constant being the case.  A line
that lost its test is then a finding of this lane, not a number that drifted.

Per-binding env contract:

  - ALETHEIA_MUTATION_CHECK    set to anything truthy by run_ci.py to enable
                               this lane (run_ci.py only invokes us when the
                               env var or `--mutation` flag is set; this
                               script does NOT re-check the env var).

Optional per-binding skip (useful for partial runs in CI lanes):

  - ALETHEIA_MUTATION_SKIP_PYTHON=1
  - ALETHEIA_MUTATION_SKIP_GO=1
  - ALETHEIA_MUTATION_SKIP_CPP=1
  - ALETHEIA_MUTATION_SKIP_RUST=1

The C++ lane in stages, so CI can sweep its two trees on two machines:

  - ALETHEIA_MUTATION_CPP_STAGE  unset: both trees are swept in this process
                               and merged, the whole lane in one run.
                               ``leak`` or ``plain``: that tree alone is
                               swept, a leg, and the run passes when the
                               tree built, swept and wrote its reports; a
                               leg judges no survivor, since a mutant is a
                               survivor of the lane only where every tree
                               let it live.  ``merge``: nothing is swept;
                               the legs' reports are read from the directory
                               ALETHEIA_MUTATION_CPP_LEGS names (searched
                               recursively, one copy of each report), merged,
                               and gated as the whole lane is.
  - ALETHEIA_MUTATION_CPP_LEGS   that directory, read by the merge stage only.

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
    rust.json      same shape
    rust/mutants.out/
                   cargo-mutants' own report directory: outcomes.json, every
                   Rust mutant with its bucket and its site, which the ledger
                   check reads, and a log per mutant
    cpp-leak.json, cpp-plain.json
                   one leg's census where the run is one leg of the C++
                   lane (ALETHEIA_MUTATION_CPP_STAGE); recorded, not gated
    cpp-legs.json  each leg's wall clock, written by the merge stage
    cpp-mull.json  Mull's Elements report: every C++ mutant with its status
                   and site, which the ledger check reads
    cpp-mull-<lane>.json
                   one tree's Elements report, what the merge reads
    cpp-mull-<lane>.txt
                   Mull's IDE report of that tree, its summary
    cpp-mull-<lane>.sqlite
                   Mull's SQLite report of one tree: each mutant's exit
                   status and the test binary's output, which the kill-route
                   census (tools/mutation_routes.py) reads
    cpp-routes.json
                   that census: the C++ mutants counted by what killed them
    cpp-unobserved.json
                   the kills no test observes by behaviour, in the shape the
                   baseline's unobserved_ledger carries, which the drift gate
                   reads back and a re-take copies
    summary.json   {commit, runs: [...], passed: bool, baseline_drift: {...}}

Usage:
  ALETHEIA_MUTATION_CHECK=1 python3 tools/mutation_run.py

The static counterpart is ``tools/check_mutation_setup.py``, which gates on
each binding's hot-path source files existing per ``docs/MUTATION_BENCH.yaml``.
"""

from __future__ import annotations

import collections
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

from tools._common import (
    find_executable,
    prepare_artifact_dir,
    run_capture,
    run_streaming,
    short_sha,
    write_and_report_summary,
)
from tools.mutation_cpp import cpp_survivor_rows, cpp_unobserved_rows, run_cpp
from tools.mutation_cpp_legs import is_cpp_leg
from tools.mutation_report import (
    SPEC_PATH,
    Baseline,
    BindingSpec,
    DriftEntry,
    LedgerRow,
    MutationReport,
    SurvivorKey,
    UnobservedKey,
    load_spec,
    unobserved_ledger_to_rows,
    unobserved_rows_to_ledger,
)
from tools.mutation_rust import run_rust, rust_survivor_rows

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

REPO_ROOT = Path(__file__).resolve().parent.parent
ARTIFACT_BASE = REPO_ROOT / "benchmarks" / "mutation"

# Exit codes (mirrors the CHANGELOG / stability runners' convention).
SPEC_ERROR_EXIT = 2


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


# One mutant gremlins made on a line no test executes, as its log names it.
_NOT_COVERED_RE = re.compile(r"NOT COVERED (\w+) at ([\w.]+\.go):(\d+):\d+")


def go_not_covered_rows(raw: str, repo_root: Path = REPO_ROOT) -> dict[SurvivorKey, int]:
    """Key a gremlins run's not-covered mutants on their source lines, as survivors are.

    gremlins names each by mutator, file and position; the position is turned
    into the text of the line it names, read from the tree the sweep ran on,
    so the row survives an edit above it and not an edit of it.  A file the
    tree no longer has, or a line past its end, keeps the position as text, so
    the row still fails to match a recorded one rather than vanishing.
    """
    rows: dict[SurvivorKey, int] = collections.Counter()
    lines_of: dict[str, list[str]] = {}
    for mutator, file, line in _NOT_COVERED_RE.findall(raw):
        rel = f"go/aletheia/{file}"
        if rel not in lines_of:
            source = repo_root / rel
            lines_of[rel] = (
                source.read_text(encoding="utf-8").split("\n") if source.is_file() else []
            )
        index = int(line) - 1
        text = lines_of[rel][index].strip() if 0 <= index < len(lines_of[rel]) else f"line {line}"
        rows[(mutator, rel, text)] += 1
    return rows


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
BINDING_DIRS: dict[str, str] = {
    "python": "python/",
    "go": "go/",
    "cpp": "cpp/",
    "rust": "rust/",
}

# A change under any of these can alter the shared ``.so`` every binding dlopens,
# or this harness / the baselines themselves — so it forces ALL bindings.  This
# set IS precision-sensitive: a miss here under-scopes (the dangerous direction),
# unlike the generous per-binding dirs above.
# What makes the kernel every binding loads: a change here moves every
# binding's result in this lane and in the coverage lane alike.
KERNEL_PATHS: tuple[str, ...] = (
    "src/",  # Agda → MAlonzo → libaletheia-ffi.so (every binding dlopens it)
    "haskell-shim/",  # FFI shim → .so
    "Shakefile.hs",  # build graph → .so
    "shake.cabal",
    "aletheia.agda-lib",
)
_GLOBAL_MUTATION_PATHS: tuple[str, ...] = (
    *KERNEL_PATHS,
    # The harness, every module of it: the runner, the scope question a lane
    # asks before installing a toolchain, the C++ lane, its report shapes, its
    # kill-route census and its slice partition.  A prefix rather than a list,
    # so a module the harness grows is covered the day it is tracked: a
    # harness module no global path covers is a change no lane runs on its
    # own pull request.
    "tools/mutation_",
    "tools/cpp_scratch.py",  # the C++ lane's scratch-directory reaping
    "tools/_common.py",  # the harness's shared helpers
    "docs/MUTATION_BENCH.yaml",  # the per-binding baselines the drift gate reads
    ".github/workflows/pr-heavy-lanes.yml",  # the lane definition
)

# Escape hatch: force every binding to run regardless of the diff.
_NO_DIFF_SCOPE_ENV = "ALETHEIA_MUTATION_NO_DIFF_SCOPE"


def bindings_in_scope(
    repo_root: Path,
    *,
    binding_dirs: Mapping[str, str] | None = None,
    global_paths: tuple[str, ...] = _GLOBAL_MUTATION_PATHS,
    no_scope_env: str = _NO_DIFF_SCOPE_ENV,
) -> set[str] | None:
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

    The tables default to this lane's; the coverage lane
    (``tools/coverage_run.py``) passes its own, so one reading of the diff
    serves both and a fourth binding is one more row rather than a second
    function.
    """
    if binding_dirs is None:
        binding_dirs = BINDING_DIRS
    if os.environ.get(no_scope_env) == "1":
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
    if any(line.startswith(global_paths) for line in changed):
        return None
    return {
        binding
        for binding, prefix in binding_dirs.items()
        if any(line.startswith(prefix) for line in changed)
    }


# (binding-name, skip-env-var, runner) per binding, in the order reports are produced.
RUNNERS: list[tuple[str, str, Callable[[Path], MutationReport]]] = [
    ("python", "ALETHEIA_MUTATION_SKIP_PYTHON", run_python),
    ("go", "ALETHEIA_MUTATION_SKIP_GO", run_go),
    ("cpp", "ALETHEIA_MUTATION_SKIP_CPP", run_cpp),
    ("rust", "ALETHEIA_MUTATION_SKIP_RUST", run_rust),
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
                f"[mutation] skip {name}: no change under {BINDING_DIRS[name]} (diff-scoped)\n"
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


def _ungated(rep: MutationReport) -> DriftEntry | None:
    """Return the verdict no baseline enters into, or None where one does.

    A leg is one tree: a mutant it let live may die in the other tree, so its
    count is recorded and the merge is what is gated.
    """
    if rep.error:
        return {"status": "error", "error": rep.error}
    if is_cpp_leg(rep.binding):
        return {"status": "leg", "observed_survivors": rep.survived}
    return None


def drift_for(
    rep: MutationReport,
    bindings: dict[str, BindingSpec],
    survivor_rows: dict[SurvivorKey, int] | None = None,
    unobserved_rows: dict[UnobservedKey, int] | None = None,
    not_covered_rows: dict[SurvivorKey, int] | None = None,
) -> DriftEntry:
    """Compute one binding's drift verdict against its YAML baseline.

    ``survivor_rows`` are the run's survivors by identity where the tool
    reports them; with a ``survivors_ledger`` in the baseline, each must be a
    recorded row.  ``unobserved_rows`` are the kills no test observes by
    behaviour, held to an ``unobserved_ledger`` the same way: a row the record
    does not name fails the lane, because a line whose mutation runs into an
    operation the language does not define, with no test saying so, is a gap
    somebody has to look at rather than a number to carry.  ``not_covered_rows``
    are the mutants on lines no test executes, held to a ``not_covered`` count
    and a ``not_covered_ledger`` the same way again.
    """
    ungated = _ungated(rep)
    if ungated is not None:
        return ungated
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
    _judge_not_covered(entry, spec_baseline, not_covered_rows)
    _judge_unobserved(entry, spec_baseline, unobserved_rows)
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


def _judge_not_covered(
    entry: DriftEntry,
    spec_baseline: Baseline,
    not_covered_rows: dict[SurvivorKey, int] | None,
) -> None:
    """Hold the run's not-covered mutants to the record, by count and by row.

    The count is the rows' sum, one per mutant the tool named.  More of them
    than recorded is a line that lost its test and fails the lane; so does a
    row the ledger does not name, at any count.  A recorded row the run no
    longer produces is reported and does not fail, a line that gained a test
    being an improvement the record follows.
    """
    recorded_count = spec_baseline.get("not_covered")
    if recorded_count is not None and not_covered_rows is not None:
        observed_count = sum(not_covered_rows.values())
        entry["observed_not_covered"] = observed_count
        entry["baseline_not_covered"] = recorded_count
        if observed_count > recorded_count:
            entry["status"] = "regression"
    ledger = spec_baseline.get("not_covered_ledger")
    if ledger is None or not_covered_rows is None:
        return
    recorded = collections.Counter(ledger_to_rows(ledger))
    observed = collections.Counter(not_covered_rows)
    stale = rows_to_ledger(dict(recorded - observed))
    unrecorded = rows_to_ledger(dict(observed - recorded))
    if stale:
        entry["stale_not_covered_ledger"] = stale
    if unrecorded:
        entry["status"] = "regression"
        entry["unrecorded_not_covered"] = unrecorded


def _judge_unobserved(
    entry: DriftEntry,
    spec_baseline: Baseline,
    unobserved_rows: dict[UnobservedKey, int] | None,
) -> None:
    """Hold the run's unobserved kills to the recorded ledger, both ways.

    A row the record does not name fails the lane, as an unrecorded survivor
    does.  A recorded row the run no longer produces is reported and does not
    fail: a test that learned to observe a kill is an improvement, and the
    change that made it lowers the record.  The probe over this ledger refuses
    that direction too, so a stale row is not carried quietly.
    """
    ledger = spec_baseline.get("unobserved_ledger")
    if ledger is None or unobserved_rows is None:
        return
    recorded = collections.Counter(unobserved_ledger_to_rows(ledger))
    observed = collections.Counter(unobserved_rows)
    stale = unobserved_rows_to_ledger(dict(recorded - observed))
    unrecorded = unobserved_rows_to_ledger(dict(observed - recorded))
    if stale:
        entry["stale_unobserved_ledger"] = stale
    if unrecorded:
        entry["status"] = "regression"
        entry["unrecorded_unobserved_kills"] = unrecorded


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
        is_cpp = rep.binding == "cpp"
        rows = cpp_survivor_rows(artifact_dir) if is_cpp else None
        if rep.binding == "rust":
            rows = rust_survivor_rows(artifact_dir)
        unobserved = cpp_unobserved_rows(artifact_dir) if is_cpp else None
        not_covered = go_not_covered_rows(rep.raw_log) if rep.binding == "go" else None
        drift[rep.binding] = drift_for(rep, bindings, rows, unobserved, not_covered)
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
