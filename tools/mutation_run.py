# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Dynamic mutation-testing runner.

Drives each binding's mutation tool in turn (mutmut for Python, gremlins for
Go, Mull for C++ in ``tools/mutation_cpp.py``, cargo-mutants for Rust in
``tools/mutation_rust.py``), parses tool-specific output
into a normalized ``MutationReport`` shape (``tools/mutation_report.py``), and
archives per-binding JSON to ``benchmarks/mutation/<short_sha>/``.

Drift gate: each binding's report is held to its baseline in
``docs/MUTATION_BENCH.yaml``, exactly and both ways: any new survivor is a
finding per AGENTS.md cat 14(g) "an unjustified survivor is a test gap".  A
run worse than the record is a ``regression`` and a run better than it is
``stale``; both fail the lane, so the change that improves the tree lowers
the record in the same commit and the record never names a figure no run
gives.  The survivor count and ``total_mutants`` are held for every binding,
and ``generated`` where the tool reports buckets beyond killed, survived and
timed out.  Where the baseline carries a ``survivors_ledger``, every survivor
must be one of its rows, by mutator, repository-relative file and
source-line text, up to the count the row records, and every row a survivor:
a survivor traded for another leaves the count unchanged and fails the lane
all the same.  The C++ census by kill route is held to ``kill_routes``, and
every file the C++ ``hot_path`` names must hold a mutant.

An ``unobserved_ledger`` is held the same way, over the kills no test observes
by behaviour: the mutants the C++ lane attributes to a check the standard
library runs in the mutation build or to a bare signal, where the suite
reports nothing before the process stops.  A row the record does not name
fails the lane, because a line whose mutation runs into an operation the
language does not define, with no test saying so, is a gap somebody has to
look at rather than a number to carry; a recorded row the run no longer
produces is a stale record.

A ``not_covered`` count and a ``not_covered_ledger`` are held for the Go
lane, whose tool reports the mutants on lines no test executes: a run with
more or fewer of them than the record fails, and each one is keyed on its
source line as a survivor is and must be a recorded row, and every row one
the run produces, the rows being the lines coverage cannot attribute to a
test, a package-level constant being the case.  A line that lost its test is
then a finding of this lane, not a number that drifted.

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

The C++ lane in legs, so CI can sweep the tree in slices across machines
(``tools/mutation_cpp.py``):

  - ALETHEIA_MUTATION_CPP_STAGE  unset: the tree is swept whole in this
                               process, the whole lane in one run.  A slice
                               number: the surface's files are cut on their
                               recorded suite runs and this slice's files
                               alone are swept, a leg; the run passes when
                               the leg built, swept and wrote its reports,
                               and a leg judges no survivor.  ``merge``:
                               nothing is swept; every slice is read from
                               the directory ALETHEIA_MUTATION_CPP_LEGS names
                               (searched recursively, one copy of each
                               report), the slices unioned and refused below
                               the recorded census, and gated as the whole
                               lane is; a leg swept whole is no part of the
                               merge.
  - ALETHEIA_MUTATION_CPP_LEGS   that directory, read by the merge stage only.

The Go lane in shards, so CI can sweep the package's files across machines
(``tools/mutation_go.py``):

  - ALETHEIA_MUTATION_GO_STAGE   unset: the package is swept whole in this
                               process.  A shard number: the package's files
                               are cut on their sizes and this shard's files
                               alone are swept, after which a dry run under
                               the package's own configuration takes the
                               whole package's census; a shard judges no
                               survivor.  ``merge``:
                               nothing is swept; the shards' records and logs
                               are read from the directory
                               ALETHEIA_MUTATION_GO_SHARDS names, held to the
                               census the shards took, and gated as the whole
                               package is.
  - ALETHEIA_MUTATION_GO_SHARDS  that directory, read by the merge stage only.

The Rust lane over two jobs, so CI sweeps the crate on two machines, each
running four shards side by side (``tools/mutation_rust.py``):

  - ALETHEIA_MUTATION_RUST_STAGE unset: the crate is swept whole in this
                               process, one shard per CPU up to four.  A job
                               number: its four of the jobs' eight shards are
                               swept, and the listing kept beside them; a job
                               judges no survivor.  ``merge``: nothing is
                               swept; the jobs' shards are read from the
                               directory ALETHEIA_MUTATION_RUST_JOBS names,
                               held to one listing of this commit, and gated
                               as the whole crate is.
  - ALETHEIA_MUTATION_RUST_JOBS  that directory, read by the merge stage only.

Diff scoping (automatic): on a PR branch only the binding(s) whose directory the
diff vs ``main`` touches are run; the rest are skipped, since an unchanged
binding's survivor count is unchanged from its baseline by construction.  A
change to a shared artifact (the Agda ``src/`` → ``.so``, this harness, or
``docs/MUTATION_BENCH.yaml``) forces ALL bindings, as does push:main / an empty
diff (the post-merge backstop).  Set ``ALETHEIA_MUTATION_NO_DIFF_SCOPE=1`` to
force the full run regardless.  See ``bindings_in_scope``.

Artifacts written:

  benchmarks/mutation/<short_sha>/
    python.json    {binding, tool, total_mutants, killed, survived, timeouts,
                   generated, routes, mutated_files, score_pct, raw_log_tail,
                   error}, null where the tool has no such figure
    go.json        same shape
    go-1.json, go-1.raw.txt, go-shard-1.json
                   one shard's census, log and record (the dry run's census,
                   the domain and the shard's files) where the run is one
                   shard of the Go lane (ALETHEIA_MUTATION_GO_STAGE); recorded,
                   not gated
    go-shards.json each shard's wall clock, written by the merge stage
    cpp.json       same shape
    rust.json      same shape
    rust/mutants.out/outcomes.json
                   the shards' outcomes merged: every Rust mutant with its
                   bucket and its site, which the ledger check reads
    rust/shard-<n>/mutants.out/, rust-shard-<n>.raw.txt
                   one shard's own cargo-mutants report directory, a log per
                   mutant in it, and the shard's console log
    rust-1.json, rust-1.raw.txt, rust-listing.json
                   one job's report, log and the listing it swept its shards
                   of, where the run is one job of the Rust lane
                   (ALETHEIA_MUTATION_RUST_STAGE); recorded, not gated
    cpp-<leg>.json one leg's census where the run is one leg of the C++
                   lane (ALETHEIA_MUTATION_CPP_STAGE), the leg named by its
                   slice, cpp-1.json and its siblings (cpp.json for the tree
                   swept whole); recorded, not gated
    cpp-legs.json  each leg's wall clock, written by the merge stage
    cpp-mull.json  Mull's Elements report: every C++ mutant with its status
                   and site, which the ledger check reads
    cpp-mull-<leg>.json
                   one leg's Elements report, the tree or one slice of it,
                   what the merge reads
    cpp-mull-<leg>.txt
                   Mull's IDE report of that leg, its summary
    cpp-mull-<leg>.sqlite
                   Mull's SQLite report of one leg: each mutant's exit
                   status and the test binary's output, which the kill-route
                   census (tools/mutation_routes.py) reads
    cpp-mull-<leg>.runs.json
                   the suite runs that leg's mutants cost by file, which the
                   leg writes (tools/mutation_cpp_runs.py)
    cpp-runs.json  the suite runs by file, summed over the legs: what the
                   recorded slice weights are re-taken from
    cpp-routes.json
                   that census: the C++ mutants counted by what killed them
    cpp-unobserved.json
                   the kills no test observes by behaviour, in the shape the
                   baseline's unobserved_ledger carries, which the drift gate
                   reads back and a re-take copies
    summary.json   {commit, runs: [...], passed: bool, baseline_drift: {...}}

Usage:
  python/.venv/bin/python -m tools.mutation_run

The static counterpart is ``tools/check_mutation_setup.py``, which gates on
each binding's hot-path source files existing per ``docs/MUTATION_BENCH.yaml``.
"""

from __future__ import annotations

import argparse
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
from typing import TYPE_CHECKING, Literal, NewType

from tools._common import (
    RelPath,
    find_executable,
    prepare_artifact_dir,
    run_capture,
    run_streaming,
    short_sha,
    write_and_report_summary,
)
from tools.mutation_cpp import cpp_survivor_rows, cpp_unobserved_rows, run_cpp
from tools.mutation_cpp_legs import is_cpp_leg
from tools.mutation_go import (
    GO_CONFIG,
    GO_LANE,
    GO_MERGE_STAGE,
    GO_RAW_LOG,
    Binding,
    GremlinsLog,
    ShortSha,
    cut_go_shard,
    go_refusal,
    go_stage,
    is_go_shard,
    merge_go_shards,
    parse_gremlins_summary,
    record_go_shard,
    shard_binding,
    shard_log_name,
)
from tools.mutation_report import (
    SPEC_PATH,
    Baseline,
    BindingSpec,
    DriftEntry,
    LedgerRow,
    MutantCount,
    MutationReport,
    Observed,
    RouteCensus,
    SurvivorKey,
    UnobservedKey,
    load_spec,
    scratch_tree_or_report,
    unobserved_ledger_to_rows,
    unobserved_rows_to_ledger,
)
from tools.mutation_rust import RustBinding, is_rust_job, run_rust, rust_survivor_rows

from aletheia.common_types import Prose

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

    (`mutmut results` lists ONLY the non-killed mutants, one per line,
    ``module.x__mutmut_K: survived``, so the killed count is NOT recoverable
    from ``results`` alone; the run summary is the only source for killed.)

    Primary: parse the last emoji summary.  Fallback (summary shape changed):
    count the per-mutant ``: survived`` / ``: no tests`` lines from ``results``;
    that keeps the gate-critical SURVIVOR count correct even if the killed
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
    # kill/survive verdicts on SOURCE changes, NOT on TEST changes (test files
    # are not in ``source_paths``, so their content is not tracked).  A test
    # edit, or files arriving via ``git merge`` / ``checkout`` / ``pull``,
    # therefore yields stale verdicts (observed live: a merge that added a
    # function plus its killing tests reported 20 phantom survivors until the
    # tree was cleared).  Erasing it makes this local gate reproduce CI's
    # fresh-checkout semantics exactly: CI already starts from a clean checkout
    # (``mutants/`` is gitignored and uncached), so this is a no-op there.  Cost
    # is local only: ~11 s on the Python lane (warm reuse 29 s -> clean 40 s).
    shutil.rmtree(cwd / "mutants", ignore_errors=True)
    # mutmut keeps ALL state under mutants/: the mutated tree, the copied
    # tests/ (the piece that goes stale), and the mutmut-stats.json results.  It
    # has no separate .mutmut/ cache, so the erase above is complete.  Run
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
    return MutationReport(
        "python",
        "mutmut",
        counts.killed,
        counts.survived,
        raw,
        observed=Observed(timeouts=counts.timeout),
    )


def run_go(artifact_dir: Path) -> MutationReport:
    """Run gremlins on the Go aletheia/ package and parse its tail summary.

    Output is a text summary with ``Killed``, ``Lived`` (= survived),
    ``Not covered`` and ``Mutator coverage`` lines.

    AGENTS.md cat 14(g) names go-mutesting / gomut / mutate; ``gremlins``
    is the actively-maintained successor (zimmski's repo is unmaintained
    since 2021 and panics on Go 1.26 internals).  Same operator set, same
    intent, just a different implementation.

    gremlins tests each mutant in a copy of the ``go/`` module alone, under
    the system's temporary directory, where nothing outside the module is.
    The package's tests read the documents, the corpus and the kernel's
    header from the repository, and load the kernel, so the lane names both:
    ``ALETHEIA_REPO_ROOT`` a scratch copy of the whole tree, which the sweep
    runs from (``scratch_worktree``), and ``ALETHEIA_LIB`` the tree's own
    built library, which the copy does not carry.  Without them every test
    that reads the repository fails in gremlins' copy, and every mutant reads
    as killed whatever it changed.  The doc-example harness is skipped
    (``go_sweep_goflags``).

    The stage (``go_stage``) selects the whole package, one shard of it, or
    the merge of the shards' sweeps (``tools/mutation_go.py``).
    """
    try:
        stage = go_stage()
    except ValueError as exc:
        return go_refusal(GO_LANE, Prose(str(exc)))
    if stage == GO_MERGE_STAGE:
        return merge_go_shards(artifact_dir, ShortSha(short_sha(REPO_ROOT)))
    binding = GO_LANE if stage is None else shard_binding(stage)
    tools = _go_tools(binding)
    if isinstance(tools, MutationReport):
        return tools
    gremlins, lib = tools
    header = Prose("")
    with scratch_tree_or_report(REPO_ROOT, "go", "gremlins") as tree:
        if isinstance(tree, MutationReport):
            return tree
        env = dict(os.environ)
        env["ALETHEIA_REPO_ROOT"] = str(tree)
        env["ALETHEIA_LIB"] = str(lib)
        env["GOFLAGS"] = go_sweep_goflags(GoFlags(env.get("GOFLAGS", "")))
        # gremlins targets the package directory and runs the package's tests
        # against each mutant: the canonical aletheia/ subpackage, the only Go
        # module holding runtime code.
        cut = None if stage is None else cut_go_shard(tree, stage)
        proc = run_streaming([str(gremlins), "unleash", "./aletheia"], cwd=tree / "go", env=env)
        if stage is not None and cut is not None:
            # The census comes after the sweep, under the package's own
            # configuration: before it, the dry run would leave the package
            # compiled for the coverage run gremlins times every mutant by
            # (tools/mutation_go.py).
            _ = (tree / GO_CONFIG).write_text(cut.package_config, encoding="utf-8")
            dry = run_capture(
                [str(gremlins), "unleash", "--dry-run", "./aletheia"], cwd=tree / "go", env=env
            )
            recorded = record_go_shard(stage, cut, GremlinsLog(dry.stdout), artifact_dir)
            if recorded is None:
                return go_refusal(
                    binding,
                    Prose(f"the dry run listed no mutant (exit {dry.returncode}):\n{dry.stderr}"),
                    GremlinsLog(proc.stdout),
                )
            header = recorded
    raw = header + proc.stdout
    _ = (artifact_dir / (GO_RAW_LOG if stage is None else shard_log_name(stage))).write_text(raw)

    return parse_gremlins_summary(GremlinsLog(raw), Prose(f"exit {proc.returncode}"), binding)


def _go_tools(binding: Binding) -> tuple[Path, Path] | MutationReport:
    """Find gremlins and the built kernel library, or report which of them is missing."""
    found = shutil.which("gremlins")
    if found is None:
        return go_refusal(
            binding,
            Prose(
                "gremlins not in PATH; run "
                + "`go install github.com/go-gremlins/gremlins/cmd/gremlins@latest`"
            ),
        )
    lib = REPO_ROOT / "build" / "libaletheia-ffi.so"
    if not lib.is_file():
        return go_refusal(
            binding,
            Prose(f"libaletheia-ffi.so not found at {lib}; run `cabal run shake -- build` first"),
        )
    return Path(found), lib


# The flags the go command reads from its environment, as GOFLAGS spells them.
GoFlags = NewType("GoFlags", str)

# The Go doc-example harness, which builds and runs every Go fence of the
# documents as a program of its own: it holds the documents to the package,
# the unit tests hold the package's behaviour, and the sweep skips it rather
# than pay its whole run once per mutant.
GO_DOC_HARNESS = "TestDocExamples"


def go_sweep_goflags(caller: GoFlags) -> GoFlags:
    """Return the caller's ``GOFLAGS`` with test caching off and the doc-example harness skipped.

    ``go test`` reads both from ``GOFLAGS``, the one route to a test flag
    gremlins leaves open, and its coverage run and every mutant's run inherit
    them alike.  gremlins times its coverage run and stops each mutant's run
    at three times that, so a coverage run served from the test cache, as one
    is after a dry run of the same tree, stops every mutant before its tests
    end: measured on one shard, 362 of 382 mutants timed out.
    """
    return GoFlags(f"{caller} -count=1 -skip=^{GO_DOC_HARNESS}$".strip())


# One mutant gremlins reported, by the verdict its log line opens with.
_GO_MUTANT_RE = re.compile(r"(NOT COVERED|LIVED) (\w+) at ([\w.]+\.go):(\d+):\d+")


def go_mutant_rows(
    raw: str, verdict: Literal["NOT COVERED", "LIVED"], repo_root: Path = REPO_ROOT
) -> dict[SurvivorKey, int]:
    """Key a gremlins run's mutants of one verdict on their source lines.

    The verdict is the one the log line opens with: ``LIVED`` for a survivor,
    ``NOT COVERED`` for a mutant on a line no test executes.  gremlins names
    each by mutator, file and position; the position is turned into the text
    of the line it names, read from the tree the sweep ran on, so the row
    survives an edit above it and not an edit of it.  A file the tree no
    longer has, or a line past its end, keeps the position as text, so the row
    still fails to match a recorded one rather than vanishing.
    """
    rows: dict[SurvivorKey, int] = collections.Counter()
    lines_of: dict[str, list[str]] = {}
    for found, mutator, file, line in _GO_MUTANT_RE.findall(raw):
        if found != verdict:
            continue
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
# mutation config changed, OR if a shared artifact every binding depends on
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
# costs time, so per-binding we scope generously.
BINDING_DIRS: dict[str, str] = {
    "python": "python/",
    "go": "go/",
    "cpp": "cpp/",
    "rust": "rust/",
}

# A change under any of these can alter the shared ``.so`` every binding dlopens,
# or this harness / the baselines themselves, so it forces ALL bindings.  This
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
    "tools/_resources.py",  # the CPU budget the C++ lane builds with
    "tools/__init__.py",  # the package every harness module is imported through
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

    Returns ``None`` (meaning "run ALL bindings", the fail-SAFE answer) when:

      * the escape-hatch env var is set,
      * git is absent / the diff cannot be computed (no ``git`` binary, no
        ``main`` ref, git error),
      * the diff is EMPTY (push:main / on-main: ``HEAD == main``, the
        cache-seeding + post-merge backstop run), or
      * any GLOBAL path changed (shared ``.so`` / harness / baselines).

    Otherwise returns the set of bindings whose directory the diff touched,
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
        return None  # no `git` binary on PATH: fail safe to the full run
    result = run_capture(
        [git, "-C", str(repo_root), "diff", "--name-only", "main...HEAD"],
    )
    if result.returncode != 0:
        return None  # no `main` ref / git error: fail safe to the full run
    changed = [line for line in result.stdout.splitlines() if line]
    if not changed:
        return None  # push:main / no diff: run the full backstop
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
    run: a gate's claim is only as good as its record of what it covered.
    """
    reports: list[MutationReport] = []
    # Wall seconds per binding that ran, so the budget a CI job gives a lane is
    # read off a measurement rather than guessed, a measurement nobody had when
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

    A C++ leg is one slice of the tree: its count is recorded and the merge
    over the slices is what is gated.
    A Go shard is one part of the package, and a Rust job one part of the
    crate's sweep, each judged with the others by the merge in the same way.
    """
    if rep.error:
        return {"status": "error", "error": rep.error}
    if (
        is_cpp_leg(rep.binding)
        or is_go_shard(Binding(rep.binding))
        or is_rust_job(RustBinding(rep.binding))
    ):
        return {"status": "leg", "observed_survivors": rep.survived}
    return None


def _fail(entry: DriftEntry, status: Literal["regression", "stale"]) -> None:
    """Mark the run off its record, a regression outranking a stale record."""
    if entry["status"] != "regression":
        entry["status"] = status


def drift_for(
    rep: MutationReport,
    bindings: dict[str, BindingSpec],
    survivor_rows: dict[SurvivorKey, int] | None = None,
    unobserved_rows: dict[UnobservedKey, int] | None = None,
    not_covered_rows: dict[SurvivorKey, int] | None = None,
) -> DriftEntry:
    """Compute one binding's drift verdict against its YAML baseline.

    The record is a measurement of the tree, held exactly both ways: a run
    worse than the record is a regression, and a run better than it is a
    stale record, which fails too, so the change that improves the tree
    lowers the record in the same commit and the record never names a figure
    no run gives.  ``survivor_rows`` are the run's survivors by identity where
    the tool reports them, held to a ``survivors_ledger``.  ``unobserved_rows``
    are the kills no test observes by behaviour, held to an
    ``unobserved_ledger``: a line whose mutation runs into an operation the
    language does not define, with no test saying so, is a gap somebody has
    to look at rather than a number to carry.  ``not_covered_rows`` are the
    mutants on lines no test executes, held to a ``not_covered`` count and a
    ``not_covered_ledger``.  The report's own counts are held too: the
    mutants judged, every mutant the tool made, the C++ census by kill route,
    and the files it made a mutant in, which must hold every file of the
    binding's ``hot_path``.  Where the tool makes no such observation it is
    ``None`` and holds nothing.
    """
    spec = bindings.get(rep.binding, {})
    spec_baseline = spec.get("baseline", {})
    early = _ungated(rep) or _over_ceiling(rep, spec_baseline)
    if early is not None:
        return early
    baseline = spec_baseline.get("survivors")
    if baseline is None:
        return {"status": "first_run", "observed_survivors": rep.survived}
    entry: DriftEntry = {
        "status": "ok",
        "observed_survivors": rep.survived,
        "baseline_survivors": baseline,
    }
    if rep.survived != baseline:
        entry["delta"] = rep.survived - baseline
        _fail(entry, "regression" if rep.survived > baseline else "stale")
    _judge_counts(entry, spec_baseline, rep)
    _judge_routes(entry, spec_baseline, rep.observed.routes)
    _judge_hot_path(entry, spec.get("hot_path", []), rep.observed.mutated_files)
    _judge_not_covered(entry, spec_baseline, not_covered_rows)
    _judge_unobserved(entry, spec_baseline, unobserved_rows)
    # A survivor the ledger does not name is a regression even at an unchanged
    # count; a recorded row the run no longer leaves alive is a stale record,
    # deleted by the change that kills or removes its mutant.
    ledger = spec_baseline.get("survivors_ledger")
    if ledger is None or survivor_rows is None:
        return entry
    recorded = collections.Counter(ledger_to_rows(ledger))
    observed = collections.Counter(survivor_rows)
    unrecorded = rows_to_ledger(dict(observed - recorded))
    stale = rows_to_ledger(dict(recorded - observed))
    if stale:
        entry["stale_ledger"] = stale
        _fail(entry, "stale")
    if unrecorded:
        entry["unrecorded_survivors"] = unrecorded
        _fail(entry, "regression")
    return entry


def _over_ceiling(rep: MutationReport, spec_baseline: Baseline) -> DriftEntry | None:
    """Refuse a run past the record's timeout ceiling, whatever else it reports.

    A mutant that timed out is neither killed nor survived, so a sweep whose
    timeouts hide survivors reports fewer of them than the tree has, and the
    survivor count alone cannot tell it from a clean run: the ceiling is
    checked first.
    """
    ceiling = spec_baseline.get("timeout_ceiling")
    timeouts = rep.observed.timeouts
    if ceiling is None or timeouts is None or timeouts <= ceiling:
        return None
    return {
        "status": "regression",
        "observed_survivors": rep.survived,
        "observed_timeouts": timeouts,
        "timeout_ceiling": ceiling,
    }


def _judge_counts(entry: DriftEntry, spec_baseline: Baseline, rep: MutationReport) -> None:
    """Hold the mutants the run judged, and every mutant the tool made, to the record.

    Both are the surface, a property of the source, its tests and the tool, so
    a count off the record either way is a record that no longer describes
    the tree.  A run that reports no generated count where the record holds
    one is off the record too: a count compared against nothing holds nothing.
    """
    recorded_total = spec_baseline.get("total_mutants")
    if recorded_total is not None:
        entry["observed_total_mutants"] = MutantCount(rep.total_mutants)
        entry["baseline_total_mutants"] = MutantCount(recorded_total)
        if rep.total_mutants != recorded_total:
            _fail(entry, "stale")
    recorded_generated = spec_baseline.get("generated")
    if recorded_generated is not None:
        entry["observed_generated"] = rep.observed.generated
        entry["baseline_generated"] = recorded_generated
        if rep.observed.generated != recorded_generated:
            _fail(entry, "stale")


def _judge_routes(entry: DriftEntry, spec_baseline: Baseline, routes: RouteCensus | None) -> None:
    """Hold the C++ census to the record route by route, a route one side lacks counting zero.

    A kill moving from a test to a check or a signal is a test that stopped
    observing it, which the unobserved ledger names; one moving the other way
    is a test that learned to.  Either changes what the census says, and
    either fails until the record follows.
    """
    recorded = spec_baseline.get("kill_routes")
    if recorded is None or routes is None:
        return
    if any(routes.get(r, 0) != recorded.get(r, 0) for r in routes.keys() | recorded.keys()):
        entry["observed_kill_routes"] = routes
        entry["baseline_kill_routes"] = recorded
        _fail(entry, "stale")


def _judge_hot_path(
    entry: DriftEntry, hot_path: list[RelPath], mutated_files: frozenset[RelPath] | None
) -> None:
    """Refuse a run with no mutant in a file the binding's hot path names.

    The list names the files the lane exists to mutate.  One no mutant
    reaches, because no suite the mutation build links reaches it or the
    tool drops its mutants, is surface the lane does not have.
    """
    if mutated_files is None:
        return
    missing = [path for path in hot_path if path not in mutated_files]
    if missing:
        entry["hot_path_without_mutants"] = missing
        _fail(entry, "regression")


def _judge_not_covered(
    entry: DriftEntry,
    spec_baseline: Baseline,
    not_covered_rows: dict[SurvivorKey, int] | None,
) -> None:
    """Hold the run's not-covered mutants to the record, by count and by row.

    The count is the rows' sum, one per mutant the tool named.  More of them
    than recorded is a line that lost its test, and so is a row the ledger
    does not name, at any count: a regression.  Fewer, or a recorded row the
    run no longer produces, is a line that gained a test, which lowers the
    record in the change that wrote the test.
    """
    recorded_count = spec_baseline.get("not_covered")
    if recorded_count is not None and not_covered_rows is not None:
        observed_count = sum(not_covered_rows.values())
        entry["observed_not_covered"] = observed_count
        entry["baseline_not_covered"] = recorded_count
        if observed_count != recorded_count:
            _fail(entry, "regression" if observed_count > recorded_count else "stale")
    ledger = spec_baseline.get("not_covered_ledger")
    if ledger is None or not_covered_rows is None:
        return
    recorded = collections.Counter(ledger_to_rows(ledger))
    observed = collections.Counter(not_covered_rows)
    stale = rows_to_ledger(dict(recorded - observed))
    unrecorded = rows_to_ledger(dict(observed - recorded))
    if stale:
        entry["stale_not_covered_ledger"] = stale
        _fail(entry, "stale")
    if unrecorded:
        entry["unrecorded_not_covered"] = unrecorded
        _fail(entry, "regression")


def _judge_unobserved(
    entry: DriftEntry,
    spec_baseline: Baseline,
    unobserved_rows: dict[UnobservedKey, int] | None,
) -> None:
    """Hold the run's unobserved kills to the recorded ledger, both ways.

    A row the record does not name is a regression, as an unrecorded survivor
    is.  A recorded row the run no longer produces is a stale record: a test
    that learned to observe a kill lowers the record in the change that
    taught it.
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
        _fail(entry, "stale")
    if unrecorded:
        entry["unrecorded_unobserved_kills"] = unrecorded
        _fail(entry, "regression")


def main() -> int:
    """Drive every binding's mutation tool, archive reports, gate on baseline drift."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
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

    # Drift gate: hold each binding's run to its baseline in the YAML spec.
    # A null survivor count is a first run, not gated yet; otherwise a run off
    # the record either way fails the lane.
    drift: dict[str, DriftEntry] = {}
    for rep in reports:
        is_cpp = rep.binding == "cpp"
        rows = cpp_survivor_rows(artifact_dir) if is_cpp else None
        if rep.binding == "rust":
            rows = rust_survivor_rows(artifact_dir)
        if rep.binding == "go":
            rows = go_mutant_rows(rep.raw_log, "LIVED")
        unobserved = cpp_unobserved_rows(artifact_dir) if is_cpp else None
        not_covered = go_mutant_rows(rep.raw_log, "NOT COVERED") if rep.binding == "go" else None
        drift[rep.binding] = drift_for(rep, bindings, rows, unobserved, not_covered)
    any_drift = any(entry["status"] in ("error", "regression", "stale") for entry in drift.values())

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
