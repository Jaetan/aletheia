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

The Python lane in shards, so CI can test its mutants across machines
(``tools/mutation_python.py``):

  - ALETHEIA_MUTATION_PYTHON_STAGE  unset: every mutant is tested in this
                               process.  A shard number: mutmut makes every
                               mutant and the witness deals them, this shard
                               testing the sorted names its place is dealt,
                               and the run writes the census it read beside
                               its log; a shard judges no
                               survivor.  ``merge``: nothing is tested; the
                               shards' records, logs and reports are read from
                               the directory ALETHEIA_MUTATION_PYTHON_SHARDS
                               names, held to one census, and gated as the
                               whole lane is.
  - ALETHEIA_MUTATION_PYTHON_SHARDS that directory, read by the merge stage only.

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
change to a shared artifact (the Agda ``src/`` → ``.so``, this harness, the Mull
build, or ``docs/MUTATION_BENCH.yaml``) forces ALL bindings, as does push:main / an empty
diff (the post-merge backstop).  Set ``ALETHEIA_MUTATION_NO_DIFF_SCOPE=1`` to
force the full run regardless.  See ``bindings_in_scope``.

Artifacts written:

  benchmarks/mutation/<short_sha>/
    python.json    {binding, tool, total_mutants, killed, survived, timeouts,
                   generated, routes, mutated_files, score_pct, raw_log_tail,
                   error}, null where the tool has no such figure
    python-1.json, python-1.raw.txt, python-shard-1.json
                   one shard's report, log and record (its commit, the census
                   and the mutants it judged) where the run is one shard of
                   the Python lane (ALETHEIA_MUTATION_PYTHON_STAGE); recorded,
                   not gated
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

The static counterpart is ``tools/check_mutation_setup.py``, which holds the
record and each lane's configuration to the tree without running a tool.
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

from tools._branch_diff import branch_changes
from tools._common import (
    EnvName,
    EnvValue,
    prepare_artifact_dir,
    run_capture,
    run_streaming,
    short_sha,
    write_and_report_summary,
)
from tools.mutation_cpp import cpp_survivor_rows, cpp_unobserved_rows, run_cpp
from tools.mutation_drift import drift_for
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
    gremlins_command,
    merge_go_shards,
    parse_gremlins_summary,
    record_go_shard,
    shard_binding,
    shard_log_name,
    without_gremlins_settings,
)
from tools.mutation_go_cases import sweep_go_package
from tools.mutation_python import (
    PYTHON_LANE,
    PYTHON_MERGE_STAGE,
    PYTHON_SHARDS_ENV,
    PYTHON_STAGE_ENV,
    ShardNumber,
    python_stage,
    read_exits,
    read_python_shards,
    record_python_shard,
    shard_deal,
)
from tools.mutation_python import shard_binding as python_shard_binding
from tools.mutation_report import (
    SPEC_PATH,
    CrashedMutant,
    DriftEntry,
    MutationReport,
    Observed,
    SurvivorKey,
    load_spec,
    scratch_tree_or_report,
)
from tools.mutation_rust import run_rust, rust_survivor_rows
from tools.mutation_witness import (
    LOW_HEAP_SUFFIX,
    PROCESS_MAPS,
    TALLY_FILE,
    MutantName,
    placement_env,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

REPO_ROOT = Path(__file__).resolve().parent.parent
ARTIFACT_BASE = REPO_ROOT / "benchmarks" / "mutation"

# Exit codes (mirrors the CHANGELOG / stability runners' convention).
SPEC_ERROR_EXIT = 2


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


# A mutant ``mutmut results`` lists as ending on a signal it names (``segfault``, which it
# also gives a process it killed) or on an exit it does not know (``suspicious``).
_CRASHED_MUTANT = re.compile(r"^\s*(\S+): (segfault|suspicious)$", re.MULTILINE)


def parse_mutmut(raw: str) -> MutmutCounts:
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


# A mutant's run that raises exits 255, which mutmut files as a timeout and
# keeps nothing of, and one that ends its process leaves only its exit status:
# the witness writes what each did under this directory of the lane's artifacts
# (tools/mutation_witness.py), and mutmut's own log, written under mutants/
# where its log_to_file puts it by default, is kept beside them.
WITNESS_SCRIPT = REPO_ROOT / "tools" / "mutation_witness.py"
PYTHON_WITNESS_DIR = "python-witness"
MUTMUT_LOG = "mutmut-debug.log"


# The exits mutmut files a mutant under without forking a run for it: no tests
# to run, skipped, and caught by the type check.  One never checked has none.
_NOT_RUN = frozenset({ExitStatus(33), ExitStatus(34), ExitStatus(37)})


# mutmut's progress line, whose second number counts every mutant it judged.
_MUTMUT_TOTAL = re.compile(r"(\d+)/(\d+)\s+🎉")


def python_witness_refusal(artifact_dir: Path, mutants: Path, raw: Prose) -> Prose | None:
    """Return why the witness's tally does not cover mutmut's runs, or None where it does.

    mutmut's ``.meta`` files give each mutant's exit, and they are held first to
    mutmut's own count: files naming fewer mutants than its summary counts
    would hold the tally to fewer runs than there were.  Every exit but those of
    ``_NOT_RUN`` and none comes from a child, which tallies its mutant before
    its tests start, so a name missing from the tally is a run the witness did
    not see, and it is off for every run like it.
    """
    totals = _MUTMUT_TOTAL.findall(raw)
    if not totals:
        return Prose("mutmut printed no count to hold its .meta files to, so no run was checked")
    total = int(totals[-1][1])
    exits = read_exits(mutants)
    if len(exits) < total:
        return Prose(
            f"mutmut's .meta files name {len(exits)} of the {total} mutants its summary "
            + "counts, so the witness's tally was held to no run of the others"
        )
    ran = {name for name, code in exits.items() if code not in {None, *_NOT_RUN}}
    tally = artifact_dir / PYTHON_WITNESS_DIR / TALLY_FILE
    lines = tally.read_text(encoding="utf-8").splitlines() if tally.is_file() else []
    missing = sorted(ran - {MutantName(line) for line in lines})
    if not missing:
        return None
    return Prose(
        f"the witness tallied no run of {len(missing)} mutants mutmut ran, so it is off "
        + f"(tools/mutation_witness.py), first {', '.join(missing[:3])}"
    )


def python_placement_refusal(artifact_dir: Path) -> Prose | None:
    """Return why a mutant's run may have read an address a C int cut short, or None.

    A run whose process's heap started below 2^32 as its tests ended left
    ``<mutant>.heap``: there, an address that lost its high half can still name
    its block, so a test may have passed on what crashes where it does not.
    """
    low = sorted((artifact_dir / PYTHON_WITNESS_DIR).glob(f"*{LOW_HEAP_SUFFIX}"))
    if not low:
        return None
    return Prose(
        f"{len(low)} mutants' runs ended with their heap below 2^32, where an address "
        + "cut to 32 bits still names its block: mutmut must run under "
        + f"tools/mutation_witness.py's PLACEMENT_ENV, first {low[0].stem}"
    )


def _keep_python_witnesses(artifact_dir: Path, mutants: Path, binding: Binding) -> Prose:
    """Keep mutmut's log beside the report and return each witness for the raw record.

    A ``.txt`` witness is a run that raised, which mutmut files as a timeout; a
    ``.running`` one is a run that ended its process before returning, whose
    last ``started`` line names the test it was in.  Each is named on stderr
    too, so the log of a lane that went red says where that run's cause is.
    """
    log = mutants / MUTMUT_LOG
    if log.is_file():
        _ = shutil.copy2(log, artifact_dir / f"{binding}.{MUTMUT_LOG}")
    kept = Prose("")
    witnesses = artifact_dir / PYTHON_WITNESS_DIR
    for suffix, how in ((".txt", "raised"), (".running", "ended its process before returning")):
        for witness in sorted(witnesses.glob(f"*{suffix}")):
            _ = sys.stderr.write(
                f"[mutation] python: a mutant's run {how}, witnessed in {witness}\n"
            )
            text = witness.read_text(encoding="utf-8")
            kept = Prose(f"{kept}=== {how}: {witness.name} ===\n{text}\n")
    return kept


def _crashes(results: Prose) -> tuple[CrashedMutant, ...]:
    """Name the mutants whose process a signal or an exit mutmut does not know ended."""
    return tuple(
        sorted(
            CrashedMutant(f"{name}: {status}") for name, status in _CRASHED_MUTANT.findall(results)
        )
    )


def run_python(artifact_dir: Path) -> MutationReport:
    """Mutmut run on Python hot-path; parses ``mutmut results`` summary.

    The stage (``python_stage``) selects the whole lane, one shard of it, or
    the merge of the shards' sweeps (``tools/mutation_python.py``).
    """
    try:
        stage = python_stage()
    except ValueError as exc:
        return MutationReport(PYTHON_LANE, "mutmut", 0, 0, "", error=str(exc))
    if stage == PYTHON_MERGE_STAGE:
        return merge_python_shards(artifact_dir, ShortSha(short_sha(REPO_ROOT)))
    return _sweep_python(artifact_dir, stage)


def _sweep_python(artifact_dir: Path, stage: ShardNumber | None) -> MutationReport:
    """Sweep the whole lane, or one shard of it, and report it under its binding."""
    binding = PYTHON_LANE if stage is None else python_shard_binding(stage)
    checked = _check_python_tools()
    if isinstance(checked, str):
        return MutationReport(binding, "mutmut", 0, 0, "", error=checked)
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
    # Read by python/tests/_repo_root.py: a test's ancestors under mutants/ miss the root.
    env["ALETHEIA_REPO_ROOT"] = str(REPO_ROOT)
    # Read by glibc's malloc as each process starts, where this interpreter's
    # heap lies below 2^32 (tools/mutation_witness.py).
    env |= placement_env(PROCESS_MAPS)
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
    # (ALETHEIA_LIB), and every word naming a program is an absolute path (no
    # S607).  The run goes through the witness, which mutmut's children inherit.
    witness = [str(WITNESS_SCRIPT), "--witness-dir", str(artifact_dir / PYTHON_WITNESS_DIR)]
    if stage is not None:
        witness += ["--shard", shard_deal(stage)]
    run_proc = run_streaming(
        [str(cwd / ".venv" / "bin" / "python3"), *witness, "run"], cwd=cwd, env=env
    )
    raw = "=== mutmut run ===\n" + run_proc.stdout + "\n"
    # Even on non-zero exit, mutants may have been generated; capture results.
    results_proc = subprocess.run(
        [str(mutmut_bin), "results"], cwd=cwd, env=env, capture_output=True, text=True, check=False
    )
    raw += "=== mutmut results ===\n" + results_proc.stdout + results_proc.stderr + "\n"
    raw += _keep_python_witnesses(artifact_dir, cwd / "mutants", binding)
    if stage is not None:
        header = record_python_shard(
            stage, ShortSha(short_sha(REPO_ROOT)), cwd / "mutants", artifact_dir
        )
        if header is None:
            (artifact_dir / f"{binding}.raw.txt").write_text(raw)
            return MutationReport(
                binding, "mutmut", 0, 0, raw, error="mutmut made no mutant, so no shard ran"
            )
        raw = header + raw
    (artifact_dir / f"{binding}.raw.txt").write_text(raw)

    counts = parse_mutmut(raw)
    if counts.total == 0 and (run_proc.returncode != 0 or results_proc.returncode != 0):
        return MutationReport(
            binding,
            "mutmut",
            0,
            0,
            raw,
            error=(
                f"mutmut run/results failed: exit "
                f"{run_proc.returncode}/{results_proc.returncode} (see {binding}.raw.txt)"
            ),
        )
    refusal = python_witness_refusal(
        artifact_dir, cwd / "mutants", Prose(raw)
    ) or python_placement_refusal(artifact_dir)
    if refusal is not None:
        return MutationReport(binding, "mutmut", counts.killed, counts.survived, raw, error=refusal)
    return MutationReport(
        binding,
        "mutmut",
        counts.killed,
        counts.survived,
        raw,
        observed=Observed(timeouts=counts.timeout, crashes=_crashes(Prose(results_proc.stdout))),
    )


# The section of a sweep's log ``mutmut results`` printed, which names the
# mutants that ended their process.
_RESULTS_SECTION = re.compile(
    r"^=== mutmut results ===\n(.*?)(?:^=== |\Z)", re.MULTILINE | re.DOTALL
)


def merge_python_shards(artifact_dir: Path, commit: ShortSha) -> MutationReport:
    """Merge the shards' sweeps found under the directory ``PYTHON_SHARDS_ENV`` names.

    Each shard's record, log and report are wanted exactly once under that
    directory, and the records must add up to one whole sweep
    (``tools/mutation_python.py``); a shard whose own run reported an error
    refuses the merge with it.  The merged report is the lane's ``python``
    report, its counts the shards' sums read off their logs and its log every
    shard's log, so the drift gate holds it to the record as a whole sweep's.
    """
    shards_env = os.environ.get(PYTHON_SHARDS_ENV, "")
    if not shards_env:
        msg = (
            f"{PYTHON_STAGE_ENV}={PYTHON_MERGE_STAGE} reads the shards from "
            + f"{PYTHON_SHARDS_ENV}: unset"
        )
        return MutationReport(PYTHON_LANE, "mutmut", 0, 0, "", error=msg)
    shards_dir = Path(shards_env)
    raw = f"=== merge of the Python shards under {shards_dir} ===\n"
    parts = read_python_shards(shards_dir, commit)
    if not isinstance(parts, list):
        return MutationReport(PYTHON_LANE, "mutmut", 0, 0, raw + parts, error=parts)
    raw += "".join(part.log for part in parts)
    (artifact_dir / f"{PYTHON_LANE}.raw.txt").write_text(raw)
    failed = [part for part in parts if part.error]
    if failed:
        error = f"Python shard {failed[0].record.number} failed: {failed[0].error}"
        return MutationReport(PYTHON_LANE, "mutmut", 0, 0, raw, error=error)
    counts = [parse_mutmut(part.log) for part in parts]
    crashes = sorted(
        crash
        for part in parts
        for section in _RESULTS_SECTION.findall(part.log)
        for crash in _crashes(Prose(section))
    )
    return MutationReport(
        PYTHON_LANE,
        "mutmut",
        sum(count.killed for count in counts),
        sum(count.survived for count in counts),
        raw,
        observed=Observed(timeouts=sum(count.timeout for count in counts), crashes=tuple(crashes)),
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
    as killed whatever it changed.  The doc-example harness and the Example
    functions are skipped (``go_sweep_goflags``).

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
        env = without_gremlins_settings({EnvName(k): EnvValue(v) for k, v in os.environ.items()})
        env[EnvName("ALETHEIA_REPO_ROOT")] = EnvValue(str(tree))
        env[EnvName("ALETHEIA_LIB")] = EnvValue(str(lib))
        env[EnvName("GOFLAGS")] = EnvValue(
            go_sweep_goflags(GoFlags(env.get(EnvName("GOFLAGS"), "")))
        )
        # gremlins targets the package directory and runs the package's tests
        # against each mutant: the canonical aletheia/ subpackage, the only Go
        # module holding runtime code.
        cut = None if stage is None else cut_go_shard(tree, stage)
        proc = sweep_go_package(gremlins_command(gremlins, tree), tree, env)
        if stage is not None and cut is not None:
            # The census comes after the sweep, under the package's own
            # configuration: before it, the dry run would leave the package
            # compiled for the coverage run gremlins times every mutant by
            # (tools/mutation_go.py).
            _ = (tree / GO_CONFIG).write_text(cut.package_config, encoding="utf-8")
            dry = run_capture(
                gremlins_command(gremlins, tree, "--dry-run"), cwd=tree / "go", env=env
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
# documents as a program of its own, and the package's Example functions, which
# go test checks against their Output: they hold the documentation to the
# package, the unit tests hold the package's behaviour, and the sweep skips
# them rather than pay their runs once per mutant.
GO_DOC_HARNESS = "TestDocExamples"
GO_EXAMPLES = r"Example\w*"


def go_sweep_goflags(caller: GoFlags) -> GoFlags:
    """Return the caller's ``GOFLAGS`` with test caching off, the harness and the examples skipped.

    ``go test`` reads both from ``GOFLAGS``, the one route to a test flag
    gremlins leaves open, and its coverage run and every mutant's run inherit
    them alike.  gremlins times its coverage run and stops each mutant's run
    at a multiple of that (``go/.gremlins.yaml``'s ``timeout-coefficient``), so
    a coverage run served from the test cache, as one is after a dry run of the
    same tree, stops every mutant before its tests end: measured on one shard
    at gremlins' default multiple of three, 362 of 382 mutants timed out.
    """
    return GoFlags(f"{caller} -count=1 -skip=^({GO_DOC_HARNESS}|{GO_EXAMPLES})$".strip())


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
# changed (the .so they all dlopen, this harness / the Mull build / the baselines).  So on a
# PR we run only the affected engine(s); an unchanged binding's survivor count
# is definitionally unchanged from its baseline, so skipping it is coverage-
# neutral.  The diff is read through ``tools/_branch_diff.py``, as every gate
# scoped by the branch reads it.
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
# this harness, the Mull build or the baselines, so it forces ALL bindings.  This
# set IS precision-sensitive: a miss here under-scopes (the dangerous direction),
# unlike the generous per-binding dirs above.
# What makes the kernel every binding loads: a change here moves every
# binding's result in this lane and in the coverage lane alike.
KERNEL_PATHS: tuple[str, ...] = (
    "src/",  # Agda → MAlonzo → libaletheia-ffi.so (every binding dlopens it)
    "haskell-shim/",  # FFI shim → .so
    "Shakefile.hs",  # build graph → .so
    "shake/",  # the build graph's rules
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
    "tools/_branch_diff.py",  # how the runner reads what the branch changed
    "tools/mull/",  # the patches the Mull plugin is built with, which decide its mutants
    "tools/build_mull.sh",  # the Mull release the plugin is built from, and how
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
      * any GLOBAL path changed (shared ``.so`` / harness / Mull build / baselines).

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
    changed = branch_changes(repo_root)
    if not changed:
        # None: no `git`, no `main` ref, a git error, so fail safe to the full
        # run; empty: push:main or no diff, so run the full backstop.
        return None
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
