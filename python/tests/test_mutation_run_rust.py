# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the Rust lane's reading of cargo-mutants and the drift gate over it.

cargo-mutants puts every mutant in one of four buckets and writes them to
``outcomes.json``; the console prints only what was missed.  What is held
here: the sweep mutates a scratch copy of the tree as it stands and never
the tree, the counts are read from the file, a survivor is keyed on the
mutation and its source line the way the C++ ledger keys one, a sweep that
reached no mutant is an error rather than a clean run of nothing, the tool's
version is read off its banner, and the verdict refuses a survivor the record
does not name.  The sweeps start no process: the tool, the scratch copy and
the commit at HEAD are stood in on the test's own thread, so what each test
holds is the lane's use of them.
"""

from __future__ import annotations

import contextlib
import json
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, NewType, NoReturn, SupportsInt, cast

from _executors import DrivenExecutor
from _processes import CommandWord
from _scratch_copies import install as install_copies

from tools import mutation_run, mutation_rust
from tools.mutation_go import ShortSha
from tools.mutation_report import MutantCount, MutationReport, Observed

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Generator, Mapping

    import pytest
    from _scratch_copies import ScratchCopies

    from tools.mutation_report import BindingSpec


def _mutant(file: str, line: int, name: str, summary: str) -> dict[str, object]:
    """One outcome in the shape cargo-mutants 27 writes."""
    return {
        "scenario": {
            "Mutant": {
                "name": f"{file}:{line}:5: {name}",
                "package": "aletheia",
                "file": file,
                "function": {"function_name": "f", "return_type": "", "span": {}},
                "span": {"start": {"line": line, "column": 5}, "end": {"line": line, "column": 9}},
                "replacement": "()",
                "genre": "FnValue",
            }
        },
        "summary": summary,
        "log_path": "log/x.log",
        "diff_path": "diff/x.diff",
        "phase_results": [],
    }


_OUTCOMES: dict[str, object] = {
    "outcomes": [
        {"scenario": "Baseline", "summary": "Success", "phase_results": []},
        _mutant("src/backend.rs", 2, "replace > with >= in frame_len", "MissedMutant"),
        _mutant("src/backend.rs", 2, "replace > with == in frame_len", "MissedMutant"),
        _mutant("src/types.rs", 3, "replace Dlc::new -> Self with 0", "CaughtMutant"),
        _mutant("src/types.rs", 1, "replace as_u8 -> u8 with 0", "Unviable"),
        _mutant("src/types.rs", 1, "replace as_u8 -> u8 with 1", "Timeout"),
    ],
    "total_mutants": 5,
    "missed": 2,
    "caught": 1,
    "timeout": 1,
    "unviable": 1,
    "success": 0,
    "cargo_mutants_version": "27.1.0",
}


def _tree(tmp_path: Path) -> Path:
    crate = tmp_path / "rust" / "src"
    crate.mkdir(parents=True)
    _ = (crate / "backend.rs").write_text("fn frame_len() {\n    if data.len() > MAX {\n}\n")
    _ = (crate / "types.rs").write_text("a\nb\nc\n")
    return tmp_path


def _read_line(root: Path) -> Callable[[str, int], str]:
    def read(file: str, line: int) -> str:
        return (root / file).read_text(encoding="utf-8").split("\n")[line - 1]

    return read


def _spec(survivors: int = 2, **baseline: object) -> dict[str, BindingSpec]:
    return {"rust": cast("BindingSpec", {"baseline": {"survivors": survivors, **baseline}})}


def test_the_counts_are_read_from_the_outcomes() -> None:
    """Caught is killed, missed is survived, and the timeouts travel with the report.

    Every mutant the tool made is the four buckets together, the unviable
    included, which no other count reads.
    """
    rep = mutation_rust.parse_outcomes(_OUTCOMES, "", "exit 2")
    assert rep.error is None
    assert (rep.killed, rep.survived, rep.observed.timeouts) == (1, 2, 1)
    assert rep.total_mutants == 3
    assert rep.observed.generated == 5


def test_a_sweep_that_reached_no_mutant_is_an_error() -> None:
    """A failed baseline leaves every bucket empty, which is not a clean run."""
    empty: dict[str, object] = {
        **_OUTCOMES,
        "outcomes": [],
        "missed": 0,
        "caught": 0,
        "timeout": 0,
        "unviable": 0,
    }
    rep = mutation_rust.parse_outcomes(empty, "", "exit 1")
    assert rep.error is not None
    assert "no mutant" in rep.error
    absent = mutation_rust.parse_outcomes({"outcomes": []}, "", "exit 1")
    assert absent.error is not None
    assert "no counts" in absent.error


def test_survivors_are_keyed_on_the_mutation_and_the_source_line(tmp_path: Path) -> None:
    """The position is stripped from the name; the line's text is read from the tree."""
    rows = mutation_rust.outcomes_survivor_rows(_OUTCOMES, _read_line(_tree(tmp_path)))
    assert rows == {
        ("replace > with >= in frame_len", "rust/src/backend.rs", "if data.len() > MAX {"): 1,
        ("replace > with == in frame_len", "rust/src/backend.rs", "if data.len() > MAX {"): 1,
    }


def test_the_version_is_read_off_the_banner() -> None:
    """``cargo mutants --version`` prints the name and the version; anything else is none."""
    assert mutation_rust.cargo_mutants_version("cargo-mutants 27.1.0\n") == "27.1.0"
    assert mutation_rust.cargo_mutants_version("error: no such command: `mutants`") is None


def test_a_survivor_the_ledger_does_not_name_fails(tmp_path: Path) -> None:
    """At an unchanged count, a survivor traded for another is still a regression."""
    rows = mutation_rust.outcomes_survivor_rows(_OUTCOMES, _read_line(_tree(tmp_path)))
    rep = MutationReport("rust", "cargo-mutants", 1, 2, "", observed=Observed(timeouts=1))
    ledger = [
        {
            "mutator": "replace > with >= in frame_len",
            "file": "rust/src/backend.rs",
            "text": "if data.len() > MAX {",
            "count": 1,
        },
        {"mutator": "replace a with b in g", "file": "rust/src/types.rs", "text": "a", "count": 1},
    ]
    entry = mutation_run.drift_for(rep, _spec(survivors_ledger=ledger), survivor_rows=rows)
    assert entry["status"] == "regression"
    assert entry.get("unrecorded_survivors") == [
        {
            "mutator": "replace > with == in frame_len",
            "file": "rust/src/backend.rs",
            "text": "if data.len() > MAX {",
            "count": 1,
        }
    ]
    assert entry.get("stale_ledger") == [ledger[1]]


def test_the_timeout_ceiling_is_read_before_the_count() -> None:
    """A run that timed out on nearly everything is refused whatever else it reports."""
    rep = MutationReport("rust", "cargo-mutants", 3, 0, "", observed=Observed(timeouts=300))
    entry = mutation_run.drift_for(rep, _spec(survivors=0, timeout_ceiling=20))
    assert entry["status"] == "regression"
    assert entry.get("observed_timeouts") == 300


# A stand-in for cargo-mutants on the test's thread, installed where the lane
# calls the tool.  The listing gives ten mutants of the crate, dealt
# round-robin to the shards as cargo-mutants deals them: enough that each of a
# split sweep's eight shards gets one.  A shard's sweep records the directory
# it ran in and the source it found there, writes a mutant into that source as
# the real tool does, and reports its share of the mutants caught.

# A variable of a run's environment, and the value it is set to.
_EnvName = NewType("_EnvName", str)
_EnvValue = NewType("_EnvValue", str)


def _listed_mutant(line: mutation_rust.SourceIndex) -> mutation_rust.ListedMutant:
    """One mutant of ``src/lib.rs`` at ``line``, as ``cargo mutants --list --json`` spells it."""
    span = mutation_rust.SourceSpan(
        start=mutation_rust.SourcePosition(line=line, column=mutation_rust.SourceIndex(1)),
        end=mutation_rust.SourcePosition(line=line, column=mutation_rust.SourceIndex(2)),
    )
    return mutation_rust.ListedMutant(
        file=mutation_rust.CrateFile("src/lib.rs"),
        name=mutation_rust.MutationName(f"src/lib.rs:{line}:1: replace {line}"),
        span=span,
    )


_LISTED = [_listed_mutant(mutation_rust.SourceIndex(line)) for line in range(1, 11)]


@dataclass(frozen=True)
class _Run:
    """One run of the stood-in tool: the words, the directory and the environment it was given."""

    argv: tuple[CommandWord, ...]
    cwd: Path
    env: dict[_EnvName, _EnvValue]

    def after(self, flag: CommandWord) -> CommandWord:
        """Give the word that follows ``flag``."""
        return self.argv[self.argv.index(flag) + 1]


@dataclass
class _Cargo:
    """cargo-mutants, as the lane lists with it and sweeps each shard with it."""

    listings: list[_Run] = field(default_factory=list[_Run])
    sweeps: list[_Run] = field(default_factory=list[_Run])

    def capture(
        self, cmd: list[CommandWord], *, cwd: Path, env: Mapping[_EnvName, _EnvValue]
    ) -> subprocess.CompletedProcess[Prose]:
        """Print the listing, the one call the lane captures."""
        assert cmd[1:] == ["mutants", "--list", "--json"]
        self.listings.append(_Run(tuple(cmd), cwd, dict(env)))
        return subprocess.CompletedProcess(cmd, 0, Prose(f"{json.dumps(_LISTED)}\n"), Prose(""))

    def stream(
        self,
        cmd: list[CommandWord],
        *,
        cwd: Path,
        env: Mapping[_EnvName, _EnvValue],
        sink: Callable[[Prose], SupportsInt],
    ) -> subprocess.CompletedProcess[Prose]:
        """Sweep the shard ``--shard`` names, writing its outcomes under ``--output``."""
        run = _Run(tuple(cmd), cwd, dict(env))
        self.sweeps.append(run)
        number, total = (int(part) for part in run.after(CommandWord("--shard")).split("/"))
        out = Path(run.after(CommandWord("--output")))
        source = cwd / "src" / "lib.rs"
        seen = source.read_text(encoding="utf-8")
        _ = source.write_text("mutant\n", encoding="utf-8")
        (out / "mutants.out").mkdir(parents=True, exist_ok=True)
        _ = (out / "ran_in.txt").write_text(f"{cwd}\n{seen}", encoding="utf-8")
        debug = run.env.get(_EnvName(mutation_rust.SWEEP_DEBUG_VAR), _EnvValue("unset"))
        _ = (out / "debug.txt").write_text(debug)
        _ = (out / "shard.txt").write_text(f"{number}/{total}")
        document = _shard_outcomes(mutation_rust.RustShard(number), mutation_rust.ShardCount(total))
        _ = (out / "mutants.out" / "outcomes.json").write_text(json.dumps(document))
        # A sweep prints nothing, so no line reaches the lane's log.
        del sink
        return subprocess.CompletedProcess(cmd, 0, Prose(""), Prose(""))


def _shard_outcomes(
    number: mutation_rust.RustShard, total: mutation_rust.ShardCount
) -> mutation_rust.SweepOutcomes:
    """Give one shard's outcomes: its round-robin share of the listing, every mutant caught."""
    mine = [m for index, m in enumerate(_LISTED) if index % total == number]
    outcomes: list[mutation_rust.MutantOutcome] = [
        {"scenario": "Baseline", "summary": mutation_rust.OutcomeSummary("Success")},
        *(
            mutation_rust.MutantOutcome(
                scenario={"Mutant": m}, summary=mutation_rust.OutcomeSummary("CaughtMutant")
            )
            for m in mine
        ),
    ]
    caught, none = MutantCount(len(mine)), MutantCount(0)
    return {
        "outcomes": outcomes,
        "total_mutants": caught,
        "caught": caught,
        "missed": none,
        "timeout": none,
        "unviable": none,
        "success": none,
    }


def _install_cargo(monkeypatch: pytest.MonkeyPatch) -> _Cargo:
    """Stand the tool in where the lane lists and sweeps with it; give the stand-in."""
    cargo = _Cargo()
    monkeypatch.setattr(mutation_rust, "run_capture", cargo.capture)
    monkeypatch.setattr(mutation_rust, "run_streaming", cargo.stream)
    return cargo


# The commit the stood-in ``short_sha`` reads at HEAD.
_COMMIT = ShortSha("abc1234")


@dataclass
class _Commit:
    """``short_sha`` stood in: the fixed commit, and every tree it was asked of."""

    asked: list[Path | None] = field(default_factory=list[Path | None])

    def __call__(self, repo_root: Path | None = None) -> ShortSha:
        """Record ``repo_root`` and give the fixed commit."""
        self.asked.append(repo_root)
        return _COMMIT


@dataclass(frozen=True)
class _Lane:
    """The planted tree, and the stand-ins a sweep of it runs on."""

    repo: Path
    copies: ScratchCopies
    cargo: _Cargo
    commit: _Commit


def _sweepable(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> _Lane:
    """Plant a tree whose crate source reads its uncommitted edit, and stand in what sweeps it."""
    repo = tmp_path / "repo"
    source = repo / mutation_rust.CRATE / "src" / "lib.rs"
    source.parent.mkdir(parents=True)
    _ = source.write_text("uncommitted edit\n", encoding="utf-8")
    lib = tmp_path / "libaletheia-ffi.so"

    def tools_found(_pinned: str | None) -> tuple[str, Path]:
        return str(tmp_path / "cargo"), lib

    copies = install_copies(monkeypatch, tmp_path / "copies")
    lane = _Lane(repo, copies, _install_cargo(monkeypatch), _Commit())
    monkeypatch.setattr(mutation_rust, "REPO_ROOT", repo)
    monkeypatch.setattr(mutation_rust, "_check_rust_tools", tools_found)
    monkeypatch.setattr(mutation_rust, "short_sha", lane.commit)
    return lane


def test_the_sweep_mutates_a_copy_of_the_tree_as_it_stands(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The tool runs in a copy carrying the uncommitted edit; the tree keeps its source."""
    lane = _sweepable(tmp_path, monkeypatch)
    repo = lane.repo
    monkeypatch.setattr(mutation_rust, "rust_shards", lambda: mutation_rust.ShardCount(2))
    artifacts = tmp_path / "artifacts"
    report = mutation_rust.run_rust(artifacts, executor=DrivenExecutor)
    assert report.error is None
    assert (report.killed, report.survived) == (10, 0)
    # A copy of the tree was asked for each shard, and each shard swept its own copy's crate.
    assert lane.copies.asked == [repo, repo]
    crates = [copy / mutation_rust.CRATE for copy in lane.copies.made]
    assert [run.cwd for run in lane.cargo.sweeps] == crates
    copies: set[Path] = set()
    for number in (0, 1):
        ran = artifacts / "rust" / f"shard-{number}" / "ran_in.txt"
        ran_in, seen = ran.read_text(encoding="utf-8").split("\n", 1)
        assert Path(ran_in) == crates[number]
        assert Path(ran_in).name == "rust"
        assert not Path(ran_in).is_relative_to(repo)
        assert seen == "uncommitted edit\n"
        assert not Path(ran_in).exists()
        copies.add(Path(ran_in))
        # Every shard builds without debug information, the sweep's own profile.
        debug = (artifacts / "rust" / f"shard-{number}" / "debug.txt").read_text(encoding="utf-8")
        assert debug == mutation_rust.SWEEP_DEBUG
    # Each shard swept a copy of its own: one copy holds one mutant at a time.
    assert len(copies) == 2
    assert not any(copy.exists() for copy in lane.copies.made)
    assert (repo / "rust" / "src" / "lib.rs").read_text(encoding="utf-8") == "uncommitted edit\n"


def _refuse(message: Prose) -> NoReturn:
    """Raise the ``RuntimeError`` ``scratch_worktree`` raises for a git step that failed."""
    raise RuntimeError(message)


def test_a_tree_that_cannot_be_copied_is_a_refusal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """With no scratch copy there is no sweep: the report says why, and the tool never ran."""
    cargo = _install_cargo(monkeypatch)

    def tools_found(_pinned: str | None) -> tuple[str, Path]:
        return str(tmp_path / "cargo"), tmp_path / "libaletheia-ffi.so"

    outside = tmp_path / "outside"
    outside.mkdir()
    step = f"git worktree add -q --detach {tmp_path / 'tree'} HEAD"
    refused = Prose(f"{step} failed in {outside}: fatal: not a git repository")

    @contextlib.contextmanager
    def refusing(_repo_root: Path) -> Generator[Path]:
        yield _refuse(refused)

    monkeypatch.setattr("tools.mutation_report.scratch_worktree", refusing)
    monkeypatch.setattr(mutation_rust, "REPO_ROOT", outside)
    monkeypatch.setattr(mutation_rust, "_check_rust_tools", tools_found)
    artifacts = tmp_path / "artifacts"
    report = mutation_rust.run_rust(artifacts, executor=DrivenExecutor)
    assert report.error is not None
    assert report.error == f"no scratch copy of the tree: {refused}"
    assert (cargo.listings, cargo.sweeps) == ([], [])
    assert not (artifacts / "rust").exists()


def _job(jobs: Path, monkeypatch: pytest.MonkeyPatch, job: mutation_rust.RustJob) -> MutationReport:
    """Sweep one job's part into its own directory under ``jobs``, as its artifact downloads.

    The job's summary records the commit and its binding, as the runner's does.
    """
    monkeypatch.setenv(mutation_rust.RUST_STAGE_ENV, str(job))
    artifacts = jobs / f"mutation-rust-{job}" / _COMMIT
    report = mutation_rust.run_rust(artifacts, executor=DrivenExecutor)
    summary = {"commit": _COMMIT, "runs": [{"binding": report.binding}]}
    _ = (artifacts / "summary.json").write_text(json.dumps(summary), encoding="utf-8")
    return report


def _merge(jobs: Path, monkeypatch: pytest.MonkeyPatch, out: Path) -> MutationReport:
    """Merge the jobs under ``jobs`` with no tool on hand: the merge stage needs none."""
    monkeypatch.setattr(mutation_rust, "_check_rust_tools", None)
    monkeypatch.setenv(mutation_rust.RUST_STAGE_ENV, mutation_rust.RUST_MERGE_STAGE)
    monkeypatch.setenv(mutation_rust.RUST_JOBS_ENV, str(jobs))
    return mutation_rust.run_rust(out, executor=DrivenExecutor)


def test_a_job_sweeps_its_four_of_the_jobs_eight_shards(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Job two takes shards four to seven of eight, whatever CPUs it has, and keeps the listing."""
    lane = _sweepable(tmp_path, monkeypatch)
    report = _job(tmp_path / "jobs", monkeypatch, mutation_rust.RustJob(2))
    assert report.error is None
    assert report.binding == "rust-2"
    artifacts = next((tmp_path / "jobs").rglob(mutation_rust.RUST_LISTING)).parent
    dealt = sorted(path.read_text() for path in (artifacts / "rust").glob("shard-*/shard.txt"))
    assert dealt == ["4/8", "5/8", "6/8", "7/8"]
    shards = [run.after(CommandWord("--shard")) for run in lane.cargo.sweeps]
    assert shards == ["4/8", "5/8", "6/8", "7/8"]
    assert lane.copies.asked == [lane.repo] * mutation_rust.RUST_JOB_SHARDS


def test_the_jobs_merge_into_the_whole_sweep(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The jobs' eight shards merge into the outcomes and the verdict one whole sweep gives."""
    lane = _sweepable(tmp_path, monkeypatch)
    jobs = tmp_path / "jobs"
    assert _job(jobs, monkeypatch, mutation_rust.RustJob(1)).error is None
    assert _job(jobs, monkeypatch, mutation_rust.RustJob(2)).error is None
    merged = _merge(jobs, monkeypatch, tmp_path / "out")
    assert merged.error is None
    assert merged.binding == "rust"
    assert (merged.killed, merged.survived) == (10, 0)
    outcomes = json.loads((tmp_path / "out" / mutation_rust.OUTCOMES).read_text(encoding="utf-8"))
    assert outcomes["total_mutants"] == 10
    # The merge reads the commit of the tree it merges for.
    assert lane.commit.asked == [lane.repo]


def _two_jobs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Sweep both jobs, giving the directory they landed under."""
    _ = _sweepable(tmp_path, monkeypatch)
    jobs = tmp_path / "jobs"
    _ = _job(jobs, monkeypatch, mutation_rust.RustJob(1))
    _ = _job(jobs, monkeypatch, mutation_rust.RustJob(2))
    return jobs


def test_jobs_that_listed_different_mutants_are_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Shards dealt from two listings are not one sweep's, however they add up."""
    jobs = _two_jobs(tmp_path, monkeypatch)
    listing = next(jobs.rglob(mutation_rust.RUST_LISTING))
    _ = listing.write_text("[]", encoding="utf-8")
    merged = _merge(jobs, monkeypatch, tmp_path / "out")
    assert merged.error is not None
    assert "listed different mutants" in merged.error


def test_a_job_of_another_commit_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A job left from an earlier push is no part of this commit's sweep."""
    jobs = _two_jobs(tmp_path, monkeypatch)
    summary = next(jobs.glob("mutation-rust-2/*/summary.json"))
    _ = summary.write_text(json.dumps({"commit": "0000000", "runs": [{"binding": "rust-2"}]}))
    merged = _merge(jobs, monkeypatch, tmp_path / "out")
    assert merged.error is not None
    assert "the rust-2 job swept 0000000" in merged.error
    assert f", this merge is at {_COMMIT}" in merged.error


def test_a_shard_missing_from_the_jobs_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A job that stopped short leaves a shard no merge can count, so the merge says which."""
    jobs = _two_jobs(tmp_path, monkeypatch)
    next(jobs.rglob("shard-5/mutants.out/outcomes.json")).unlink()
    merged = _merge(jobs, monkeypatch, tmp_path / "out")
    assert merged.error is not None
    assert "0 copies of shard 5's outcomes" in merged.error


def test_a_stage_that_is_no_job_is_an_error(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A third job of two would deal shards the merge never reads."""
    monkeypatch.setenv(mutation_rust.RUST_STAGE_ENV, "3")
    report = mutation_rust.run_rust(tmp_path, executor=DrivenExecutor)
    assert report.error is not None
    assert mutation_rust.RUST_STAGE_ENV in report.error


def test_a_job_is_recorded_and_never_judged() -> None:
    """A job holds part of the crate's mutants: the merge, not the job, meets the record."""
    rep = MutationReport("rust-1", "cargo-mutants", 3, 9, "")
    entry = mutation_run.drift_for(rep, _spec(survivors=0, timeout_ceiling=20))
    assert entry["status"] == "leg"
    assert entry.get("observed_survivors") == 9
