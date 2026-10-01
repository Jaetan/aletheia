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
does not name.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import TYPE_CHECKING, cast

from _git_repo import repo_with_an_uncommitted_edit

from tools import mutation_run, mutation_rust
from tools.mutation_report import MutationReport

if TYPE_CHECKING:
    from collections.abc import Callable

    import pytest

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
    """Caught is killed, missed is survived, and the timeouts travel with the report."""
    rep = mutation_rust.parse_outcomes(_OUTCOMES, "", "exit 2")
    assert rep.error is None
    assert (rep.killed, rep.survived, rep.timeouts) == (1, 2, 1)
    assert rep.total_mutants == 3


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
    rep = MutationReport("rust", "cargo-mutants", 1, 2, "", timeouts=1)
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
    rep = MutationReport("rust", "cargo-mutants", 3, 0, "", timeouts=300)
    entry = mutation_run.drift_for(rep, _spec(survivors=0, timeout_ceiling=20))
    assert entry["status"] == "regression"
    assert entry.get("observed_timeouts") == 300


# A stand-in for cargo-mutants: it records the directory it ran in and the
# source it found there, writes a mutant into that source as the real tool
# does, and reports one caught mutant.
_FAKE_CARGO = """\\
import json
import os
import sys
from pathlib import Path

# Ten mutants of the crate, dealt round-robin to the shards as cargo-mutants deals them:
# enough that each of a split sweep's eight shards gets one.
def mutant(line, name):
    span = {"start": {"line": line, "column": 1}, "end": {"line": line, "column": 2}}
    return {"file": "src/lib.rs", "name": f"src/lib.rs:{line}:1: {name}", "span": span}

listed = [mutant(line, f"replace {line}") for line in range(1, 11)]
if "--list" in sys.argv:
    print(json.dumps(listed))
    sys.exit(0)
number, total = (int(part) for part in sys.argv[sys.argv.index("--shard") + 1].split("/"))
out = Path(sys.argv[sys.argv.index("--output") + 1])
source = Path.cwd() / "src" / "lib.rs"
seen = source.read_text(encoding="utf-8")
_ = source.write_text("mutant\\n", encoding="utf-8")
(out / "mutants.out").mkdir(parents=True, exist_ok=True)
_ = (out / "ran_in.txt").write_text(f"{Path.cwd()}\\n{seen}", encoding="utf-8")
_ = (out / "debug.txt").write_text(os.environ.get("CARGO_PROFILE_DEV_DEBUG", "unset"))
_ = (out / "shard.txt").write_text(f"{number}/{total}")
mine = [m for index, m in enumerate(listed) if index % total == number]
outcomes = [{"scenario": "Baseline", "summary": "Success"}] + [
    {"scenario": {"Mutant": m}, "summary": "CaughtMutant"} for m in mine
]
counts = {"caught": len(mine), "missed": 0, "timeout": 0, "unviable": 0, "success": 0}
document = {"outcomes": outcomes, "total_mutants": len(mine), **counts}
_ = (out / "mutants.out" / "outcomes.json").write_text(json.dumps(document))
"""


def _crate_repo(root: Path) -> Path:
    """Build a repository whose crate source is committed, then edited and not committed."""
    return repo_with_an_uncommitted_edit(root, Path("rust/src/lib.rs"))


def _sweepable(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Stand the tool in for a repository whose crate carries an uncommitted edit; give the repo."""
    repo = _crate_repo(tmp_path / "repo")
    cargo = tmp_path / "cargo"
    _ = cargo.write_text(f"#!{sys.executable}\n{_FAKE_CARGO}", encoding="utf-8")
    cargo.chmod(0o755)
    lib = tmp_path / "libaletheia-ffi.so"

    def tools_found(_pinned: str | None) -> tuple[str, Path]:
        return str(cargo), lib

    monkeypatch.setattr(mutation_rust, "REPO_ROOT", repo)
    monkeypatch.setattr(mutation_rust, "_check_rust_tools", tools_found)
    return repo


def test_the_sweep_mutates_a_copy_of_the_tree_as_it_stands(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The tool runs in a copy carrying the uncommitted edit; the tree keeps its source."""
    repo = _sweepable(tmp_path, monkeypatch)
    monkeypatch.setattr(mutation_rust, "rust_shards", lambda: mutation_rust.ShardCount(2))
    artifacts = tmp_path / "artifacts"
    report = mutation_rust.run_rust(artifacts)
    assert report.error is None
    assert (report.killed, report.survived) == (10, 0)
    copies: set[Path] = set()
    for number in (0, 1):
        ran = artifacts / "rust" / f"shard-{number}" / "ran_in.txt"
        ran_in, seen = ran.read_text(encoding="utf-8").split("\n", 1)
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
    assert (repo / "rust" / "src" / "lib.rs").read_text(encoding="utf-8") == "uncommitted edit\n"


def test_a_tree_that_cannot_be_copied_is_a_refusal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """With no scratch copy there is no sweep: the report says why, and the tool never ran."""
    cargo = tmp_path / "cargo"
    _ = cargo.write_text(f"#!{sys.executable}\n{_FAKE_CARGO}", encoding="utf-8")
    cargo.chmod(0o755)

    def tools_found(_pinned: str | None) -> tuple[str, Path]:
        return str(cargo), tmp_path / "libaletheia-ffi.so"

    outside = tmp_path / "outside"
    outside.mkdir()
    monkeypatch.setattr(mutation_rust, "REPO_ROOT", outside)
    monkeypatch.setattr(mutation_rust, "_check_rust_tools", tools_found)
    artifacts = tmp_path / "artifacts"
    report = mutation_rust.run_rust(artifacts)
    assert report.error is not None
    assert report.error.startswith("no scratch copy of the tree: git worktree add")
    assert not (artifacts / "rust").exists()


def _job(jobs: Path, monkeypatch: pytest.MonkeyPatch, job: mutation_rust.RustJob) -> MutationReport:
    """Sweep one job's part into its own directory under ``jobs``, as its artifact downloads.

    The job's summary records the commit and its binding, as the runner's does.
    """
    monkeypatch.setenv(mutation_rust.RUST_STAGE_ENV, str(job))
    commit = mutation_rust.short_sha(mutation_rust.REPO_ROOT)
    artifacts = jobs / f"mutation-rust-{job}" / commit
    report = mutation_rust.run_rust(artifacts)
    summary = {"commit": commit, "runs": [{"binding": report.binding}]}
    _ = (artifacts / "summary.json").write_text(json.dumps(summary), encoding="utf-8")
    return report


def _merge(jobs: Path, monkeypatch: pytest.MonkeyPatch, out: Path) -> MutationReport:
    """Merge the jobs under ``jobs`` with no tool on hand: the merge stage needs none."""
    monkeypatch.setattr(mutation_rust, "_check_rust_tools", None)
    monkeypatch.setenv(mutation_rust.RUST_STAGE_ENV, mutation_rust.RUST_MERGE_STAGE)
    monkeypatch.setenv(mutation_rust.RUST_JOBS_ENV, str(jobs))
    return mutation_rust.run_rust(out)


def test_a_job_sweeps_its_four_of_the_jobs_eight_shards(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Job two takes shards four to seven of eight, whatever CPUs it has, and keeps the listing."""
    _ = _sweepable(tmp_path, monkeypatch)
    report = _job(tmp_path / "jobs", monkeypatch, mutation_rust.RustJob(2))
    assert report.error is None
    assert report.binding == "rust-2"
    artifacts = next((tmp_path / "jobs").rglob(mutation_rust.RUST_LISTING)).parent
    dealt = sorted(path.read_text() for path in (artifacts / "rust").glob("shard-*/shard.txt"))
    assert dealt == ["4/8", "5/8", "6/8", "7/8"]


def test_the_jobs_merge_into_the_whole_sweep(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The jobs' eight shards merge into the outcomes and the verdict one whole sweep gives."""
    _ = _sweepable(tmp_path, monkeypatch)
    jobs = tmp_path / "jobs"
    assert _job(jobs, monkeypatch, mutation_rust.RustJob(1)).error is None
    assert _job(jobs, monkeypatch, mutation_rust.RustJob(2)).error is None
    merged = _merge(jobs, monkeypatch, tmp_path / "out")
    assert merged.error is None
    assert merged.binding == "rust"
    assert (merged.killed, merged.survived) == (10, 0)
    outcomes = json.loads((tmp_path / "out" / mutation_rust.OUTCOMES).read_text(encoding="utf-8"))
    assert outcomes["total_mutants"] == 10


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
    report = mutation_rust.run_rust(tmp_path)
    assert report.error is not None
    assert mutation_rust.RUST_STAGE_ENV in report.error


def test_a_job_is_recorded_and_never_judged() -> None:
    """A job holds part of the crate's mutants: the merge, not the job, meets the record."""
    rep = MutationReport("rust-1", "cargo-mutants", 3, 9, "")
    entry = mutation_run.drift_for(rep, _spec(survivors=0, timeout_ceiling=20))
    assert entry["status"] == "leg"
    assert entry.get("observed_survivors") == 9
