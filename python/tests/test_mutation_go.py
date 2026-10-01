# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Go lane's shards cut the package on a census, and the merge holds them to it.

A shard sweeps the package under its own configuration with the other shards'
files held out; the merge refuses shards that do not add up to the census
they cut on, file by file.  Each refusal is staged here by a fixture that
breaks exactly the claim it holds, and the end-to-end merge is shown to give
the counts and the rows a whole sweep of the same mutants gives.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import TYPE_CHECKING, NewType, TypedDict, cast

import pytest
import yaml
from _git_repo import commit as commit_all
from _git_repo import git
from _stand_in import ScriptSource, ToolName, install_stand_in

from tools import mutation_run
from tools._common import RelPath, short_sha
from tools.mutation_go import (
    GO_CONFIG,
    GO_MERGE_STAGE,
    GO_SHARDS,
    GO_SHARDS_ENV,
    GO_STAGE_ENV,
    Binding,
    FilePattern,
    GremlinsLog,
    PackageFile,
    ShardNumber,
    ShardRecord,
    ShardSweep,
    ShortSha,
    WallSeconds,
    dry_run_census,
    go_stage,
    hold_out_pattern,
    is_go_shard,
    merge_refusal,
    shard_config_text,
    shard_domain,
    shard_files,
    shard_log_name,
    shard_record_name,
    swept_counts,
)

if TYPE_CHECKING:
    from tools.mutation_cpp_slices import MutantCounts

_REPO = Path(__file__).resolve().parents[2]

# What a CI job sets the stage variable to.
_StageText = NewType("_StageText", str)

# A mutator gremlins can switch on, by its configuration name.
_MutatorName = NewType("_MutatorName", str)


class _Mutator(TypedDict):
    enabled: bool


_Unleash = TypedDict("_Unleash", {"exclude-files": list[FilePattern]})


class _Config(TypedDict):
    """The gremlins configuration as the package's file spells it."""

    unleash: _Unleash
    mutants: dict[_MutatorName, _Mutator]


# A dry run's listing and two shards' sweeps of the same three files, in
# gremlins' own words: a.go and c.go in shard 1, b.go in shard 2.
_DRY = GremlinsLog(
    "Starting...\n"
    + "Gathering coverage... done in 3s\n"
    + "    RUNNABLE CONDITIONALS_NEGATION at a.go:1:2\n"
    + "    RUNNABLE ARITHMETIC_BASE at a.go:3:4\n"
    + " NOT COVERED CONDITIONALS_BOUNDARY at a.go:5:6\n"
    + "    RUNNABLE CONDITIONALS_NEGATION at b.go:7:8\n"
    + "    RUNNABLE INVERT_LOGICAL at b.go:9:1\n"
    + "    RUNNABLE INVERT_LOGICAL at b.go:9:9\n"
    + "    RUNNABLE CONDITIONALS_NEGATION at c.go:2:3\n"
    + "\n"
    + "Runnable: 6, Not covered: 1\n"
)
_SHARD_1 = GremlinsLog(
    "      KILLED CONDITIONALS_NEGATION at a.go:1:2\n"
    + "       LIVED ARITHMETIC_BASE at a.go:3:4\n"
    + " NOT COVERED CONDITIONALS_BOUNDARY at a.go:5:6\n"
    + "   TIMED OUT CONDITIONALS_NEGATION at c.go:2:3\n"
    + "Killed: 1, Lived: 1, Not covered: 1\n"
    + "Timed out: 1, Not viable: 0, Skipped: 0\n"
)
_SHARD_2 = GremlinsLog(
    "      KILLED CONDITIONALS_NEGATION at b.go:7:8\n"
    + "      KILLED INVERT_LOGICAL at b.go:9:1\n"
    + "       LIVED INVERT_LOGICAL at b.go:9:9\n"
    + "Killed: 2, Lived: 1, Not covered: 0\n"
    + "Timed out: 0, Not viable: 0, Skipped: 0\n"
)


def _path(name: PackageFile) -> RelPath:
    return RelPath(f"go/aletheia/{name}")


_DOMAIN = (
    _path(PackageFile("a.go")),
    _path(PackageFile("b.go")),
    _path(PackageFile("c.go")),
    _path(PackageFile("empty.go")),
)
_CENSUS: MutantCounts = {
    _path(PackageFile("a.go")): 3,
    _path(PackageFile("b.go")): 3,
    _path(PackageFile("c.go")): 1,
}


def _sweeps(
    files_1: tuple[RelPath, ...] = (
        _path(PackageFile("a.go")),
        _path(PackageFile("c.go")),
        _path(PackageFile("empty.go")),
    ),
    files_2: tuple[RelPath, ...] = (_path(PackageFile("b.go")),),
    log_2: GremlinsLog = _SHARD_2,
) -> list[ShardSweep]:
    return [
        ShardSweep(ShardRecord(ShardNumber(1), _DOMAIN, files_1, _CENSUS), _SHARD_1),
        ShardSweep(ShardRecord(ShardNumber(2), _DOMAIN, files_2, _CENSUS), log_2),
    ]


def test_the_stage_is_a_shard_the_merge_or_unset(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every shard and the merge read as themselves; nothing reads as the whole package."""
    monkeypatch.delenv(GO_STAGE_ENV, raising=False)
    assert go_stage() is None
    for number in range(1, GO_SHARDS + 1):
        monkeypatch.setenv(GO_STAGE_ENV, str(number))
        assert go_stage() == number
    monkeypatch.setenv(GO_STAGE_ENV, GO_MERGE_STAGE)
    assert go_stage() == GO_MERGE_STAGE


@pytest.mark.parametrize("value", ["0", str(GO_SHARDS + 1), "one", "-1", "merged"])
def test_a_stage_that_is_no_shard_is_refused_by_name(
    monkeypatch: pytest.MonkeyPatch, value: _StageText
) -> None:
    """A misspelt stage fails the job, naming the variable, rather than sweeping something else."""
    monkeypatch.setenv(GO_STAGE_ENV, value)
    with pytest.raises(ValueError, match=GO_STAGE_ENV):
        _ = go_stage()


def test_a_shard_binding_is_never_the_lane_s() -> None:
    """A shard reports as ``go-N``; the lane and other lanes' legs are no shard."""
    assert all(is_go_shard(Binding(f"go-{n}")) for n in range(1, GO_SHARDS + 1))
    for name in ("go", f"go-{GO_SHARDS + 1}", "go-0", "go-x", "cpp-leak-1", "rust"):
        assert not is_go_shard(Binding(name)), name


def test_a_hold_out_pattern_matches_its_file_and_no_other() -> None:
    """Anchored at a separator and at the end, as gremlins reads a path within the package."""
    pattern = hold_out_pattern(_path(PackageFile("json.go")))
    compiled = re.compile(pattern)
    assert compiled.search("json.go")
    assert compiled.search("sub/json.go")
    for other in ("xjson.go", "re_json.go", "json.go.orig", "json_go"):
        assert not compiled.search(other), other


def test_a_shard_configuration_keeps_the_package_s_own_exclusions(tmp_path: Path) -> None:
    """The stringer outputs stay held out: a command-line exclude would have replaced them.

    The configuration's mutators stay as written too, and the other shards'
    files are added after the package's own patterns.
    """
    source = _REPO / GO_CONFIG
    text = shard_config_text(
        source, [_path(PackageFile("json.go")), _path(PackageFile("client.go"))], ShardNumber(1)
    )
    written = tmp_path / ".gremlins.yaml"
    _ = written.write_text(text, encoding="utf-8")
    shard = cast("_Config", yaml.safe_load(written.read_text(encoding="utf-8")))
    package = cast("_Config", yaml.safe_load(source.read_text(encoding="utf-8")))
    own = package["unleash"]["exclude-files"]
    assert own, "the package's configuration holds nothing out, so this test reads nothing"
    assert shard["unleash"]["exclude-files"] == [
        *own,
        hold_out_pattern(_path(PackageFile("json.go"))),
        hold_out_pattern(_path(PackageFile("client.go"))),
    ]
    assert shard["mutants"] == package["mutants"]


def test_the_domain_is_the_package_s_sources_less_tests_generated_files_and_testdata() -> None:
    """Every file a shard may claim, read from the tree and the configuration."""
    domain = shard_domain(_REPO, _REPO / GO_CONFIG)
    assert _path(PackageFile("json.go")) in domain
    assert not [path for path in domain if path.endswith("_test.go")]
    assert not [path for path in domain if path.endswith("_string.go")]
    assert not [path for path in domain if path.count("/") != 2]


def test_a_census_counts_runnable_and_not_covered_alike() -> None:
    """The census is what the dry run lists, by file; a sweep's counts are what it reported."""
    assert dry_run_census(_DRY) == _CENSUS
    assert swept_counts(_SHARD_1) == {_path(PackageFile("a.go")): 3, _path(PackageFile("c.go")): 1}
    assert swept_counts(_SHARD_2) == {_path(PackageFile("b.go")): 3}


def test_the_shards_partition_the_domain_on_the_files_sizes(tmp_path: Path) -> None:
    """Disjoint shards whose union is the domain, each file weighing its size in the tree.

    a.go, the heaviest, takes the first shard; b.go and c.go together weigh
    as much and take the second; the empty file goes to the first on the tie.
    """
    for path, size in zip(_DOMAIN, (300, 200, 100, 0), strict=True):
        target = tmp_path / path
        target.parent.mkdir(parents=True, exist_ok=True)
        _ = target.write_text("x" * size, encoding="utf-8")
    shards = [shard_files(tmp_path, _DOMAIN, ShardNumber(n)) for n in range(1, GO_SHARDS + 1)]
    assert shards == [
        (_path(PackageFile("a.go")), _path(PackageFile("empty.go"))),
        (_path(PackageFile("b.go")), _path(PackageFile("c.go"))),
    ]


def test_a_shard_record_reads_back_as_written() -> None:
    """The record a shard writes is the one the merge reads."""
    record = ShardRecord(ShardNumber(2), _DOMAIN, (_path(PackageFile("b.go")),), _CENSUS)
    assert ShardRecord.from_json(json.loads(json.dumps(record.to_json()))) == record


def test_shards_that_add_up_to_their_census_merge() -> None:
    """The fixture's two shards swept every census mutant once."""
    assert merge_refusal(_sweeps()) is None


def test_a_missing_or_repeated_shard_is_refused() -> None:
    """Every shard once: one alone, or one twice, is no lane."""
    sweeps = _sweeps()
    assert merge_refusal(sweeps[:1]) is not None
    assert merge_refusal([sweeps[0], sweeps[0]]) is not None


def test_shards_that_cut_on_different_censuses_are_refused() -> None:
    """A tree or a tool that differed between the shards' runs."""
    first, second = _sweeps()
    other = second.record._replace(census={**_CENSUS, _path(PackageFile("c.go")): 2})
    refusal = merge_refusal([first, ShardSweep(other, second.log)])
    assert refusal is not None
    assert "censuses" in refusal


def test_a_file_claimed_twice_or_by_nobody_is_refused() -> None:
    """The shards' files are disjoint and are the whole domain, the empty file included."""
    twice = merge_refusal(_sweeps(files_2=(_path(PackageFile("b.go")), _path(PackageFile("c.go")))))
    assert twice is not None
    assert "claimed by Go shards" in twice
    nobody = merge_refusal(
        _sweeps(files_1=(_path(PackageFile("a.go")), _path(PackageFile("c.go"))))
    )
    assert nobody is not None
    assert "no Go shard claims" in nobody
    assert "empty.go" in nobody


def test_a_census_file_outside_the_domain_is_refused() -> None:
    """A census naming a file no shard may claim is a domain read wrong."""
    first, second = _sweeps()
    census = {**_CENSUS, _path(PackageFile("x_string.go")): 4}
    records = [shard.record._replace(census=census) for shard in (first, second)]
    refusal = merge_refusal([ShardSweep(records[0], first.log), ShardSweep(records[1], second.log)])
    assert refusal is not None
    assert "outside the shards' domain" in refusal


def test_a_shard_short_of_its_census_is_refused() -> None:
    """A shard that excluded more than the other shards' files swept fewer mutants."""
    short = GremlinsLog(str(_SHARD_2).replace("      KILLED INVERT_LOGICAL at b.go:9:1\n", ""))
    refusal = merge_refusal(_sweeps(log_2=short))
    assert refusal is not None
    assert "b.go: swept 2, census 3" in refusal


def test_a_shard_that_swept_a_file_it_does_not_claim_is_refused() -> None:
    """The command-line exclude trap: a shard that lost the package's own exclusions.

    Its sweep carries the generated file's mutants, which the census and its
    record do not, so the merge refuses it rather than counting them.
    """
    extra = GremlinsLog(_SHARD_2 + "      KILLED CONDITIONALS_NEGATION at kind_string.go:4:2\n")
    refusal = merge_refusal(_sweeps(log_2=extra))
    assert refusal is not None
    assert "kind_string.go: swept 1, census 0" in refusal


def _write_shard(directory: Path, sweep: ShardSweep, commit: ShortSha, secs: WallSeconds) -> None:
    number = sweep.record.number
    shard_dir = directory / f"mutation-go-{number}" / commit
    shard_dir.mkdir(parents=True)
    _ = (shard_dir / shard_record_name(number)).write_text(json.dumps(sweep.record.to_json()))
    _ = (shard_dir / shard_log_name(number)).write_text(sweep.log)
    summary = {"commit": commit, "elapsed_s": {"go": secs}, "runs": [{"binding": f"go-{number}"}]}
    _ = (shard_dir / "summary.json").write_text(json.dumps(summary))


def test_the_merge_gives_what_a_whole_sweep_of_the_same_mutants_gives(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Counts summed, every mutant line once, so the drift gate's rows are the whole sweep's."""
    shards_dir = tmp_path / "shards"
    commit = short_sha(_REPO)
    for sweep, secs in zip(_sweeps(), (11.5, 12.25), strict=True):
        _write_shard(shards_dir, sweep, ShortSha(commit), WallSeconds(secs))
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    monkeypatch.setenv(GO_STAGE_ENV, GO_MERGE_STAGE)
    monkeypatch.setenv(GO_SHARDS_ENV, str(shards_dir))
    merged = mutation_run.run_go(artifacts)
    assert merged.error is None
    assert merged.binding == "go"
    assert (merged.killed, merged.survived, merged.timeouts) == (3, 2, 1)
    whole = GremlinsLog(_SHARD_1 + _SHARD_2)
    for verdict in ("LIVED", "NOT COVERED"):
        assert mutation_run.go_mutant_rows(merged.raw_log, verdict) == mutation_run.go_mutant_rows(
            whole, verdict
        )
    assert json.loads((artifacts / "go-shards.json").read_text()) == {"go-1": 11.5, "go-2": 12.25}
    assert merged.raw_log.index("Killed: 3, Lived: 2, Not covered: 1") < merged.raw_log.index(
        "Killed: 1, Lived: 1"
    )


def test_the_merge_refuses_shards_of_another_commit(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Shards swept at another commit say nothing about this one."""
    shards_dir = tmp_path / "shards"
    for sweep in _sweeps():
        _write_shard(shards_dir, sweep, ShortSha("0000000"), WallSeconds(1.0))
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    monkeypatch.setenv(GO_STAGE_ENV, GO_MERGE_STAGE)
    monkeypatch.setenv(GO_SHARDS_ENV, str(shards_dir))
    merged = mutation_run.run_go(artifacts)
    assert merged.error is not None
    assert "0000000" in merged.error


def test_the_merge_refuses_a_shard_whose_log_is_missing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A shard its clock killed uploaded no log; the lane has no verdict without it."""
    shards_dir = tmp_path / "shards"
    commit = short_sha(_REPO)
    for sweep in _sweeps():
        _write_shard(shards_dir, sweep, ShortSha(commit), WallSeconds(1.0))
    (shards_dir / "mutation-go-2" / commit / shard_log_name(ShardNumber(2))).unlink()
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    monkeypatch.setenv(GO_STAGE_ENV, GO_MERGE_STAGE)
    monkeypatch.setenv(GO_SHARDS_ENV, str(shards_dir))
    merged = mutation_run.run_go(artifacts)
    assert merged.error is not None
    assert "0 copies of go-2.raw.txt" in merged.error


def test_a_shard_is_a_leg_the_drift_gate_does_not_judge() -> None:
    """A shard's survivors are recorded; only the merge is held to the baseline."""
    shard = mutation_run.MutationReport("go-1", "gremlins", 10, 99, "")
    entry = mutation_run.drift_for(shard, {"go": {"baseline": {"survivors": 0}}})
    assert entry["status"] == "leg"


# A stand-in for gremlins that reads the configuration it finds, as gremlins
# does: a dry run lists one mutant per file the configuration does not hold
# out, a sweep kills one per such file, and every call is recorded with the
# configuration it ran under.
_FAKE_GREMLINS = """\
import json
import os
import re
import sys
from pathlib import Path

import yaml

config = yaml.safe_load(Path(".gremlins.yaml").read_text(encoding="utf-8"))
held = [re.compile(p) for p in config["unleash"]["exclude-files"]]
names = sorted(
    f.name
    for f in Path("aletheia").glob("*.go")
    if not f.name.endswith("_test.go") and not any(p.search(f.name) for p in held)
)
dry = "--dry-run" in sys.argv
calls = Path(os.environ["GREMLINS_CALLS"])
seen = json.loads(calls.read_text()) if calls.exists() else []
seen.append({"dry": dry, "files": names, "goflags": os.environ.get("GOFLAGS")})
_ = calls.write_text(json.dumps(seen))
for name in names:
    print(("    RUNNABLE" if dry else "      KILLED") + f" CONDITIONALS_NEGATION at {name}:1:1")
if dry:
    print(f"Runnable: {len(names)}, Not covered: 0")
else:
    print(f"Killed: {len(names)}, Lived: 0, Not covered: 0")
    print("Timed out: 0, Not viable: 0, Skipped: 0")
"""

_PACKAGE = {"a.go": 300, "b.go": 200, "c.go": 100, "kind_string.go": 50, "a_test.go": 10}


def _sharded_repo(root: Path) -> Path:
    """Build a repository whose Go package has three sources, a generated file and a test file."""
    package = root / "go" / "aletheia"
    package.mkdir(parents=True)
    for name, size in _PACKAGE.items():
        _ = (package / name).write_text("x" * size, encoding="utf-8")
    _ = (root / GO_CONFIG).write_text(
        "unleash:\n  exclude-files:\n    - '_string\\.go$'\nmutants:\n  invert-logical:\n"
        + "    enabled: true\n",
        encoding="utf-8",
    )
    (root / "build").mkdir()
    _ = (root / "build" / "libaletheia-ffi.so").write_bytes(b"")
    _ = git(root, "init", "-q")
    _ = commit_all(root, "base")
    return root.resolve()


def _fake_sharded_gremlins(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    install_stand_in(tmp_path, monkeypatch, ToolName("gremlins"), ScriptSource(_FAKE_GREMLINS))
    calls = tmp_path / "calls.json"
    monkeypatch.setenv("GREMLINS_CALLS", str(calls))
    return calls


def test_a_shard_sweeps_its_files_then_takes_the_census_of_the_whole_package(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The sweep runs under the shard's configuration first; the census comes after, whole.

    A dry run ahead of the sweep would leave the package compiled for the
    coverage run gremlins times every mutant by, so the census is taken
    after, under the package's own configuration restored.
    """
    repo = _sharded_repo(tmp_path / "repo")
    calls = _fake_sharded_gremlins(tmp_path, monkeypatch)
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    monkeypatch.setenv(GO_STAGE_ENV, "1")
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    report = mutation_run.run_go(artifacts)
    assert report.error is None
    assert report.binding == "go-1"
    seen = json.loads(calls.read_text(encoding="utf-8"))
    assert [call["dry"] for call in seen] == [False, True]
    assert seen[0]["files"] == ["a.go"]
    assert seen[1]["files"] == ["a.go", "b.go", "c.go"]
    assert all("-count=1" in call["goflags"].split() for call in seen)
    record = json.loads((artifacts / shard_record_name(ShardNumber(1))).read_text())
    assert record["files"] == ["go/aletheia/a.go"]
    assert record["census"] == {"go/aletheia/a.go": 1, "go/aletheia/b.go": 1, "go/aletheia/c.go": 1}
    assert (artifacts / shard_log_name(ShardNumber(1))).is_file()


def test_two_stub_shards_merge_into_the_whole_package_s_verdict(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Each shard swept through the runner, then merged through it, as the lane runs them."""
    repo = _sharded_repo(tmp_path / "repo")
    _ = _fake_sharded_gremlins(tmp_path, monkeypatch)
    monkeypatch.setattr(mutation_run, "REPO_ROOT", repo)
    shards_dir = tmp_path / "shards"
    commit_sha = short_sha(repo)
    for number in range(1, GO_SHARDS + 1):
        monkeypatch.setenv(GO_STAGE_ENV, str(number))
        artifacts = shards_dir / f"mutation-go-{number}" / commit_sha
        artifacts.mkdir(parents=True)
        report = mutation_run.run_go(artifacts)
        assert report.error is None
        summary = {"commit": commit_sha, "elapsed_s": {"go": 1.0}, "runs": [report.to_dict()]}
        _ = (artifacts / "summary.json").write_text(json.dumps(summary))
    merge_dir = tmp_path / "merge"
    merge_dir.mkdir()
    monkeypatch.setenv(GO_STAGE_ENV, GO_MERGE_STAGE)
    monkeypatch.setenv(GO_SHARDS_ENV, str(shards_dir))
    merged = mutation_run.run_go(merge_dir)
    assert merged.error is None
    assert (merged.killed, merged.survived) == (3, 0)
