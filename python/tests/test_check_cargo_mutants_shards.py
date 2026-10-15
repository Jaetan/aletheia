# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The shards gate judges planted listings, and asks cargo-mutants for every shard of every count.

``tools/check_cargo_mutants_shards.py`` lists the crate's mutants whole and in
shards and holds the shards to the whole.  The listings are replaced here by
answers the test writes, so what the gate asks, how it reads each answer and
each refusal it can make are held without cargo-mutants.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

import pytest
from _processes import CommandWord

from tools import check_cargo_mutants_shards, mutation_rust
from tools.check_cargo_mutants_shards import (
    STEP,
    ShardKeys,
    check,
    partition_refusals,
    shard_counts,
)
from tools.mutation_rust import (
    RUST_JOB_SHARDS,
    RUST_JOBS,
    RUST_SHARDS_CAP,
    CargoMutantsVersion,
    ListedMutant,
    MutantKey,
    RustShard,
    ShardCount,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Sequence

    from tools.pin_scope import PinGate

CARGO = Path("/home/tester/.cargo/bin/cargo")
PINNED = CargoMutantsVersion("27.1.0")

# A planted listing: nine mutants, two of them in one file.
MUTANTS: tuple[ListedMutant, ...] = tuple(
    ListedMutant(
        file=mutation_rust.CrateFile(f"src/{name}.rs"),
        name=mutation_rust.MutationName(f"replace {name} with ()"),
        span={
            "start": {
                "line": mutation_rust.SourceIndex(line),
                "column": mutation_rust.SourceIndex(1),
            },
            "end": {
                "line": mutation_rust.SourceIndex(line),
                "column": mutation_rust.SourceIndex(9),
            },
        },
    )
    for name, line in (
        ("alpha", 3),
        ("beta", 5),
        ("gamma", 7),
        ("delta", 9),
        ("epsilon", 11),
        ("zeta", 13),
        ("eta", 15),
        ("theta", 17),
        ("alpha", 19),
    )
)

# The commands a run of the gate asked, in order.
type Asked = list[list[CommandWord]]
# An answer to a listing command run in a directory.
type Answer = Callable[[list[CommandWord], Path], subprocess.CompletedProcess[Prose]]


def _keys(spelled: Prose) -> list[MutantKey]:
    """Plant keys from their space-separated names, so a judge's case reads as what it deals."""
    return [MutantKey(name) for name in spelled.split()]


def _dealt(count: ShardCount, mutants: Sequence[ListedMutant]) -> list[list[ListedMutant]]:
    """Deal ``mutants`` to ``count`` shards round robin, as cargo-mutants does."""
    return [list(mutants[number::count]) for number in range(count)]


def test_the_counts_are_every_shard_count_the_runner_can_choose() -> None:
    """Two up to the cap for a sweep in one process, and the CI jobs' total."""
    assert shard_counts() == (*range(2, RUST_SHARDS_CAP + 1), RUST_JOBS * RUST_JOB_SHARDS)
    assert len(set(shard_counts())) == len(shard_counts())


class _Judged(NamedTuple):
    """A planted partition and the refusals the judge owes it."""

    whole: list[MutantKey]
    shards: dict[ShardCount, ShardKeys]
    refusals: list[Prose]


_JUDGED = [
    _Judged(_keys(Prose("a b c")), {ShardCount(2): [_keys(Prose("a c")), _keys(Prose("b"))]}, []),
    _Judged(
        _keys(Prose("a b c")),
        {ShardCount(2): [_keys(Prose("a c")), _keys(Prose("b c"))]},
        [Prose("2 shards: 1 mutants in more than one shard, 0 in none, 0 not in the listing")],
    ),
    _Judged(
        _keys(Prose("a b c")),
        {ShardCount(3): [_keys(Prose("a")), _keys(Prose("b")), []]},
        [Prose("3 shards: 0 mutants in more than one shard, 1 in none, 0 not in the listing")],
    ),
    _Judged(
        _keys(Prose("a b c")),
        {ShardCount(2): [_keys(Prose("a c")), _keys(Prose("b d"))]},
        [Prose("2 shards: 0 mutants in more than one shard, 0 in none, 1 not in the listing")],
    ),
    _Judged(
        _keys(Prose("a b")),
        {
            ShardCount(2): [_keys(Prose("a a")), _keys(Prose("b"))],
            ShardCount(3): [_keys(Prose("a")), [], []],
        },
        [
            Prose("2 shards: 1 mutants in more than one shard, 0 in none, 0 not in the listing"),
            Prose("3 shards: 0 mutants in more than one shard, 1 in none, 0 not in the listing"),
        ],
    ),
    _Judged([], {}, [Prose("the listing names no mutant")]),
    _Judged([], {ShardCount(2): [[], []]}, [Prose("the listing names no mutant")]),
    _Judged(_keys(Prose("a b a")), {}, [Prose("the listing names 3 mutants, 2 of them distinct")]),
    _Judged(
        _keys(Prose("a b a")),
        {ShardCount(2): [_keys(Prose("a")), _keys(Prose("b"))]},
        [Prose("the listing names 3 mutants, 2 of them distinct")],
    ),
]


@pytest.mark.parametrize(
    ("whole", "shards", "refusals"),
    _JUDGED,
    ids=[
        "clean",
        "twice",
        "missed",
        "extra",
        "two-counts",
        "empty-whole",
        "empty-whole-with-shards",
        "repeated-whole",
        "repeated-whole-with-shards",
    ],
)
def test_the_judge_names_each_defect_of_a_planted_partition(
    whole: list[MutantKey], shards: dict[ShardCount, ShardKeys], refusals: list[Prose]
) -> None:
    """A clean partition is refused nothing; each defect is named with its count and numbers."""
    assert partition_refusals(whole, shards) == refusals


def _listing(mutants: Sequence[ListedMutant]) -> subprocess.CompletedProcess[Prose]:
    """Answer a listing with ``mutants`` as cargo-mutants prints them."""
    return subprocess.CompletedProcess(
        [], ExitStatus(0), Prose(json.dumps(list(mutants))), Prose("")
    )


def _shard_of(cmd: list[CommandWord]) -> tuple[RustShard, ShardCount] | None:
    """Read the shard a listing command asks for, or None for the whole listing."""
    if "--shard" not in cmd:
        return None
    number, count = cmd[cmd.index(CommandWord("--shard")) + 1].split("/")
    return RustShard(int(number)), ShardCount(int(count))


def _install(monkeypatch: pytest.MonkeyPatch, answer: Answer) -> Asked:
    """Answer every listing through ``answer``, the pinned tool on hand; return what is asked."""
    asked: Asked = []

    def run(cmd: list[CommandWord], *, cwd: Path) -> subprocess.CompletedProcess[Prose]:
        asked.append(cmd)
        return answer(cmd, cwd)

    def installed(_pinned: CargoMutantsVersion | None) -> Path | Prose:
        return CARGO

    monkeypatch.setattr(check_cargo_mutants_shards, "run_capture", run)
    monkeypatch.setattr(check_cargo_mutants_shards, "check_cargo_mutants", installed)
    return asked


def _round_robin(cmd: list[CommandWord], cwd: Path) -> subprocess.CompletedProcess[Prose]:
    """Deal the planted listing round robin to whatever shard is asked for, in the crate."""
    assert cwd.name == "rust"
    shard = _shard_of(cmd)
    if shard is None:
        return _listing(MUTANTS)
    number, count = shard
    return _listing(_dealt(count, MUTANTS)[number])


def test_a_release_dealing_every_count_as_a_partition_passes(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The gate lists the whole, then every shard of every count in the crate, and says nothing."""
    asked = _install(monkeypatch, _round_robin)
    assert check(tmp_path) == ExitStatus(0)
    assert capsys.readouterr().out == ""
    listing = [str(CARGO), "mutants", "--list", "--json", "--colors", "never"]
    expected = [listing]
    for count in shard_counts():
        expected.extend([*listing, "--shard", f"{number}/{count}"] for number in range(count))
    assert asked == expected


def test_a_count_whose_shards_break_the_partition_is_refused(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """One count dealing a mutant twice and dropping another is named with its numbers."""

    def skewed(cmd: list[CommandWord], cwd: Path) -> subprocess.CompletedProcess[Prose]:
        shard = _shard_of(cmd)
        if shard is None or shard[1] != 3:
            return _round_robin(cmd, cwd)
        number, count = shard
        dealt = _dealt(count, MUTANTS)
        if number == 0:
            return _listing(dealt[0][1:])
        if number == 1:
            return _listing([*dealt[1], dealt[2][0]])
        return _listing(dealt[2])

    asked = _install(monkeypatch, skewed)
    assert check(tmp_path) == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"{STEP}: 3 shards: 1 mutants in more than one shard, 1 in none, 0 not in the listing\n"
    )
    assert len(asked) == 1 + sum(shard_counts())


@pytest.mark.parametrize(
    ("whole", "said"),
    [
        ([], "the listing names no mutant"),
        ([*MUTANTS, MUTANTS[0]], "the listing names 10 mutants, 9 of them distinct"),
    ],
    ids=["empty", "repeated"],
)
def test_a_whole_listing_that_is_empty_or_repeats_a_mutant_is_refused_before_any_shard(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    whole: list[ListedMutant],
    said: Prose,
) -> None:
    """A whole listing with nothing to partition is refused, and no shard is listed."""

    def answer(_cmd: list[CommandWord], _cwd: Path) -> subprocess.CompletedProcess[Prose]:
        return _listing(whole)

    asked = _install(monkeypatch, answer)
    assert check(tmp_path) == ExitStatus(1)
    assert capsys.readouterr().out == f"{STEP}: {said}\n"
    assert len(asked) == 1


def test_a_listing_that_fails_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A shard listing exiting non-zero stops the gate at 2, naming the command and its stderr."""

    def failing(cmd: list[CommandWord], cwd: Path) -> subprocess.CompletedProcess[Prose]:
        if _shard_of(cmd) == (1, 2):
            return subprocess.CompletedProcess(cmd, ExitStatus(4), Prose(""), Prose("no crate\n"))
        return _round_robin(cmd, cwd)

    asked = _install(monkeypatch, failing)
    assert check(tmp_path) == ExitStatus(2)
    assert capsys.readouterr().out == (
        f"{STEP}: `cargo mutants --list --json --colors never --shard 1/2` in {tmp_path / 'rust'}"
        + " exited 4: no crate\n"
    )
    assert len(asked) == 3


@pytest.mark.parametrize(
    ("printed", "said"),
    [
        (Prose("not json"), "printed what is not JSON: Expecting value: line 1 column 1 (char 0)"),
        (Prose('{"a": 1}'), "printed what is not a list of mutants"),
        (Prose('[{"file": "src/lib.rs"}]'), "printed what is not a list of mutants"),
    ],
    ids=["not-json", "not-a-list", "not-mutants"],
)
def test_a_listing_that_does_not_parse_is_no_answer(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    printed: Prose,
    said: Prose,
) -> None:
    """The whole listing printing anything but a JSON list stops the gate at 2."""

    def answer(cmd: list[CommandWord], _cwd: Path) -> subprocess.CompletedProcess[Prose]:
        return subprocess.CompletedProcess(cmd, ExitStatus(0), printed, Prose(""))

    asked = _install(monkeypatch, answer)
    assert check(tmp_path) == ExitStatus(2)
    assert capsys.readouterr().out == (
        f"{STEP}: `cargo mutants --list --json --colors never` in {tmp_path / 'rust'} {said}\n"
    )
    assert len(asked) == 1


def _tool_answers(
    monkeypatch: pytest.MonkeyPatch, *, version: subprocess.CompletedProcess[Prose] | None
) -> Asked:
    """Have cargo on PATH only when ``version`` is an answer, the one its ``--version`` gets."""
    asked: Asked = []

    def cargo(name: CommandWord) -> CommandWord:
        assert name == "cargo"
        if version is None:
            message = f"required executable not found on PATH: {name}"
            raise RuntimeError(message)
        return CommandWord(str(CARGO))

    def run(cmd: list[CommandWord]) -> subprocess.CompletedProcess[Prose]:
        asked.append(cmd)
        assert version is not None
        return version

    def never_listed(cmd: list[CommandWord], *, cwd: Path) -> subprocess.CompletedProcess[Prose]:
        raise AssertionError((cmd, cwd))

    def pinned() -> CargoMutantsVersion | None:
        return PINNED

    monkeypatch.setattr(mutation_rust, "find_executable", cargo)
    monkeypatch.setattr(mutation_rust, "run_capture", run)
    monkeypatch.setattr(check_cargo_mutants_shards, "run_capture", never_listed)
    monkeypatch.setattr(check_cargo_mutants_shards, "pinned_version", pinned)
    return asked


def _version(status: ExitStatus, printed: Prose) -> subprocess.CompletedProcess[Prose]:
    """Answer ``cargo mutants --version`` with ``printed`` at ``status``."""
    return subprocess.CompletedProcess([], status, printed, Prose(""))


@pytest.mark.parametrize(
    ("version", "said"),
    [
        (None, "required executable not found on PATH: cargo"),
        (
            _version(ExitStatus(101), Prose("error: no such command: `mutants`\n")),
            "cargo-mutants is not installed: cargo install cargo-mutants --locked",
        ),
        (
            _version(ExitStatus(0), Prose("cargo-mutants 26.3.0\n")),
            "cargo-mutants 26.3.0 is installed where the record pins 27.1.0",
        ),
    ],
    ids=["no-cargo", "no-cargo-mutants", "another-release"],
)
def test_a_tool_that_is_absent_or_not_the_pinned_release_is_no_answer(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    version: subprocess.CompletedProcess[Prose] | None,
    said: Prose,
) -> None:
    """The lane's own refusal of the tool stops the gate at 2 before any listing."""
    asked = _tool_answers(monkeypatch, version=version)
    assert check(tmp_path) == ExitStatus(2)
    assert capsys.readouterr().out == f"{STEP}: {said}\n"
    assert asked == ([] if version is None else [[str(CARGO), "mutants", "--version"]])


def _out_of_scope(_gate: PinGate, _root: Path) -> bool:
    """Answer that the branch moved nothing a gate rests on."""
    return False


def _never_checked(_root: Path) -> ExitStatus:
    """Fail the test if the gate reaches for the tool."""
    raise AssertionError


def test_a_branch_moving_nothing_the_fact_rests_on_lists_nothing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Out of scope, the gate passes without listing."""

    def the_tree() -> Path:
        return tmp_path

    monkeypatch.setattr(check_cargo_mutants_shards, "git_toplevel", the_tree)
    monkeypatch.setattr(check_cargo_mutants_shards, "gate_runs", _out_of_scope)
    monkeypatch.setattr(check_cargo_mutants_shards, "check", _never_checked)
    monkeypatch.setattr("sys.argv", ["check_cargo_mutants_shards"])
    assert check_cargo_mutants_shards.main() == ExitStatus(0)


def test_in_scope_the_gate_s_verdict_is_the_check_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving what the fact rests on gets the check's own exit status."""

    def the_tree() -> Path:
        return tmp_path

    def in_scope(gate: PinGate, root: Path) -> bool:
        assert gate == "cargo-mutants-shards"
        assert root == tmp_path
        return True

    def refusing(root: Path) -> ExitStatus:
        assert root == tmp_path
        return ExitStatus(1)

    monkeypatch.setattr(check_cargo_mutants_shards, "git_toplevel", the_tree)
    monkeypatch.setattr(check_cargo_mutants_shards, "gate_runs", in_scope)
    monkeypatch.setattr(check_cargo_mutants_shards, "check", refusing)
    monkeypatch.setattr("sys.argv", ["check_cargo_mutants_shards"])
    assert check_cargo_mutants_shards.main() == ExitStatus(1)


def test_the_gate_refuses_an_argument_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An argument the gate does not take stops it before it reads anything."""
    monkeypatch.setattr("sys.argv", ["check_cargo_mutants_shards", "--unknown"])
    with pytest.raises(SystemExit) as stopped:
        _ = check_cargo_mutants_shards.main()
    assert stopped.value.code == 2
