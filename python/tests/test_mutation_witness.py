# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The witness keeps what a mutant's run that does not return did, and changes nothing else.

``tools/mutation_witness.py`` wraps mutmut's ``PytestRunner.run_tests`` in
mutmut's own process.  These tests hand the wrapper a function in its place and
hold what each run leaves: while it runs, a file holding the mutant's name and
pytest's output, every byte on disk as it is written, which a run that ends its
process leaves behind; a run that raises turns it into its witness with the
traceback and raises on unchanged; one that returns removes it; a run naming no
mutant is not touched.  The name is read through the runner's signature, a
runner naming no mutant is refused before any run, and each named run is
tallied before its tests start.  A run that returns or raises with its heap
below 2^32 leaves where the heap starts, read from a map each test plants, so
the verdict is the same under every interpreter.  The suite loads the module
as a plugin, which names each test as it starts in that file, and only there.
``main`` installs the wrapper on the class it imports and hands mutmut's
command line the rest.
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock

import pytest

from tools import mutation_witness
from tools._common import CommandWord
from tools.mutation_witness import (
    LOW_HEAP_SUFFIX,
    PLACEMENT_ENV,
    TALLY_FILE,
    WITNESS_FILE_ENV,
    Address,
    Deal,
    DealText,
    MapsText,
    MutantName,
    ShardCount,
    ShardPlace,
    TestId,
    dealing,
    dealt,
    low_heap,
    parse_deal,
    placement_env,
    pytest_runtest_logstart,
    running_path,
    witness_path,
    witnessed,
)

from aletheia.common_types import ExitStatus, Prose

_MUTANT = MutantName("aletheia.client._streaming.xǁStreamingMixinǁ_enrich_violation__mutmut_9")
# What the stand-in run prints, as pytest prints a usage error.
_PRINTED = Prose("ERROR: not found: tests/test_x.py::test_y")

# A map naming no heap, as a process's where mmap placed every block.
_NO_HEAP = Path(os.devnull)

# A map's lines around the heap, as this host's interpreter, built without
# position independence, places it low and one built with it places it high.
_MAPPED = MapsText("00400000-00421000 r--p 00000000 08:20 2121 /usr/bin/python3.14\n")
_STACK = MapsText("7ffd4b2e1000-7ffd4b302000 rw-p 00000000 00:00 0  [stack]\n")
_LOW_HEAP = MapsText("0689e000-068e0000 rw-p 00000000 00:00 0  [heap]\n")
_HIGH_HEAP = MapsText("55d1c3a2b000-55d1c3b4c000 rw-p 00000000 00:00 0  [heap]\n")
_LAST_LOW_HEAP = MapsText("fffff000-100000000 rw-p 00000000 00:00 0  [heap]\n")
_FIRST_HIGH_HEAP = MapsText("100000000-100021000 rw-p 00000000 00:00 0  [heap]\n")


# A mutant as the stand-in listings give it: its file's data, its name, its exit.
type _Listed = tuple[Prose, MutantName, ExitStatus | None]


def _maps(directory: Path, *lines: MapsText) -> Path:
    """Write a map of ``lines`` in ``directory`` and return its path."""
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "maps"
    _ = path.write_text("".join(lines), encoding="utf-8")
    return path


class _RefusedError(Exception):
    """The exception the stand-in run raises, as mutmut's runner does when pytest returns 4."""


_REFUSAL = _RefusedError("pytest returned 4")


def _raising(*, mutant_name: MutantName | None) -> ExitStatus:
    """Print what pytest would, then raise the one refusal."""
    _ = mutant_name
    _ = sys.stdout.write(f"{_PRINTED}\n")
    raise _REFUSAL


def _returning(*, mutant_name: MutantName | None) -> ExitStatus:
    """Print what pytest would, then return its status for a failed test."""
    _ = mutant_name
    _ = sys.stdout.write(f"{_PRINTED}\n")
    return ExitStatus(1)


def _exiting(*, mutant_name: MutantName | None) -> ExitStatus:
    """Leave by ``SystemExit``, which no ``except Exception`` catches."""
    _ = mutant_name
    raise SystemExit(3)


def _named() -> Prose | None:
    """Return the file the witness names now, if it names one."""
    named = os.environ.get(WITNESS_FILE_ENV)
    return None if named is None else Prose(named)


def test_a_mutants_raising_run_leaves_its_output_and_traceback_and_raises_on(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The witness names the mutant, holds pytest's output and the traceback; the error goes on."""
    streams = sys.stdout, sys.stderr
    with pytest.raises(_RefusedError) as raised:
        _ = witnessed(_raising, tmp_path, _NO_HEAP)(mutant_name=_MUTANT)
    assert raised.value is _REFUSAL
    lines = witness_path(tmp_path, _MUTANT).read_text(encoding="utf-8").splitlines()
    assert lines[:3] == [_MUTANT, _PRINTED, ""]
    assert lines[3] == "Traceback (most recent call last):"
    assert lines[-1] == "test_mutation_witness._RefusedError: pytest returned 4"
    assert not running_path(tmp_path, _MUTANT).exists()
    assert capsys.readouterr() == ("", "")
    assert (sys.stdout, sys.stderr) == streams
    assert _named() is None


def test_a_mutants_run_that_returns_leaves_nothing(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A run that returns hands back its status and leaves its tally line alone."""
    streams = sys.stdout, sys.stderr
    assert witnessed(_returning, tmp_path, _NO_HEAP)(mutant_name=_MUTANT) == ExitStatus(1)
    assert [path.name for path in tmp_path.iterdir()] == [TALLY_FILE]
    assert capsys.readouterr() == ("", "")
    assert (sys.stdout, sys.stderr) == streams
    assert _named() is None


def test_every_byte_is_on_disk_while_the_run_goes_on(tmp_path: Path) -> None:
    """Mid-run the named file holds the name and the output so far: what an ended run leaves."""
    seen: list[Prose] = []

    def looking(*, mutant_name: MutantName | None) -> ExitStatus:
        _ = mutant_name
        _ = sys.stdout.write(f"{_PRINTED}\n")
        named = _named()
        assert named is not None
        seen.extend([named, Prose(Path(named).read_text(encoding="utf-8"))])
        return ExitStatus(0)

    assert witnessed(looking, tmp_path, _NO_HEAP)(mutant_name=_MUTANT) == ExitStatus(0)
    assert seen == [str(running_path(tmp_path, _MUTANT)), f"{_MUTANT}\n{_PRINTED}\n"]


def _by_position(mutant_name: MutantName | None) -> ExitStatus:
    """Take the mutant's name by position, as a later mutmut might hand it."""
    _ = mutant_name
    raise _REFUSAL


def _renamed(*, mutant: MutantName | None) -> ExitStatus:
    """Name the mutant under another parameter, as a later mutmut might."""
    _ = mutant
    return ExitStatus(0)


def test_a_name_handed_by_position_is_read_too(tmp_path: Path) -> None:
    """The name is read through the runner's signature, so a positional one is witnessed."""
    with pytest.raises(_RefusedError):
        _ = witnessed(_by_position, tmp_path, _NO_HEAP)(_MUTANT)
    assert witness_path(tmp_path, _MUTANT).is_file()


def test_a_runner_without_the_parameter_is_refused_before_any_run(tmp_path: Path) -> None:
    """A ``run_tests`` naming no ``mutant_name`` stops the witness at its start, not unseen."""
    with pytest.raises(TypeError, match="takes no mutant_name: no mutant's run could be told"):
        _ = witnessed(_renamed, tmp_path, _NO_HEAP)
    assert not list(tmp_path.iterdir())


def test_each_named_run_is_tallied_before_its_tests_start(tmp_path: Path) -> None:
    """The tally has one line per named run, written before it runs, and none for the others."""
    seen: list[Prose] = []

    def looking(*, mutant_name: MutantName | None) -> ExitStatus:
        _ = mutant_name
        seen.append(Prose((tmp_path / TALLY_FILE).read_text(encoding="utf-8")))
        return ExitStatus(0)

    other = MutantName("aletheia.client._ffi.x_take__mutmut_6")
    _ = witnessed(looking, tmp_path, _NO_HEAP)(mutant_name=_MUTANT)
    with pytest.raises(_RefusedError):
        _ = witnessed(_raising, tmp_path, _NO_HEAP)(mutant_name=other)
    with pytest.raises(_RefusedError):
        _ = witnessed(_raising, tmp_path, _NO_HEAP)(mutant_name=None)
    assert seen == [f"{_MUTANT}\n"]
    assert (tmp_path / TALLY_FILE).read_text(encoding="utf-8") == f"{_MUTANT}\n{other}\n"


def test_a_run_naming_no_mutant_is_left_alone(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The clean and forced-fail runs print where they did, name no file and leave none."""
    with pytest.raises(_RefusedError):
        _ = witnessed(_raising, tmp_path, _NO_HEAP)(mutant_name=None)
    assert not list(tmp_path.iterdir())
    assert capsys.readouterr().out == f"{_PRINTED}\n"


def test_a_run_that_exits_is_witnessed_and_exits_on(tmp_path: Path) -> None:
    """A ``SystemExit``, which mutmut's ``except Exception`` lets by, leaves its witness too."""
    with pytest.raises(SystemExit) as stopped:
        _ = witnessed(_exiting, tmp_path, _NO_HEAP)(mutant_name=_MUTANT)
    assert stopped.value.code == 3
    assert witness_path(tmp_path, _MUTANT).read_text(encoding="utf-8").endswith("SystemExit: 3\n")


@pytest.mark.parametrize(
    ("lines", "start"),
    [
        ((_MAPPED, _LOW_HEAP, _STACK), Address(0x689E000)),
        ((_MAPPED, _HIGH_HEAP, _STACK), None),
        ((_MAPPED, _STACK), None),
        ((_LAST_LOW_HEAP,), Address(0xFFFFF000)),
        ((_FIRST_HIGH_HEAP,), None),
    ],
    ids=["low", "high", "none", "the last low address", "2^32"],
)
def test_the_heap_is_named_where_it_starts_below_2_32_and_only_there(
    lines: tuple[MapsText, ...], start: Address | None
) -> None:
    """A heap starting below 2^32 is named by its start; one above, or none, is not."""
    assert low_heap(MapsText("".join(lines))) == start


def test_the_settings_apply_where_the_heap_lies_below_2_32_and_only_there(tmp_path: Path) -> None:
    """A low heap takes the placement settings; a high one or none takes nothing."""
    assert placement_env(_maps(tmp_path / "low", _MAPPED, _LOW_HEAP)) == PLACEMENT_ENV
    assert not placement_env(_maps(tmp_path / "high", _MAPPED, _HIGH_HEAP))
    assert not placement_env(_NO_HEAP)


def test_a_run_ending_with_its_heap_low_leaves_where_it_starts(tmp_path: Path) -> None:
    """A run that returns, raises or exits with its heap below 2^32 names its start."""
    witness_dir = tmp_path / "witness"
    witness_dir.mkdir()
    maps = _maps(tmp_path / "proc", _MAPPED, _LOW_HEAP, _STACK)
    raising = MutantName("aletheia.client._ffi.x_take__mutmut_6")
    exiting = MutantName("aletheia.client._ffi.x_take__mutmut_7")
    assert witnessed(_returning, witness_dir, maps)(mutant_name=_MUTANT) == ExitStatus(1)
    with pytest.raises(_RefusedError):
        _ = witnessed(_raising, witness_dir, maps)(mutant_name=raising)
    with pytest.raises(SystemExit):
        _ = witnessed(_exiting, witness_dir, maps)(mutant_name=exiting)
    for mutant in (_MUTANT, raising, exiting):
        heap = witness_dir / f"{mutant}{LOW_HEAP_SUFFIX}"
        assert heap.read_text(encoding="utf-8") == "0x689e000\n"


def test_a_run_naming_no_mutant_reads_no_heap(tmp_path: Path) -> None:
    """The clean and forced-fail runs leave nothing, whatever their heap."""
    witness_dir = tmp_path / "witness"
    witness_dir.mkdir()
    maps = _maps(tmp_path / "proc", _LOW_HEAP)
    assert witnessed(_returning, witness_dir, maps)(mutant_name=None) == ExitStatus(1)
    assert not list(witness_dir.iterdir())


def test_a_name_the_witness_held_before_is_given_back(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The variable the run set is restored to what it held, on return and on a raise."""
    monkeypatch.setenv(WITNESS_FILE_ENV, "outer")
    _ = witnessed(_returning, tmp_path, _NO_HEAP)(mutant_name=_MUTANT)
    assert _named() == "outer"
    with pytest.raises(_RefusedError):
        _ = witnessed(_raising, tmp_path, _NO_HEAP)(mutant_name=_MUTANT)
    assert _named() == "outer"


def test_each_starting_test_is_named_only_in_a_witnessed_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The start hook appends one line per test to the named file, and writes nothing unnamed."""
    record = tmp_path / "m.running"
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv(WITNESS_FILE_ENV, raising=False)
    pytest_runtest_logstart(TestId("tests/test_a.py::test_one"))
    assert not list(tmp_path.iterdir())
    monkeypatch.setenv(WITNESS_FILE_ENV, str(record))
    pytest_runtest_logstart(TestId("tests/test_a.py::test_one"))
    pytest_runtest_logstart(TestId("tests/test_b.py::test_two"))
    assert record.read_text(encoding="utf-8") == (
        "started tests/test_a.py::test_one\nstarted tests/test_b.py::test_two\n"
    )


def test_the_suite_loads_the_witness_for_its_start_lines(request: pytest.FixtureRequest) -> None:
    """The conftest registers the witness module as a plugin, so its start hook runs."""
    assert request.config.pluginmanager.has_plugin("tools.mutation_witness")


def test_main_installs_the_witness_and_hands_mutmut_the_rest(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``main`` wraps the runner it imports, makes the directory and runs mutmut on the rest.

    The wrapped runner reads the heap from this process's map, planted here.
    """
    runner = SimpleNamespace(run_tests=_raising)
    cli = Mock()
    modules = {
        "mutmut.runners.harness": SimpleNamespace(PytestRunner=runner),
        "mutmut.__main__": SimpleNamespace(cli=cli),
    }
    monkeypatch.setattr(mutation_witness, "import_module", modules.__getitem__)
    monkeypatch.setattr(mutation_witness, "PROCESS_MAPS", _maps(tmp_path / "proc", _LOW_HEAP))
    witness_dir = tmp_path / "python-witness"
    argv = ["--witness-dir", str(witness_dir), "run", _MUTANT]
    with pytest.raises(SystemExit) as stopped:
        mutation_witness.main([CommandWord(word) for word in argv])
    assert stopped.value.code == 0
    cli.main.assert_called_once_with(args=["run", _MUTANT], prog_name="mutmut")
    assert witness_dir.is_dir()
    with pytest.raises(_RefusedError):
        _ = runner.run_tests(mutant_name=_MUTANT)
    assert witness_path(witness_dir, _MUTANT).is_file()
    assert (witness_dir / f"{_MUTANT}{LOW_HEAP_SUFFIX}").is_file()


def test_main_refuses_a_runner_it_cannot_tell_a_mutant_by(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``main`` stops before mutmut runs when the imported runner names no ``mutant_name``."""
    cli = Mock()
    modules = {
        "mutmut.runners.harness": SimpleNamespace(PytestRunner=SimpleNamespace(run_tests=_renamed)),
        "mutmut.__main__": SimpleNamespace(cli=cli),
    }
    monkeypatch.setattr(mutation_witness, "import_module", modules.__getitem__)
    argv = ["--witness-dir", str(tmp_path / "python-witness"), "run"]
    with pytest.raises(TypeError, match="takes no mutant_name"):
        mutation_witness.main([CommandWord(word) for word in argv])
    cli.main.assert_not_called()


def test_a_deal_reads_k_of_n_and_refuses_anything_else() -> None:
    """``K/N`` with 1 <= K <= N is a shard; any other text is refused naming the form."""
    assert parse_deal(DealText("1/2")) == Deal(ShardPlace(1), ShardCount(2))
    assert parse_deal(DealText("3/3")) == Deal(ShardPlace(3), ShardCount(3))
    for text in ("0/2", "3/2", "2", "a/b", "1/0", "/2", "1/"):
        with pytest.raises(argparse.ArgumentTypeError, match="is not K/N with 1 <= K <= N"):
            _ = parse_deal(DealText(text))


# Seven mutants as mutmut's listing gives them, out of name order, each with its file.
_LISTED = [
    (Prose(f"data-{n % 2}"), MutantName(f"aletheia.client._ffi.x_take__mutmut_{n}"), None)
    for n in (5, 1, 7, 3, 2, 6, 4)
]


def test_each_shard_is_dealt_every_nth_of_the_sorted_names_from_its_place() -> None:
    """Shard K of N keeps the K-th, (K+N)-th, ... sorted name, its triple whole and in order."""
    names = sorted(name for _, name, _ in _LISTED)
    first = dealt(_LISTED, Deal(ShardPlace(1), ShardCount(2)))
    second = dealt(_LISTED, Deal(ShardPlace(2), ShardCount(2)))
    assert sorted(name for _, name, _ in first) == names[0::2]
    assert sorted(name for _, name, _ in second) == names[1::2]
    assert [mutant for mutant in _LISTED if mutant in first] == first
    assert sorted(first + second, key=lambda mutant: mutant[1]) == sorted(
        _LISTED, key=lambda mutant: mutant[1]
    )
    assert dealt(_LISTED, Deal(ShardPlace(1), ShardCount(1))) == _LISTED


def test_the_dealt_listing_hands_mutmut_its_shard_and_every_file() -> None:
    """The wrapper passes the names through and keeps the files' data, dealing the mutants."""
    asked: list[tuple[MutantName, ...]] = []

    def listing(*, mutant_names: tuple[MutantName, ...]) -> tuple[list[_Listed], Prose]:
        asked.append(mutant_names)
        return list(_LISTED), Prose("every file")

    deal = Deal(ShardPlace(2), ShardCount(3))
    mutants, files = dealing(listing, deal)(mutant_names=(_MUTANT,))
    assert asked == [(_MUTANT,)]
    assert (mutants, files) == (dealt(_LISTED, deal), "every file")


def test_main_deals_mutmuts_listing_only_when_given_a_shard(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """With ``--shard`` the module's listing is the dealt one; without, it is left as it was."""

    def listing(*, mutant_names: tuple[MutantName, ...]) -> tuple[list[_Listed], Prose]:
        _ = mutant_names
        return list(_LISTED), Prose("every file")

    for argv, wanted in (
        (["--shard", "1/2"], dealt(_LISTED, Deal(ShardPlace(1), ShardCount(2)))),
        ([], _LISTED),
    ):
        main_module = SimpleNamespace(cli=Mock(), collect_source_file_mutation_data=listing)
        modules = {
            "mutmut.runners.harness": SimpleNamespace(
                PytestRunner=SimpleNamespace(run_tests=_raising)
            ),
            "mutmut.__main__": main_module,
        }
        monkeypatch.setattr(mutation_witness, "import_module", modules.__getitem__)
        words = ["--witness-dir", str(tmp_path / "python-witness"), *argv, "run"]
        with pytest.raises(SystemExit):
            mutation_witness.main([CommandWord(word) for word in words])
        main_module.cli.main.assert_called_once_with(args=["run"], prog_name="mutmut")
        mutants, _ = main_module.collect_source_file_mutation_data(mutant_names=())
        assert mutants == wanted


def test_help_describes_the_witness_and_imports_nothing(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """``--help`` prints the description and stops before mutmut is imported."""
    importer = Mock()
    monkeypatch.setattr(mutation_witness, "import_module", importer)
    with pytest.raises(SystemExit) as stopped:
        mutation_witness.main([CommandWord("--help")])
    assert stopped.value.code == 0
    assert "mutmut, run with a witness of each mutant's run that does not return." in (
        capsys.readouterr().out
    )
    importer.assert_not_called()
