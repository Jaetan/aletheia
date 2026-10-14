# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``benchmarks/compare.py``: the comparison of benchmark result files, read in process.

A file is a column, named by its binding, its mode and what its name adds
beyond them. A fresh run and its committed baseline print as two columns and,
per lane, as the current mean, the baseline mean, the delta and the current
standard deviation; files of several modes print a table per mode; every
complexity label the schema pins prints whole, its column as wide as the
longest; and two files for one column are refused, both named. The usage names
every binding the schema names and only paths of the shape the runner writes,
and the command the benchmarks guide prints under ``Local baselines`` runs as
written over a fresh file beside its baseline.
"""

from __future__ import annotations

import json
import re
import shlex
import shutil
import sys
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, Final, NewType, TypedDict, cast

import pytest
from _bench_schema import BindingId, LaneName, schema
from _processes import CommandWord

from tools import _markdown

from aletheia.common_types import Prose
from benchmarks import compare

if TYPE_CHECKING:
    from collections.abc import Sequence

_REPO: Final = Path(__file__).resolve().parents[2]
_RESULTS: Final = _REPO / "benchmarks" / "results"
_GUIDE: Final = _REPO / "docs" / "development" / "BENCHMARKS.md"
_CPP_THROUGHPUT: Final = "cpp_throughput_baseline.json"

# The name each binding the schema lists goes by in prose.
_NAMES: Final = {
    BindingId("cpp"): Prose("C++"),
    BindingId("go"): Prose("Go"),
    BindingId("python"): Prose("Python"),
    BindingId("rust"): Prose("Rust"),
}

# A lane's frames per second, as a throughput result file records it.
FramesPerSecond = NewType("FramesPerSecond", float)


class _Lane(TypedDict):
    """One lane of a throughput result file."""

    name: LaneName
    fps_mean: FramesPerSecond
    fps_stdev: FramesPerSecond


class _Throughput(TypedDict):
    """A throughput result file, in the field the tests change."""

    results: list[_Lane]


def _compare(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], files: Sequence[Path]
) -> Prose:
    """Run the comparison over ``files`` and return what it printed."""
    monkeypatch.setattr(sys, "argv", ["benchmarks/compare.py", *map(str, files)])
    assert compare.main() == 0
    return Prose(capsys.readouterr().out)


def _tables(out: Prose) -> dict[Prose, list[Prose]]:
    """Each table printed, by its title: its header, its rule and its rows.

    A title is the line between two rules of ``=``; the table runs from the
    line after the second rule to the next empty line.
    """
    lines = list(map(Prose, out.splitlines()))
    tables: dict[Prose, list[Prose]] = {}
    for i, line in enumerate(lines[1:-1], start=1):
        if set(lines[i - 1]) == {"="} and set(lines[i + 1]) == {"="}:
            end = lines.index("", i + 2)
            tables[line] = lines[i + 2 : end]
    return tables


def test_a_fresh_run_prints_beside_its_baseline(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A fresh file and its baseline are two columns, and each lane reads +10.0% against it."""
    baseline = tmp_path / _CPP_THROUGHPUT
    _ = shutil.copy(_RESULTS / _CPP_THROUGHPUT, baseline)
    data = cast("_Throughput", json.loads(baseline.read_text(encoding="utf-8")))
    for row in data["results"]:
        row["fps_mean"] = FramesPerSecond(round(row["fps_mean"] * 1.1, 1))
    fresh = tmp_path / "cpp_throughput.json"
    _ = fresh.write_text(json.dumps(data), encoding="utf-8")
    base = cast("_Throughput", json.loads(baseline.read_text(encoding="utf-8")))

    tables = _tables(_compare(monkeypatch, capsys, [fresh, baseline]))

    assert tables[Prose("Throughput Comparison (frames/sec)")][0].split() == [
        "Benchmark",
        "cpp",
        "cpp",
        "baseline",
    ]
    against = tables[Prose("cpp throughput against its baseline (frames/sec)")]
    assert against[0].split() == ["Benchmark", "current", "baseline", "delta", "stdev"]
    rows = against[2:]
    assert len(rows) == len(base["results"])
    for row, cur, old in zip(rows, data["results"], base["results"], strict=True):
        assert row.startswith(cur["name"])
        assert row.removeprefix(cur["name"]).split() == [
            f"{cur['fps_mean']:,.0f}",
            f"{old['fps_mean']:,.0f}",
            "+10.0%",
            f"{cur['fps_stdev']:,.0f}",
        ]


def test_every_mode_given_prints_its_table(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Every committed baseline at once: a table per mode, each with every binding's column."""
    tables = _tables(_compare(monkeypatch, capsys, sorted(_RESULTS.glob("*_baseline.json"))))

    for mode in schema()["envelope"]["benchmarks"]:
        titled = [title for title in tables if f"{mode.title()} Comparison" in title]
        assert titled, f"no {mode} table"
        for title in titled:
            header = tables[title][0]
            for binding in schema()["envelope"]["languages"]:
                assert f"{binding} baseline" in header, f"{title}: {binding}"


def test_the_usage_names_the_bindings_and_the_runner_paths() -> None:
    """The docstring names every binding, and each path it shows is one the runner writes."""
    usage = compare.__doc__
    assert usage is not None
    envelope = schema()["envelope"]
    assert set(_NAMES) == set(envelope["languages"])
    for name in _NAMES.values():
        assert re.search(rf"(?<!\w){re.escape(name)}(?!\w)", usage), name
    bindings, modes = "|".join(envelope["languages"]), "|".join(envelope["benchmarks"])
    shape = re.compile(rf"benchmarks/results/(?:\*|{bindings})_(?:{modes})(?:_baseline|\*)?\.json")
    paths = re.findall(r"\S+\.json", usage)
    assert paths
    assert [path for path in paths if not shape.fullmatch(path)] == []


def test_every_complexity_label_prints_whole(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Each label heads its row whole, and every row is as wide as the header."""
    tables = _tables(
        _compare(monkeypatch, capsys, sorted(_RESULTS.glob("*_scaling_baseline.json")))
    )
    [table] = [lines for lines in tables.values() if lines[0].split()[0] == "complexity"]
    header, rows = table[0], table[2:]

    for label in schema()["modes"]["scaling"]["complexity_labels"]:
        assert [row for row in rows if re.match(rf"\s*{re.escape(label)}\s", row)], label
    assert {len(row) for row in rows} == {len(header)}


def test_two_files_for_one_column_are_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """One baseline copied into two directories: exit 1, both paths named."""
    first, second = tmp_path / "a" / _CPP_THROUGHPUT, tmp_path / "b" / _CPP_THROUGHPUT
    for path in (first, second):
        path.parent.mkdir()
        _ = shutil.copy(_RESULTS / _CPP_THROUGHPUT, path)
    monkeypatch.setattr(sys, "argv", ["benchmarks/compare.py", str(first), str(second)])

    with pytest.raises(SystemExit) as exited:
        _ = compare.main()

    assert exited.value.code == 1
    err = capsys.readouterr().err
    assert str(first) in err
    assert str(second) in err


def _guide_command() -> list[CommandWord]:
    """Return the one comparison command the guide's ``Local baselines`` section prints."""
    text = Prose(_GUIDE.read_text(encoding="utf-8"))
    found = _markdown.section(text, Prose("## Local baselines"))
    assert found is not None
    body = Prose("\n".join(_markdown.lines(text)[found.first - 1 : found.end - 1]))
    commands = [
        list(map(CommandWord, shlex.split(line)))
        for block in _markdown.code_blocks(body)
        for line in block.splitlines()
        if "benchmarks/compare.py" in line
    ]
    assert len(commands) == 1, commands
    return commands[0]


def test_the_guide_s_comparison_command_runs_as_written(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The guide's command, over a fresh copy beside each baseline its glob names."""
    argv = _guide_command()
    assert argv[:2] == ["python/.venv/bin/python", "benchmarks/compare.py"]
    assert (_REPO / argv[1]).resolve() == Path(compare.__file__).resolve()
    files: list[Path] = []
    pairs: list[Prose] = []
    for pattern in map(PurePosixPath, argv[2:]):
        assert pattern.parent == PurePosixPath("benchmarks/results"), pattern
        baselines = [
            path for path in _RESULTS.glob(pattern.name) if path.stem.endswith("_baseline")
        ]
        assert baselines, f"{pattern} names no committed baseline"
        for baseline in baselines:
            current = baseline.stem.removesuffix("_baseline")
            _ = shutil.copy(baseline, tmp_path / baseline.name)
            _ = shutil.copy(baseline, tmp_path / f"{current}.json")
            pairs.append(Prose(current.replace("_", " ", 1)))
        files += sorted(tmp_path.glob(pattern.name))

    titles = _tables(_compare(monkeypatch, capsys, files))

    for pair in pairs:
        assert [title for title in titles if title.startswith(f"{pair} against its baseline")]
