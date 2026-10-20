# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``benchmarks/compare.py``: the comparison of benchmark result files, read in process.

A file is a column, named by its binding, its mode and what its name adds
beyond them. A fresh run and its committed baseline print as two columns and,
per lane, as the current mean, the baseline mean, the delta and the current
standard deviation; files of several modes print a table per mode; every
complexity label the schema pins prints whole, its column as wide as the
longest; and two files for one column are refused, both named. A load sweep
prints a table of its rate and one of the bytes a load allocated, keyed by its
size; a file without the sweep reads n/a beside one with it, and alone prints
an empty table; a row without ``allocated_bytes``, as an older file's, reads
n/a for its bytes and keeps its rate; and a byte count fits its column, beside
its baseline too. The usage names every binding the schema names and only paths
of the shape the runner writes, and the command the benchmarks guide prints
under ``Local baselines`` runs as written over a fresh file beside its
baseline.
"""

from __future__ import annotations

import json
import re
import shlex
import shutil
import sys
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, Final, NamedTuple, NewType, TypedDict, cast

import pytest
from _bench_schema import BindingId, LaneName, SweepName, schema
from _processes import CommandWord

from tools import _markdown

from aletheia.common_types import Prose
from benchmarks import compare

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence

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


# A point's size in a load sweep: the messages of a DBC, or the digits of its
# one long number.
PointSize = NewType("PointSize", int)

# Each load sweep's size column and rate column.
_COLUMNS: Final = {
    SweepName("dbc_size"): ("messages", "messages_per_sec"),
    SweepName("text_literal_length"): ("digits", "digits_per_sec"),
    SweepName("json_literal_length"): ("digits", "digits_per_sec"),
}

# The tables the load sweeps print, side by side.
_LOAD_TABLES: Final = (
    Prose("DBC Size Scaling Comparison (messages/sec)"),
    Prose("DBC Size Allocation Scaling Comparison (bytes per load)"),
    Prose("Text Literal Length Scaling Comparison (digits/sec)"),
    Prose("Text Literal Length Allocation Scaling Comparison (bytes per load)"),
    Prose("JSON Literal Length Scaling Comparison (digits/sec)"),
    Prose("JSON Literal Length Allocation Scaling Comparison (bytes per load)"),
)


class _Point(NamedTuple):
    """A point of a load sweep: its size, its rate and the bytes its load allocated."""

    size: PointSize
    rate: compare.SweepValue
    allocated: compare.ByteCount


def _write_scaling(path: Path, sweeps: Mapping[SweepName, Sequence[_Point]]) -> Path:
    """Write a scaling result file holding these load sweeps and no other, in the fields read."""
    results = {
        sweep: [
            {
                _COLUMNS[sweep][0]: p.size,
                _COLUMNS[sweep][1]: p.rate,
                "allocated_bytes": p.allocated,
            }
            for p in points
        ]
        for sweep, points in sweeps.items()
    }
    language = path.name.split("_", 1)[0]
    payload = {"benchmark": "scaling", "language": language, "results": results}
    _ = path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def _load_sweeps(allocated: compare.ByteCount) -> dict[SweepName, list[_Point]]:
    """Every load sweep at two sizes each, every load allocating ``allocated`` bytes."""
    return {
        SweepName("dbc_size"): [
            _Point(PointSize(2500), compare.SweepValue(80_000.0), allocated),
            _Point(PointSize(5000), compare.SweepValue(79_000.0), allocated),
        ],
        SweepName("text_literal_length"): [
            _Point(PointSize(25000), compare.SweepValue(5_000_000.0), allocated),
            _Point(PointSize(50000), compare.SweepValue(4_900_000.0), allocated),
        ],
        SweepName("json_literal_length"): [
            _Point(PointSize(25000), compare.SweepValue(6_000_000.0), allocated),
            _Point(PointSize(50000), compare.SweepValue(5_900_000.0), allocated),
        ],
    }


def test_a_load_sweep_prints_its_rate_and_its_allocation_by_its_size(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Each load sweep prints its rate and, apart, its allocation, a row per size."""
    fresh = _write_scaling(tmp_path / "cpp_scaling.json", _load_sweeps(compare.ByteCount(3_000)))

    tables = _tables(_compare(monkeypatch, capsys, [fresh]))

    printed = {
        title: [row.split() for row in tables[title] if set(row) != {"-"}] for title in _LOAD_TABLES
    }
    assert printed == {
        _LOAD_TABLES[0]: [["messages", "cpp"], ["2,500", "80,000"], ["5,000", "79,000"]],
        _LOAD_TABLES[1]: [["messages", "cpp"], ["2,500", "3,000"], ["5,000", "3,000"]],
        _LOAD_TABLES[2]: [["digits", "cpp"], ["25,000", "5,000,000"], ["50,000", "4,900,000"]],
        _LOAD_TABLES[3]: [["digits", "cpp"], ["25,000", "3,000"], ["50,000", "3,000"]],
        _LOAD_TABLES[4]: [["digits", "cpp"], ["25,000", "6,000,000"], ["50,000", "5,900,000"]],
        _LOAD_TABLES[5]: [["digits", "cpp"], ["25,000", "3,000"], ["50,000", "3,000"]],
    }


def test_a_file_without_a_load_sweep_reads_n_a_or_an_empty_table(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Beside a file with the sweep, one without it reads n/a; alone, its table has no row."""
    carrying = _write_scaling(tmp_path / "cpp_scaling.json", _load_sweeps(compare.ByteCount(3_000)))
    lacking = _write_scaling(tmp_path / "go_scaling.json", {})

    beside = _tables(_compare(monkeypatch, capsys, [carrying, lacking]))
    alone = _tables(_compare(monkeypatch, capsys, [lacking]))

    for title in _LOAD_TABLES:
        rows = beside[title][2:]
        assert len(rows) == len(("small", "large")), title
        assert [row.split()[-1] for row in rows] == ["n/a", "n/a"], title
        assert alone[title][2:] == [], title


def test_a_byte_count_fits_its_column(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A byte count wider than the column floor widens its column, beside its baseline too."""
    fresh = _write_scaling(
        tmp_path / "cpp_scaling.json", _load_sweeps(compare.ByteCount(125_000_000_000))
    )
    baseline = _write_scaling(
        tmp_path / "cpp_scaling_baseline.json", _load_sweeps(compare.ByteCount(100_000_000_000))
    )

    tables = _tables(_compare(monkeypatch, capsys, [fresh, baseline]))

    sweeps = (
        ("DBC Size", "2,500"),
        ("Text Literal Length", "25,000"),
        ("JSON Literal Length", "25,000"),
    )
    for sweep, size in sweeps:
        side = tables[Prose(f"{sweep} Allocation Scaling Comparison (bytes per load)")]
        against = tables[
            Prose(f"cpp {sweep} Allocation scaling against its baseline (bytes per load)")
        ]
        assert side[2].split() == [size, "125,000,000,000", "100,000,000,000"]
        assert against[2].split() == [size, "125,000,000,000", "100,000,000,000", "+25.0%"]
        for table in (side, against):
            assert {len(line) for line in table} == {len(table[0])}, table


def test_a_row_without_its_allocation_reads_n_a(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A ``dbc_size`` row without ``allocated_bytes``, as an older file's, reads n/a for its bytes.

    Its rate is still read, beside the fresh file and against it.
    """
    fresh = _write_scaling(tmp_path / "cpp_scaling.json", _load_sweeps(compare.ByteCount(3_000)))
    older_rows = [
        {"messages": p.size, "messages_per_sec": p.rate}
        for p in _load_sweeps(compare.ByteCount(3_000))[SweepName("dbc_size")]
    ]
    older = tmp_path / "cpp_scaling_baseline.json"
    payload = {"benchmark": "scaling", "language": "cpp", "results": {"dbc_size": older_rows}}
    _ = older.write_text(json.dumps(payload), encoding="utf-8")

    tables = _tables(_compare(monkeypatch, capsys, [fresh, older]))

    side = Prose("DBC Size Allocation Scaling Comparison (bytes per load)")
    against = Prose("cpp DBC Size Allocation scaling against its baseline (bytes per load)")
    rate = Prose("cpp DBC Size scaling against its baseline (messages/sec)")
    printed = {title: [row.split() for row in tables[title][2:]] for title in (side, against, rate)}
    assert printed == {
        side: [["2,500", "3,000", "n/a"], ["5,000", "3,000", "n/a"]],
        against: [["2,500", "n/a", "n/a", "n/a"], ["5,000", "n/a", "n/a", "n/a"]],
        rate: [["2,500", "80,000", "80,000", "+0.0%"], ["5,000", "79,000", "79,000", "+0.0%"]],
    }


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
