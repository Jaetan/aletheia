# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_stability_bench``: every row is held by its read alone.

A row reads the file its ``source_file`` names, or its binding's harness when it
names none.  Its marker is spelled there once, reaching into code, since a
comment or a docstring that named the read would keep the row green with the
read gone; every row of the spec is held to that, and to failing once its
marker is gone.  A row a harness reports is named as the report names it.  The
gate is pointed at a copy of the tree, or at a planted one.
"""

from __future__ import annotations

import io
import re
import shutil
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType, NotRequired, TypedDict, cast

import pytest
import yaml

from tools import check_stability_bench
from tools._determinism_reading import BlankedCode, blank_cpp, blank_go, blank_python
from tools._determinism_syntax import SourceText

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from tools._common import RelPath

SourceMarker = NewType("SourceMarker", str)


class _Row(TypedDict):
    """One sub-check row of the spec, as the gate reads it."""

    name: Prose
    source_file: NotRequired[RelPath]
    source_marker: SourceMarker


class _Binding(TypedDict):
    """One binding of the spec: its harness and its rows."""

    harness: RelPath
    sub_checks: list[_Row]


class _Spec(TypedDict):
    """The part of the spec the tests read."""

    bindings: dict[Prose, _Binding]


class _SpecRow(NamedTuple):
    """One row of the spec: its binding, its name, the file the gate reads for it and its marker."""

    binding: Prose
    name: Prose
    source: Path
    marker: SourceMarker


class _ReportWriter(NamedTuple):
    """The file that writes a binding's report and how it names a sub-check, ``{}`` the name."""

    path: Path
    namings: tuple[Prose, ...]


_REPO = check_stability_bench.REPO_ROOT
_SPEC = Path("docs/STABILITY_BENCH.yaml")
_BINDINGS = cast("_Spec", yaml.safe_load((_REPO / _SPEC).read_text(encoding="utf-8")))["bindings"]
_ROWS = [
    _SpecRow(
        binding, row["name"], Path(row.get("source_file", spec["harness"])), row["source_marker"]
    )
    for binding, spec in _BINDINGS.items()
    for row in spec["sub_checks"]
]
# The spec and every file the gate reads: each binding's harness and each row's file.
_TREE = (
    _SPEC,
    *sorted({Path(spec["harness"]) for spec in _BINDINGS.values()} | {row.source for row in _ROWS}),
)
# Each binding's report writer, whose sub-check names the rows carry.  The agda rows
# name the runner's heap-profile steps, which no harness reports.
_REPORT_WRITERS = {
    Prose("python"): _ReportWriter(
        Path("python/benchmarks/stability.py"), (Prose('"name": "{}",'),)
    ),
    Prose("go"): _ReportWriter(
        Path("go/benchmarks/stability/main.go"), (Prose('Name: "{}",'), Prose('exact("{}",'))
    ),
    Prose("cpp"): _ReportWriter(
        Path("cpp/benchmarks/stability_report.hpp"), (Prose('.name = "{}",'),)
    ),
}
_UNREPORTED = Prose("agda")
_REPORTED = [row for row in _ROWS if row.binding != _UNREPORTED]
# A comment or a literal is blanked to spaces, so a marker spelled in one alone
# reads as a run of spaces in the code.
_BLANKED = re.compile(" +")

_PLANTED_SPEC = """\
version: 1
bindings:
  demo:
    harness: harness.txt
    sub_checks:
      - name: here
        gate: hard_zero
        source_marker: "in_harness()"
      - name: there
        gate: hard_zero
        source_file: {source_file}
        source_marker: "in_other()"
"""


def _point_gate_at(root: Path, monkeypatch: pytest.MonkeyPatch) -> io.StringIO:
    """Make the gate read the tree under ``root``, and return what its stderr is written to."""
    monkeypatch.setattr(check_stability_bench, "REPO_ROOT", root)
    monkeypatch.setattr(check_stability_bench, "SPEC_PATH", root / _SPEC)
    monkeypatch.setattr("sys.argv", ["check_stability_bench"])
    stderr = io.StringIO()
    monkeypatch.setattr(sys, "stderr", stderr)
    return stderr


def _copy_tree(root: Path) -> None:
    """Copy the spec and every file the gate reads under ``root``."""
    for rel in _TREE:
        target = root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        _ = shutil.copyfile(_REPO / rel, target)


def _code(source: Path, text: SourceText) -> BlankedCode:
    """Return ``text`` as code alone, its comments and literals blanked with every offset kept."""
    if source.suffix == ".py":
        return blank_python(text)
    if source.suffix == ".go":
        return blank_go(text)
    assert source.suffix in {".cpp", ".hpp"}, f"no reading of {source} as code"
    return blank_cpp(text)


def _plant(root: Path, source_file: Prose, harness: Prose, other: Prose) -> None:
    """Plant a spec whose second row names ``source_file``, and the two files it may read."""
    (root / _SPEC).parent.mkdir(parents=True)
    _ = (root / _SPEC).write_text(_PLANTED_SPEC.format(source_file=source_file))
    _ = (root / "harness.txt").write_text(harness)
    _ = (root / "other.txt").write_text(other)


def test_the_tree_as_it_stands_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """The copy holds every file the spec reads, and every marker is found."""
    _copy_tree(tmp_path)
    stderr = _point_gate_at(tmp_path, monkeypatch)
    assert check_stability_bench.main() == 0
    assert not stderr.getvalue()


@pytest.mark.parametrize("row", _ROWS, ids=[f"{row.binding}/{row.name}" for row in _ROWS])
def test_a_row_is_held_by_its_read_alone(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, row: _SpecRow
) -> None:
    """The marker is spelled once in its row's file, in code; the file without it fails the row."""
    text = (_REPO / row.source).read_text(encoding="utf-8")
    assert text.count(row.marker) == 1
    start = text.index(row.marker)
    code = _code(row.source, SourceText(text))
    assert not _BLANKED.fullmatch(code, start, start + len(row.marker))
    _copy_tree(tmp_path)
    _ = (tmp_path / row.source).write_text(text.replace(row.marker, ""), encoding="utf-8")
    stderr = _point_gate_at(tmp_path, monkeypatch)
    assert check_stability_bench.main() == 1
    missing = f"[{row.binding}/{row.name}] marker {row.marker!r} not found in {row.source}"
    assert missing in stderr.getvalue()


@pytest.mark.parametrize("row", _REPORTED, ids=[f"{row.binding}/{row.name}" for row in _REPORTED])
def test_a_row_is_named_as_its_harness_reports_the_sub_check(row: _SpecRow) -> None:
    """A row's name is the name its binding's report writer gives one sub-check."""
    writer = _REPORT_WRITERS[row.binding]
    text = (_REPO / writer.path).read_text(encoding="utf-8")
    assert sum(text.count(naming.format(row.name)) for naming in writer.namings) == 1


def test_a_row_reads_its_source_file_and_otherwise_its_harness(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Each marker is found only in the file its row reads."""
    _plant(tmp_path, Prose("other.txt"), Prose("in_harness();\n"), Prose("in_other();\n"))
    stderr = _point_gate_at(tmp_path, monkeypatch)
    assert check_stability_bench.main() == 0
    assert not stderr.getvalue()


def test_a_marker_in_the_file_its_row_does_not_read_fails_the_row(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """With the markers swapped between the two files, both rows fail, each naming its file."""
    _plant(tmp_path, Prose("other.txt"), Prose("in_other();\n"), Prose("in_harness();\n"))
    stderr = _point_gate_at(tmp_path, monkeypatch)
    assert check_stability_bench.main() == 1
    assert "[demo/here] marker 'in_harness()' not found in harness.txt" in stderr.getvalue()
    assert "[demo/there] marker 'in_other()' not found in other.txt" in stderr.getvalue()


def test_a_source_file_that_does_not_exist_fails_its_row(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A row naming a missing file fails, even with its marker in the harness."""
    _plant(tmp_path, Prose("absent.txt"), Prose("in_harness(); in_other();\n"), Prose(""))
    stderr = _point_gate_at(tmp_path, monkeypatch)
    assert check_stability_bench.main() == 1
    assert "[demo/there] source file does not exist: absent.txt" in stderr.getvalue()


@pytest.mark.parametrize("source_file", [Prose('""'), Prose("3")], ids=["empty", "number"])
def test_a_source_file_that_names_no_path_fails_its_row(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, source_file: Prose
) -> None:
    """An empty or non-text ``source_file`` fails its row rather than reading the harness."""
    _plant(tmp_path, source_file, Prose("in_harness(); in_other();\n"), Prose(""))
    stderr = _point_gate_at(tmp_path, monkeypatch)
    assert check_stability_bench.main() == 1
    assert "[demo/there] 'source_file' must name a file" in stderr.getvalue()


def test_a_binding_whose_harness_does_not_exist_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A missing harness fails its binding before any row is read."""
    _plant(tmp_path, Prose("other.txt"), Prose(""), Prose("in_harness(); in_other();\n"))
    (tmp_path / "harness.txt").unlink()
    stderr = _point_gate_at(tmp_path, monkeypatch)
    assert check_stability_bench.main() == 1
    assert "[demo] harness file does not exist: harness.txt" in stderr.getvalue()
