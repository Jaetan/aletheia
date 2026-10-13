# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Rust licence check holds each row of the guide's Rust section to the licence cargo records.

``licence_findings`` reads every table of ``### Runtime, Rust layer`` and no
other section's, and names a row whose licence differs from cargo's record, one
naming a crate cargo does not resolve and one with no licence cell, each at its
line; a guide without the section is refused.  ``cargo_licences`` runs
``cargo metadata --offline`` in each directory in turn, the first directory to
resolve a crate answering for it, and refuses a directory cargo cannot read,
naming it.  ``main`` reports each case on stdout and exits 0, 1 or 2 as its
docstring states.  cargo is stood in for in-process: its executable is found on
the search path and never runs, since every claim here is the module's reading
of cargo's answers, not cargo's own.
"""

from __future__ import annotations

import errno
import json
import os
import subprocess
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant
from _processes import CommandWord
from _stand_in import ScriptSource, ToolName, install_stand_in

from tools import check_rust_licences
from tools._common import RelPath
from tools.check_rust_licences import (
    DIFFERS,
    HELD,
    UNCHECKED,
    CargoUnreadError,
    CrateName,
    Platform,
    cargo_licences,
    licence_findings,
)
from tools.docs_arms import BUILDING_GUIDE

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

_NO_OUTPUT = Prose("")

_NEVER_RUNS = ScriptSource("raise SystemExit('the stand-in never runs')")
# The platform the tests' cargo resolves for.
_HOST = Platform("x86_64-unknown-linux-gnu")

_HEADER = "| Crate | License | Role |\n|---|---|---|\n"

_PYTHON_SECTION = (
    "### Runtime, Python layer\n\n"
    + "| Package | License | Role |\n|---|---|---|\n"
    + "| numpy | BSD-3-Clause | Arrays |\n"
)

_CLEAN: dict[CrateName, Prose | None] = {
    CrateName("libloading"): Prose("ISC"),
    CrateName("serde_json"): Prose("MIT OR Apache-2.0"),
    CrateName("calamine"): Prose("MIT"),
}


def _table(*rows: Prose) -> Prose:
    """Return a three-column ledger table whose body is ``rows``."""
    return Prose(_HEADER + "\n".join(rows))


def _guide(*tables: Prose) -> Prose:
    """Return a guide whose Rust section holds ``tables`` between prose, a Python section after it.

    The section's heading is line 3 and its first table's header line 7, so the
    first table's body rows are lines 9 onwards.
    """
    body = "\n\nThe optional crate's own:\n\n".join(tables)
    return Prose(
        "# Building\n\n### Runtime, Rust layer\n\nThe binding's crates:\n\n"
        + f"{body}\n\nBoth crates are edition 2021.\n\n{_PYTHON_SECTION}"
    )


# Two tables, as the real section holds: the binding's crates, then the optional crate's;
# the second table's row is line 16.
_TWO_TABLES = _guide(
    _table(
        Prose("| libloading | ISC | Runtime `dlopen` of the kernel |"),
        Prose("| serde_json | MIT OR Apache-2.0 | JSON protocol |"),
    ),
    _table(Prose("| calamine | MIT | Read `.xlsx` workbooks |")),
)


def test_rows_naming_the_licences_cargo_records_give_no_finding() -> None:
    """Both tables of the Rust section hold, and the Python section's row is never read."""
    assert not licence_findings(_TWO_TABLES, _CLEAN)


def test_a_row_whose_licence_differs_names_both_licences_at_its_line() -> None:
    """A licence other than cargo's is named with the ledger's text and cargo's, quoted."""
    recorded = _CLEAN | {CrateName("calamine"): Prose("MIT OR Apache-2.0")}
    assert licence_findings(_TWO_TABLES, recorded) == [
        Prose(
            "docs/development/BUILDING.md:16: the ledger says calamine is MIT,"
            + " cargo records 'MIT OR Apache-2.0'"
        )
    ]


def test_a_crate_cargo_records_no_licence_for_reads_as_a_differing_licence() -> None:
    """A crate cargo lists with a null licence is named, cargo's record shown as None."""
    recorded = _CLEAN | {CrateName("libloading"): None}
    assert licence_findings(_TWO_TABLES, recorded) == [
        Prose(
            "docs/development/BUILDING.md:9: the ledger says libloading is ISC, cargo records None"
        )
    ]


def test_a_row_naming_a_crate_cargo_does_not_resolve_is_named() -> None:
    """A crate absent from cargo's record is named as one cargo resolves no crate for."""
    recorded = {name: licence for name, licence in _CLEAN.items() if name != "serde_json"}
    assert licence_findings(_TWO_TABLES, recorded) == [
        Prose("docs/development/BUILDING.md:10: cargo resolves no crate serde_json")
    ]


def test_every_failing_row_is_named_in_the_order_the_guide_gives() -> None:
    """Each row is judged on its own: a differing and an unresolved row give one finding each."""
    recorded = {CrateName("libloading"): Prose("MIT"), CrateName("calamine"): Prose("MIT")}
    assert licence_findings(_TWO_TABLES, recorded) == [
        Prose(
            "docs/development/BUILDING.md:9: the ledger says libloading is ISC, cargo records 'MIT'"
        ),
        Prose("docs/development/BUILDING.md:10: cargo resolves no crate serde_json"),
    ]


def test_a_row_with_no_licence_cell_states_no_licence_whether_or_not_cargo_resolves_it() -> None:
    """A one-column table's rows have no licence cell, which is named before any record is read."""
    guide = _guide(Prose("| Crate |\n|---|\n| libloading |\n| unknown_crate |"))
    assert licence_findings(guide, _CLEAN) == [
        Prose("docs/development/BUILDING.md:9: the row for libloading states no licence"),
        Prose("docs/development/BUILDING.md:10: the row for unknown_crate states no licence"),
    ]


@pytest.mark.parametrize(
    "row",
    [Prose("| libloading | | Runtime `dlopen` of the kernel |"), Prose("| libloading |")],
    ids=["empty licence cell", "row short of its licence cell"],
)
def test_a_row_of_a_ledger_table_with_an_empty_licence_cell_states_no_licence(row: Prose) -> None:
    """A three-column row whose licence cell is empty or missing is named as stating none."""
    assert licence_findings(_guide(_table(row)), _CLEAN) == [
        Prose("docs/development/BUILDING.md:9: the row for libloading states no licence")
    ]


def test_a_crate_and_licence_in_code_spans_are_read_as_they_render() -> None:
    """The cells are compared as a reader sees them: a code span's content, emphasis dropped."""
    guide = _guide(_table(Prose("| `libloading` | **ISC** | Runtime |")))
    assert not licence_findings(guide, _CLEAN)


@pytest.mark.parametrize(
    "guide",
    [
        Prose(f"# Building\n\n{_PYTHON_SECTION}"),
        Prose(f"# Building\n\n## Runtime, Rust layer\n\n{_HEADER}| libloading | ISC | R |\n"),
    ],
    ids=["no rust heading", "rust heading at another level"],
)
def test_a_guide_without_the_rust_section_is_refused_naming_the_section(guide: Prose) -> None:
    """With no level-three Rust heading the guide is refused, its path and the heading named."""
    with pytest.raises(ValueError, match=r".") as refused:
        _ = licence_findings(guide, _CLEAN)
    assert str(refused.value) == (
        "docs/development/BUILDING.md: has no ### Runtime, Rust layer section"
    )


@dataclass(frozen=True)
class _Answer:
    """What cargo answers in one directory: its exit status and what it writes."""

    status: ExitStatus
    stdout: Prose
    stderr: Prose = _NO_OUTPUT


@dataclass(frozen=True)
class _Call:
    """One run the module asked for: its command line and its directory."""

    argv: list[CommandWord]
    cwd: Path


@dataclass
class _Cargo:
    """A stand-in for the module's ``run_capture`` of cargo, answering each directory as canned."""

    answers: dict[Path, _Answer]
    calls: list[_Call] = field(default_factory=list[_Call])

    def __call__(self, cmd: list[CommandWord], *, cwd: Path) -> subprocess.CompletedProcess[Prose]:
        """Record the run and return the directory's canned answer."""
        self.calls.append(_Call(cmd, cwd))
        answer = self.answers[cwd]
        return subprocess.CompletedProcess(cmd, answer.status, answer.stdout, answer.stderr)


def _metadata(packages: Mapping[CrateName, Prose | None]) -> _Answer:
    """Return a successful ``cargo metadata`` answer listing ``packages`` among other fields."""
    listed = [
        {"name": name, "version": "1.0.0", "license": licence, "license_file": None}
        for name, licence in packages.items()
    ]
    return _Answer(ExitStatus(0), Prose(json.dumps({"packages": listed, "version": 1})), _NO_OUTPUT)


def _install_cargo(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, answers: dict[Path, _Answer]
) -> _Cargo:
    """Put a never-run cargo first on the search path and answer its runs in-process."""
    install_stand_in(tmp_path, monkeypatch, ToolName("cargo"), _NEVER_RUNS)
    cargo = _Cargo(answers)
    monkeypatch.setattr(check_rust_licences, "run_capture", cargo)
    return cargo


def _metadata_call(tmp_path: Path, cwd: Path) -> _Call:
    """Return the run the module asks for in ``cwd``: the found cargo, read offline."""
    cargo = CommandWord(str(tmp_path / "bin" / "cargo"))
    asked = ("metadata", "--format-version", "1", "--offline", "--filter-platform", _HOST)
    words = [CommandWord(word) for word in asked]
    return _Call([cargo, *words], cwd)


def test_cargo_is_run_offline_in_each_directory_and_the_first_answers_for_a_shared_crate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Each directory is read in turn; a crate both resolve keeps the first directory's licence."""
    core, excel = tmp_path / "rust", tmp_path / "rust" / "excel"
    cargo = _install_cargo(
        tmp_path,
        monkeypatch,
        {
            core: _metadata({CrateName("libloading"): Prose("ISC"), CrateName("serde"): None}),
            excel: _metadata(
                {
                    CrateName("libloading"): Prose("MIT"),
                    CrateName("serde"): Prose("MIT OR Apache-2.0"),
                    CrateName("calamine"): Prose("MIT"),
                }
            ),
        },
    )
    assert cargo_licences([core, excel], _HOST) == {
        CrateName("libloading"): Prose("ISC"),
        CrateName("serde"): None,
        CrateName("calamine"): Prose("MIT"),
    }
    assert cargo.calls == [_metadata_call(tmp_path, core), _metadata_call(tmp_path, excel)]


def test_no_directory_gives_no_crate_and_runs_nothing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """With no directory to read, cargo records no licence and is never run."""
    cargo = _install_cargo(tmp_path, monkeypatch, {})
    assert not cargo_licences([], _HOST)
    assert not cargo.calls


def test_a_directory_cargo_cannot_read_is_refused_naming_it_and_no_later_one_is_read(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A failing run raises, naming its directory and cargo's message, and the reading stops."""
    core, excel, later = tmp_path / "rust", tmp_path / "rust" / "excel", tmp_path / "rust" / "x"
    refusal = Prose("error: no matching package named `zip` found\n")
    cargo = _install_cargo(
        tmp_path,
        monkeypatch,
        {
            core: _metadata({CrateName("libloading"): Prose("ISC")}),
            excel: _Answer(ExitStatus(101), _NO_OUTPUT, refusal),
            later: _metadata({CrateName("zip"): Prose("MIT")}),
        },
    )
    with pytest.raises(CargoUnreadError) as refused:
        _ = cargo_licences([core, excel, later], _HOST)
    assert str(refused.value) == (
        f"{excel}: cargo metadata --offline failed: error: no matching package named `zip` found"
    )
    assert cargo.calls == [_metadata_call(tmp_path, core), _metadata_call(tmp_path, excel)]


_MANIFESTS = [RelPath("rust/Cargo.toml"), RelPath("rust/excel/Cargo.toml")]


def _repo(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    tracked: list[RelPath],
    guide: Prose | None,
) -> Path:
    """Make ``tmp_path`` the repository, tracking ``tracked``, its guide ``guide`` or none."""
    if guide is not None:
        _ = plant(tmp_path, {BUILDING_GUIDE: guide})

    def git_ls_files(repo: Path) -> list[RelPath]:
        assert repo == tmp_path
        return tracked

    monkeypatch.setattr(check_rust_licences, "REPO", tmp_path)
    monkeypatch.setattr(check_rust_licences, "git_ls_files", git_ls_files)
    monkeypatch.setattr("sys.argv", ["check_rust_licences"])
    monkeypatch.setattr(check_rust_licences, "host_platform", lambda: _HOST)
    return tmp_path


def _both_read(root: Path, core: _Answer) -> dict[Path, _Answer]:
    """Answer the core directory with ``core`` and the optional crate's with its one crate."""
    return {
        root / "rust": core,
        root / "rust" / "excel": _metadata({CrateName("calamine"): Prose("MIT")}),
    }


_CORE = {CrateName("libloading"): Prose("ISC"), CrateName("serde_json"): Prose("MIT OR Apache-2.0")}


def test_main_holds_a_ledger_cargo_agrees_with(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Rows naming cargo's licences exit 0, saying so, once every manifest's directory is read."""
    root = _repo(
        tmp_path, monkeypatch, [RelPath("python/pyproject.toml"), *_MANIFESTS], _TWO_TABLES
    )
    cargo = _install_cargo(tmp_path, monkeypatch, _both_read(root, _metadata(_CORE)))
    assert check_rust_licences.main() == HELD
    assert capsys.readouterr().out == (
        "check-rust-licences: every Rust row names the licence cargo records for its crate\n"
    )
    assert [call.cwd for call in cargo.calls] == [root / "rust", root / "rust" / "excel"]


def test_main_names_each_differing_row_and_exits_1(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A row whose licence is not cargo's is printed, prefixed with the check's name, exit 1."""
    root = _repo(tmp_path, monkeypatch, _MANIFESTS, _TWO_TABLES)
    core = _CORE | {CrateName("libloading"): Prose("MIT")}
    _ = _install_cargo(tmp_path, monkeypatch, _both_read(root, _metadata(core)))
    assert check_rust_licences.main() == DIFFERS
    assert capsys.readouterr().out == (
        "check-rust-licences: docs/development/BUILDING.md:9: the ledger says libloading is ISC,"
        + " cargo records 'MIT'\n"
    )


def test_main_leaves_the_licences_unchecked_when_no_manifest_is_tracked_under_rust(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A Cargo.toml outside rust/ does not count: exit 2, and cargo is never run."""
    _ = _repo(
        tmp_path, monkeypatch, [RelPath("go/Cargo.toml"), RelPath("rust/README.md")], _TWO_TABLES
    )
    cargo = _install_cargo(tmp_path, monkeypatch, {})
    assert check_rust_licences.main() == UNCHECKED
    assert capsys.readouterr().out == (
        "check-rust-licences: no Cargo.toml is tracked under rust/; licences unchecked\n"
    )
    assert not cargo.calls


def test_main_leaves_the_licences_unchecked_when_the_guide_cannot_be_read(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A missing guide exits 2 with the read's error, before cargo is run."""
    root = _repo(tmp_path, monkeypatch, _MANIFESTS, None)
    cargo = _install_cargo(tmp_path, monkeypatch, {})
    assert check_rust_licences.main() == UNCHECKED
    missing = FileNotFoundError(errno.ENOENT, os.strerror(errno.ENOENT), str(root / BUILDING_GUIDE))
    assert capsys.readouterr().out == f"check-rust-licences: {missing}; licences unchecked\n"
    assert not cargo.calls


def test_main_leaves_the_licences_unchecked_when_the_guide_has_no_rust_section(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A guide without the Rust section exits 2, naming the section it lacks."""
    root = _repo(tmp_path, monkeypatch, _MANIFESTS, Prose(f"# Building\n\n{_PYTHON_SECTION}"))
    _ = _install_cargo(tmp_path, monkeypatch, _both_read(root, _metadata(_CORE)))
    assert check_rust_licences.main() == UNCHECKED
    assert capsys.readouterr().out == (
        "check-rust-licences: docs/development/BUILDING.md: has no ### Runtime, Rust layer"
        + " section; licences unchecked\n"
    )


def test_main_leaves_the_licences_unchecked_when_cargo_cannot_read_a_manifest(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A directory cargo cannot read offline exits 2, naming the directory and cargo's message."""
    root = _repo(tmp_path, monkeypatch, _MANIFESTS, _TWO_TABLES)
    refused = _Answer(ExitStatus(101), _NO_OUTPUT, Prose("error: no registry index\n"))
    _ = _install_cargo(tmp_path, monkeypatch, _both_read(root, refused))
    assert check_rust_licences.main() == UNCHECKED
    assert capsys.readouterr().out == (
        f"check-rust-licences: {root / 'rust'}: cargo metadata --offline failed:"
        + " error: no registry index; licences unchecked\n"
    )


def test_main_refuses_an_argument_it_does_not_take(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The command takes no argument, so one it is given is refused before any read."""
    _ = _repo(tmp_path, monkeypatch, _MANIFESTS, _TWO_TABLES)
    monkeypatch.setattr("sys.argv", ["check_rust_licences", "--registry"])
    with pytest.raises(SystemExit) as refused:
        _ = check_rust_licences.main()
    assert refused.value.code == ExitStatus(2)


def _rustc_reads(
    monkeypatch: pytest.MonkeyPatch, status: ExitStatus, out: Prose
) -> list[list[CommandWord]]:
    """Answer the module's rustc run with ``status`` and ``out``; return what it was asked."""
    asked: list[list[CommandWord]] = []

    def rustc(cmd: list[CommandWord]) -> subprocess.CompletedProcess[Prose]:
        """Record the run and answer it as rustc -vV."""
        asked.append(cmd)
        return subprocess.CompletedProcess(cmd, status, out, _NO_OUTPUT)

    monkeypatch.setattr(check_rust_licences, "find_executable", CommandWord)
    monkeypatch.setattr(check_rust_licences, "run_capture", rustc)
    return asked


def test_the_host_platform_is_the_one_rustc_names(monkeypatch: pytest.MonkeyPatch) -> None:
    """The platform the read is filtered to is rustc's ``host:`` line."""
    out = Prose("rustc 1.97.0\nbinary: rustc\nhost: x86_64-unknown-linux-gnu\nrelease: 1.97.0\n")
    asked = _rustc_reads(monkeypatch, ExitStatus(0), out)
    assert check_rust_licences.host_platform() == _HOST
    assert asked == [[CommandWord("rustc"), CommandWord("-vV")]]


@pytest.mark.parametrize(
    ("status", "out"),
    [
        (ExitStatus(0), Prose("rustc 1.97.0\nrelease: 1.97.0\n")),
        (ExitStatus(1), Prose("host: x\n")),
    ],
)
def test_a_rustc_naming_no_host_leaves_the_licences_unchecked(
    monkeypatch: pytest.MonkeyPatch, status: ExitStatus, out: Prose
) -> None:
    """A rustc that fails or prints no ``host:`` line raises rather than filtering to nothing."""
    _ = _rustc_reads(monkeypatch, status, out)
    with pytest.raises(CargoUnreadError):
        _ = check_rust_licences.host_platform()


def test_the_exit_statuses_are_the_ones_the_usage_states() -> None:
    """Held, differing and unchecked exit 0, 1 and 2, as the module's usage says."""
    assert (ExitStatus(0), ExitStatus(1), ExitStatus(2)) == (HELD, DIFFERS, UNCHECKED)


def test_main_leaves_the_licences_unchecked_when_cargo_is_not_on_the_search_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no cargo to run, cargo cannot read the metadata: exit 2, licences unchecked."""
    _ = _repo(tmp_path, monkeypatch, _MANIFESTS, _TWO_TABLES)
    empty = tmp_path / "no-tools"
    empty.mkdir()
    monkeypatch.setenv("PATH", str(empty))
    assert check_rust_licences.main() == UNCHECKED
    assert capsys.readouterr().out == (
        "check-rust-licences: required executable not found on PATH: cargo; licences unchecked\n"
    )
