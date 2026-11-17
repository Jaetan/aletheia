# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-place gate loads libclang from the toolchain's path, or exits 2 naming it.

A gate that cannot read the C++ binding refuses rather than passing over it: a
path nothing loads from ends the gate with exit 2 and a message naming that
path and the package that installs it, and a path that loads is the one the
gate hands its reader.  Every job running the sweep the gate is part of
installs that package.  The flags each file is parsed with are its command's in
the compile database, a header taking ``cpp/src/client.cpp``'s, and the C++
reader exits 2 as well where the library or the database is missing.
"""

from __future__ import annotations

import json
from ctypes import CDLL
from typing import TYPE_CHECKING, NewType, TypedDict, cast

import pytest
import yaml
from _repo_root import REPO_ROOT

from tools import _reply_places_cpp_tree
from tools._reply_places_cpp import cpp_reader
from tools._reply_places_cpp_tree import (
    COMPILE_COMMANDS,
    LIBCLANG,
    compile_arguments,
    compile_commands,
    libclang,
)

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.common_types import Prose

# A step's shell text and a job's name.
ShellText = NewType("ShellText", str)
JobName = NewType("JobName", str)
# A compile database's JSON text.
JsonText = NewType("JsonText", str)

# The Debian package of the Clang 23 toolchain that installs LIBCLANG.
_LIBCLANG_PACKAGE = "libclang1-23"


class _Step(TypedDict, total=False):
    run: ShellText


class _Job(TypedDict, total=False):
    steps: list[_Step]


class _Workflow(TypedDict, total=False):
    jobs: dict[JobName, _Job]


def test_a_library_that_does_not_load_ends_the_gate_with_exit_2_naming_its_path(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """The loader's refusal of a missing file is the gate's, with the path and its package."""
    missing = tmp_path / "libclang-23.so.23"
    with pytest.raises(OSError, match="libclang-23") as loader:
        _ = CDLL(missing)
    monkeypatch.setattr(_reply_places_cpp_tree, "LIBCLANG", missing)
    with pytest.raises(SystemExit) as exited:
        _ = libclang()
    assert exited.value.code == 2
    assert capsys.readouterr().err == (
        f"check-limits-parity: libclang does not load from {missing}: {loader.value}"
        + "; the Clang 23 toolchain's libclang1-23 package installs it\n"
    )


def test_a_library_that_loads_is_the_path_the_gate_reads_with(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The toolchain's path is loaded, and returned once it loads."""
    loaded: list[Path] = []

    def load(name: Path) -> None:
        loaded.append(name)

    monkeypatch.setattr(_reply_places_cpp_tree, "CDLL", load)
    assert libclang() == LIBCLANG
    assert loaded == [LIBCLANG]


def test_a_missing_compile_database_ends_the_gate_with_exit_2_naming_its_path(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """With cpp/build not configured, the gate has no flags to read the C++ binding with."""
    missing = tmp_path / "cpp" / "build" / "compile_commands.json"
    monkeypatch.setattr(_reply_places_cpp_tree, "COMPILE_COMMANDS", missing)
    with pytest.raises(SystemExit) as exited:
        _ = compile_commands()
    assert exited.value.code == 2
    assert capsys.readouterr().err == (
        f"check-limits-parity: {missing} is missing; configure cpp/build, which writes it\n"
    )


def test_a_compile_database_present_is_the_one_the_gate_reads_flags_from(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The database the configure of cpp/build writes is returned once it is there."""
    database = tmp_path / "compile_commands.json"
    _ = database.write_text("[]\n", encoding="utf-8")
    monkeypatch.setattr(_reply_places_cpp_tree, "COMPILE_COMMANDS", database)
    assert compile_commands() == database
    assert REPO_ROOT / "cpp" / "build" / "compile_commands.json" == COMPILE_COMMANDS


def test_every_job_running_the_sweep_installs_the_package_holding_libclang() -> None:
    """A job running ``tools.run_ci`` names the package among the toolchain's it installs."""
    sweeps = 0
    for path in sorted((REPO_ROOT / ".github" / "workflows").glob("*.y*ml")):
        workflow = cast("_Workflow", yaml.safe_load(path.read_text(encoding="utf-8")))
        for name, job in workflow.get("jobs", {}).items():
            runs = [step.get("run", ShellText("")) for step in job.get("steps", [])]
            if not any("-m tools.run_ci" in run for run in runs):
                continue
            sweeps += 1
            installs = [run.split() for run in runs if "cpp/toolchain/install.sh" in run]
            assert any(_LIBCLANG_PACKAGE in words for words in installs), f"{path.name}:{name}"
    assert sweeps > 0


def _with_database(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, written: JsonText) -> Path:
    """Have the gate read the compile database ``written`` from a file of its own; return it."""
    database = tmp_path / "compile_commands.json"
    _ = database.write_text(written, encoding="utf-8")
    monkeypatch.setattr(_reply_places_cpp_tree, "COMPILE_COMMANDS", database)
    return database


def test_a_file_is_parsed_with_its_command_but_the_compiler_the_output_and_the_file(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The command's words after the compiler, ``-o`` and its operand, ``-c`` and the file aside."""
    source = tmp_path / "a.cpp"
    command = f"/usr/bin/clang++-23 -DX -o out.o -c {source} -I/inc"
    written = JsonText(json.dumps([{"file": str(source), "command": command}]))
    _ = _with_database(monkeypatch, tmp_path, written)
    assert compile_arguments(source) == ("-DX", "-I/inc")


def test_a_command_given_as_arguments_is_read_as_given(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """An entry listing its arguments is read from that list."""
    source = tmp_path / "a.cpp"
    arguments = ["clang++", "-DY", "-c", str(source)]
    written = JsonText(json.dumps([{"file": str(source), "arguments": arguments}]))
    _ = _with_database(monkeypatch, tmp_path, written)
    assert compile_arguments(source) == ("-DY",)


def test_a_file_the_database_names_no_command_for_takes_the_library_unit_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A header, which no command compiles, is parsed as ``cpp/src/client.cpp`` is compiled."""
    client = REPO_ROOT / "cpp" / "src" / "client.cpp"
    written = JsonText(json.dumps([{"file": str(client), "command": f"clang++ -DZ -c {client}"}]))
    _ = _with_database(monkeypatch, tmp_path, written)
    assert compile_arguments(tmp_path / "a.hpp") == ("-DZ",)


def test_a_file_the_database_names_a_command_for_takes_its_own_over_the_library_unit_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A file with a command of its own is parsed with it, ``cpp/src/client.cpp``'s aside."""
    client = REPO_ROOT / "cpp" / "src" / "client.cpp"
    source = tmp_path / "a.cpp"
    entries = [
        {"file": str(client), "command": f"clang++ -DZ -c {client}"},
        {"file": str(source), "command": f"clang++ -DW -c {source}"},
    ]
    _ = _with_database(monkeypatch, tmp_path, JsonText(json.dumps(entries)))
    assert compile_arguments(source) == ("-DW",)


def test_a_database_naming_neither_ends_the_gate_with_exit_2(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], tmp_path: Path
) -> None:
    """With no command for the file nor for ``cpp/src/client.cpp``, the gate has no flags."""
    database = _with_database(monkeypatch, tmp_path, JsonText("[]"))
    header = tmp_path / "a.hpp"
    with pytest.raises(SystemExit) as exited:
        _ = compile_arguments(header)
    assert exited.value.code == 2
    client = REPO_ROOT / "cpp" / "src" / "client.cpp"
    assert capsys.readouterr().err == (
        f"check-limits-parity: {database} names no command for {client},"
        + f" whose flags {header} is parsed with\n"
    )


def test_the_cpp_reader_ends_the_gate_with_exit_2_where_libclang_does_not_load(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The reader loads libclang before it parses, so a missing library is the gate's exit 2."""
    monkeypatch.setattr(_reply_places_cpp_tree, "LIBCLANG", tmp_path / "libclang-23.so.23")
    with pytest.raises(SystemExit) as exited:
        _ = cpp_reader(frozenset())([])
    assert exited.value.code == 2


def test_the_cpp_reader_ends_the_gate_with_exit_2_where_the_compile_database_is_missing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The reader reads each file's flags from the database, so a missing one is exit 2."""
    monkeypatch.setattr(_reply_places_cpp_tree, "COMPILE_COMMANDS", tmp_path / "missing.json")
    with pytest.raises(SystemExit) as exited:
        _ = cpp_reader(frozenset())([])
    assert exited.value.code == 2
