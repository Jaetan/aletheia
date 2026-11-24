# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every build of the tree uses the one Go and the one Rust the tree pins.

``.go-version`` names Go, which every workflow's ``actions/setup-go`` step reads.
``rust-toolchain.toml`` names Rust, which ``tools/install_rust_toolchain.sh``
installs on a runner and makes the default, and which no workflow step installs
another way. ``tools.check_toolchain_pins`` refuses a machine whose Go, or whose
Rust inside the tree or outside it, is another, and reports a clang of another
upstream without failing.
"""

from __future__ import annotations

import os
import re
from pathlib import Path
from typing import NewType, TypedDict, cast

import pytest
import yaml
from _ci_runner import ci_runner

from tools import check_toolchain_pins as pins
from tools._ci_steps import register_all_steps
from tools._common import find_executable, run_capture
from tools.benchmark_scope import BENCHMARK_GLOBAL_PATHS

from aletheia.common_types import ExitStatus, Prose

# A step's shell text, an action reference, a line a program prints, and a job's label.
ShellText = NewType("ShellText", str)
ActionRef = NewType("ActionRef", str)
OutputLine = NewType("OutputLine", str)
JobName = NewType("JobName", str)
# A version a stand-in compiler reports, a Rust component, and a toolchain file's text.
Reported = NewType("Reported", str)
Component = NewType("Component", str)
ToolchainText = NewType("ToolchainText", str)
# A setup-go input's name and value.
InputName = NewType("InputName", str)
InputValue = NewType("InputValue", str)

_Step = TypedDict(
    "_Step", {"uses": ActionRef, "run": ShellText, "with": dict[InputName, InputValue]}, total=False
)


class _Job(TypedDict, total=False):
    steps: list[_Step]


class _Workflow(TypedDict, total=False):
    jobs: dict[JobName, _Job]


_REPO = Path(__file__).resolve().parents[2]
_WORKFLOWS = _REPO / ".github" / "workflows"
_SCRIPT = _REPO / "tools" / "install_rust_toolchain.sh"
_A_SHELL_RUNS_THE_SCRIPT = "only bash runs what the install script asks of rustup"
_THE_GATE_ASKS_COMPILERS = "the gate reads each compiler's report from a program it starts"


def _steps() -> list[tuple[JobName, _Step]]:
    """Return every step of every workflow, with its job named ``workflow:job``."""
    found: list[tuple[JobName, _Step]] = []
    for path in sorted(_WORKFLOWS.glob("*.y*ml")):
        workflow = cast("_Workflow", yaml.safe_load(path.read_text(encoding="utf-8")))
        for name, job in workflow.get("jobs", {}).items():
            found.extend((JobName(f"{path.name}:{name}"), step) for step in job.get("steps", []))
    return found


def test_every_go_setup_reads_the_pinned_version() -> None:
    """Each setup-go step reads .go-version and names no version of its own."""
    setups = [
        (job, step)
        for job, step in _steps()
        if step.get("uses", "").startswith("actions/setup-go@")
    ]
    assert setups
    for job, step in setups:
        given = step.get("with", {})
        assert given.get(InputName("go-version-file")) == ".go-version", job
        assert InputName("go-version") not in given, job


def test_no_step_installs_rust_but_through_the_script() -> None:
    """No workflow step asks rustup for a toolchain itself; Rust is set up by the script."""
    through = 0
    for job, step in _steps():
        run = step.get("run", "")
        assert "rustup toolchain install" not in run, job
        assert "rustup default" not in run, job
        assert "rustup update" not in run, job
        through += "tools/install_rust_toolchain.sh" in run
    assert through > 0


def _install(
    tmp_path: Path, toolchain: ToolchainText, components: list[Component]
) -> tuple[ExitStatus, list[OutputLine]]:
    """Run the script beside ``toolchain`` as its toolchain file; return what reached rustup."""
    tools = tmp_path / "tools"
    tools.mkdir()
    script = tools / "install_rust_toolchain.sh"
    _ = script.write_text(_SCRIPT.read_text(encoding="utf-8"), encoding="utf-8")
    script.chmod(0o755)
    _ = (tmp_path / "rust-toolchain.toml").write_text(toolchain, encoding="utf-8")
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    for name in ("rustup", "rustc", "cargo"):
        stand_in = bin_dir / name
        _ = stand_in.write_text(
            '#!/bin/sh\necho "$(basename "$0") $*" >> "$CALLS"\n', encoding="utf-8"
        )
        stand_in.chmod(0o755)
    calls = tmp_path / "calls"
    env = os.environ | {"PATH": f"{bin_dir}{os.pathsep}{os.environ['PATH']}", "CALLS": str(calls)}
    result = run_capture([find_executable("bash"), str(script), *components], env=env)
    logged = calls.read_text(encoding="utf-8").splitlines() if calls.exists() else []
    return ExitStatus(result.returncode), [OutputLine(line) for line in logged]


@pytest.mark.process(_A_SHELL_RUNS_THE_SCRIPT)
def test_the_script_installs_the_pinned_channel_and_makes_it_the_default(tmp_path: Path) -> None:
    """The channel is installed with each component asked for, then made the default."""
    status, calls = _install(
        tmp_path,
        ToolchainText('[toolchain]\nchannel = "1.2.3"\n'),
        [Component("clippy"), Component("rustfmt")],
    )
    assert status == 0
    assert calls == [
        OutputLine(
            "rustup toolchain install 1.2.3 --profile minimal --no-self-update"
            + " --component clippy --component rustfmt"
        ),
        OutputLine("rustup default 1.2.3"),
        OutputLine("rustc --version"),
        OutputLine("cargo --version"),
    ]


@pytest.mark.process(_A_SHELL_RUNS_THE_SCRIPT)
def test_the_script_refuses_a_toolchain_file_naming_no_channel(tmp_path: Path) -> None:
    """With no channel to read, nothing is installed and the script exits 1."""
    status, calls = _install(tmp_path, ToolchainText('[toolchain]\nprofile = "minimal"\n'), [])
    assert status == 1
    assert calls == []


class _Machine(TypedDict):
    """What each stand-in compiler reports; a None Go is absent from PATH."""

    go: Reported | None
    rust_in: Reported
    rust_out: Reported
    clang: Reported


_PINNED = _Machine(
    go=Reported("1.2.3"),
    rust_in=Reported("4.5.6"),
    rust_out=Reported("4.5.6"),
    clang=Reported("7.8.9"),
)


class _Change(TypedDict, total=False):
    """What a machine reports off the pins."""

    go: Reported | None
    rust_in: Reported
    rust_out: Reported
    clang: Reported


def _off(change: _Change) -> _Machine:
    """Return the pinned machine with ``change`` reported instead."""
    return _Machine(
        go=change["go"] if "go" in change else _PINNED["go"],
        rust_in=change.get("rust_in", _PINNED["rust_in"]),
        rust_out=change.get("rust_out", _PINNED["rust_out"]),
        clang=change.get("clang", _PINNED["clang"]),
    )


# The stand-ins: rustc answers by whether it runs inside the tree.
_STAND_INS = {
    "rustc": '#!/bin/sh\ncase "$(pwd -P)" in "$TREE"*) v=$RUST_IN ;; *) v=$RUST_OUT ;; esac\n'
    + 'echo "rustc $v (0000000 2026-01-01)"\n',
    "clang-23": '#!/bin/sh\necho "Ubuntu clang version $CLANG_HAS (++20260101)"\n',
    "go": '#!/bin/sh\necho "go version go$GO_HAS linux/amd64"\n',
}


def _pin_tree(tree: Path) -> None:
    """Write pins of Go 1.2.3, Rust 4.5.6 and LLVM 7.8.9 into ``tree``."""
    (tree / "cpp" / "toolchain").mkdir(parents=True)
    _ = (tree / ".go-version").write_text("1.2.3\n", encoding="utf-8")
    _ = (tree / "rust-toolchain.toml").write_text(
        '[toolchain]\nchannel = "4.5.6"\n', encoding="utf-8"
    )
    _ = (tree / "cpp" / "toolchain" / "check_upstream.sh").write_text(
        'for entry in "llvm-toolchain-23 7.8.9" "gcc-15 15.2.0"; do\n', encoding="utf-8"
    )


def _check(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    machine: _Machine,
) -> tuple[ExitStatus, list[OutputLine]]:
    """Run the gate against the test's pins on ``machine``; return its exit and its lines."""
    tree = (tmp_path / "tree").resolve()
    _pin_tree(tree)
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    for name, text in _STAND_INS.items():
        if name == "go" and machine["go"] is None:
            continue
        stand_in = bin_dir / name
        _ = stand_in.write_text(text, encoding="utf-8")
        stand_in.chmod(0o755)
    monkeypatch.setenv("PATH", str(bin_dir))
    monkeypatch.setenv("TREE", str(tree))
    monkeypatch.setenv("GO_HAS", machine["go"] or "")
    monkeypatch.setenv("RUST_IN", machine["rust_in"])
    monkeypatch.setenv("RUST_OUT", machine["rust_out"])
    monkeypatch.setenv("CLANG_HAS", machine["clang"])
    monkeypatch.setattr(pins, "REPO_ROOT", tree)
    monkeypatch.setattr(pins, "GO_PIN", tree / ".go-version")
    monkeypatch.setattr(pins, "RUST_PIN", tree / "rust-toolchain.toml")
    monkeypatch.setattr(pins, "CLANG_PIN", tree / "cpp" / "toolchain" / "check_upstream.sh")
    status = pins.main([])
    return status, [OutputLine(line) for line in capsys.readouterr().out.splitlines()]


@pytest.mark.process(_THE_GATE_ASKS_COMPILERS)
def test_a_machine_on_the_pins_passes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Go, and Rust in and out of the tree, on their pins pass, saying so."""
    status, lines = _check(tmp_path, monkeypatch, capsys, _PINNED)
    assert status == 0
    assert lines == [
        OutputLine(
            "check-toolchain-pins: go 1.2.3, and rustc 4.5.6 in the tree and outside it, as pinned"
        )
    ]


@pytest.mark.process(_THE_GATE_ASKS_COMPILERS)
@pytest.mark.parametrize(
    ("machine", "refusal"),
    [
        pytest.param(
            _off({"go": Reported("1.2.4")}),
            OutputLine("check-toolchain-pins: go is 1.2.4, and the tree pins 1.2.3"),
            id="another-go",
        ),
        pytest.param(
            _off({"go": None}),
            OutputLine("check-toolchain-pins: go is missing from PATH, and the tree pins 1.2.3"),
            id="no-go",
        ),
        pytest.param(
            _off({"rust_in": Reported("4.5.7")}),
            OutputLine("check-toolchain-pins: rustc in the tree is 4.5.7, and the tree pins 4.5.6"),
            id="another-rust-in-the-tree",
        ),
        pytest.param(
            _off({"rust_out": Reported("4.4.0")}),
            OutputLine(
                "check-toolchain-pins: rustc outside the tree is 4.4.0, and the tree pins 4.5.6"
            ),
            id="another-rust-outside",
        ),
    ],
)
def test_another_go_or_rust_is_refused_naming_it(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    machine: _Machine,
    refusal: OutputLine,
) -> None:
    """A Go or a Rust off its pin, or no Go, exits 1 naming what was found and the pin."""
    status, lines = _check(tmp_path, monkeypatch, capsys, machine)
    assert status == 1
    assert refusal in lines


@pytest.mark.process(_THE_GATE_ASKS_COMPILERS)
def test_a_clang_of_another_upstream_is_reported_not_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A clang off the recorded upstream is noted, and the gate still passes."""
    status, lines = _check(tmp_path, monkeypatch, capsys, _off({"clang": Reported("7.8.8")}))
    assert status == 0
    assert (
        OutputLine(
            "check-toolchain-pins: note: clang-23 is upstream 7.8.8, and the runners' is 7.8.9;"
            + " reported, not refused"
        )
        in lines
    )


def test_an_unreadable_pin_exits_2(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A .go-version naming no release leaves nothing to compare with."""
    bad = tmp_path / ".go-version"
    _ = bad.write_text("stable\n", encoding="utf-8")
    monkeypatch.setattr(pins, "GO_PIN", bad)
    assert pins.main([]) == 2
    assert "names no Go release" in capsys.readouterr().out


def test_the_tree_s_pins_name_releases() -> None:
    """The pins are releases, and the toolchain file spells its channel as the script reads it."""
    assert pins.go_pin()
    assert pins.clang_pin()
    text = pins.RUST_PIN.read_text(encoding="utf-8")
    read = re.findall(r'^channel = "(.*)"$', text, re.MULTILINE)
    assert read == [pins.rust_pin()]


def test_the_release_image_verifies_with_the_pinned_go_and_rust() -> None:
    """The image's verify stages build the Go and Rust consumers on the pinned releases."""
    image = (_REPO / "Dockerfile.runtime").read_text(encoding="utf-8")
    assert re.findall(r"^FROM golang:([0-9.]+)-", image, re.MULTILINE) == [pins.go_pin()]
    assert re.findall(r"^FROM rust:([0-9.]+)-", image, re.MULTILINE) == [pins.rust_pin()]


def test_a_change_to_a_pin_measures_the_benchmark() -> None:
    """A change moving a compiler or its install runs the benchmark, whose counts record it."""
    for path in (
        ".go-version",
        "rust-toolchain.toml",
        "tools/install_rust_toolchain.sh",
        "cpp/toolchain/",
    ):
        assert path in BENCHMARK_GLOBAL_PATHS, path


def test_every_sweep_runs_the_gate(tmp_path: Path) -> None:
    """The sweep registers the gate on every run, from the tree's root."""
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    (step,) = (step for step in runner.registered_steps if step.name == "check-toolchain-pins")
    assert (step.cmd, step.cwd) == (
        [runner.python, "-m", "tools.check_toolchain_pins"],
        runner.repo_root,
    )
