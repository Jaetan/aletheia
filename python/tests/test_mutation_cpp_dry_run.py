# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A dry run of a C++ leg runs the lane's own runner, in the lane's directory and environment.

What a dry run reports is the surface a sweep of the leg would cover, so it is
worth reading only while it runs the runner exactly as the lane does, with the
one option that runs no mutant.  The repository is faked under a scratch root.
A dry run alone is read from what it hands ``subprocess.run``; set beside the
lane, a runner standing in for Mull records where and how each started it.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace
from typing import TYPE_CHECKING, NewType

import pytest

from tools import mutation_cpp, mutation_cpp_config, mutation_cpp_dry_run, mutation_cpp_order
from tools.mutation_cpp import CPP_LEG_REPORT_SUFFIXES
from tools.mutation_cpp_legs import CPP_STAGE_ENV, CppLeg
from tools.mutation_cpp_order import Listing

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from _processes import CommandWord

    from tools.mutation_cpp import LegPaths

# A variable's name and its value in the environment a program is started under.
EnvName = NewType("EnvName", str)
EnvValue = NewType("EnvValue", str)

# What a started program printed on one of its streams.
RunnerOutput = NewType("RunnerOutput", bytes)

# The tree's configuration: two mutators and no hold-out.
_MULL_CONFIG = "mutators:\n  - cxx_add_to_sub\n  - cxx_remove_void_call\nexcludePaths: []\n"

# A runner standing in for Mull: it writes every report a leg writes, and
# records the directory it ran in, its argv and its environment beside them.
_RUNNER = """#!{python}
import os
import sys

options = dict(arg.split("=", 1) for arg in sys.argv[1:] if arg.startswith("--report-"))
base = os.path.join(options["--report-dir"], options["--report-name"])
for suffix in {suffixes!r}:
    open(base + suffix, "w").close()
with open(base + ".cwd", "w") as out:
    out.write(os.getcwd())
with open(base + ".argv", "w") as out:
    out.write("\\0".join(sys.argv))
with open(base + ".env", "w") as out:
    out.write("\\0".join(name + "=" + value for name, value in sorted(os.environ.items())))
"""

# The tree's binary asked for its tests: one untagged test and then the costly
# one, the tail the lane holds a binary to.
_LISTING = json.dumps(
    {"listings": {"tests": [{"name": "a", "tags": []}, {"name": "z", "tags": ["costly"]}]}}
)


@pytest.fixture(name="root")
def _root(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Fake the repository under a scratch root, the tree configured as the lane configures it."""
    root = tmp_path / "repo"
    (root / "cpp").mkdir(parents=True)
    for module in (mutation_cpp, mutation_cpp_config):
        monkeypatch.setattr(module, "REPO_ROOT", root)
    _ = (root / "cpp" / "mull.yml").write_text(_MULL_CONFIG, encoding="utf-8")
    leg = CppLeg()
    _ = mutation_cpp_config.leg_config(leg, mutation_cpp_dry_run.leg_build_dir(leg))
    return root


def _write_runner(path: Path) -> Path:
    """Write the runner standing in for Mull at ``path``, ready to run."""
    _ = path.write_text(
        _RUNNER.format(python=sys.executable, suffixes=tuple(CPP_LEG_REPORT_SUFFIXES)),
        encoding="utf-8",
    )
    path.chmod(0o755)
    return path


@dataclass(frozen=True)
class _Call:
    """One start of a program, as the code under test hands it to what would start it."""

    argv: list[CommandWord]
    cwd: Path
    env: dict[EnvName, EnvValue]


@dataclass(frozen=True)
class _DryRunner:
    """Stand in for ``subprocess.run`` in a dry run, recording each start of the runner.

    Told to, it writes every report a leg writes, where the argv says, as the
    runner does.
    """

    writes_reports: bool
    calls: list[_Call] = field(default_factory=list)

    def run(
        self,
        argv: list[CommandWord],
        *,
        cwd: Path,
        env: dict[EnvName, EnvValue],
        check: bool,
        capture_output: bool,
    ) -> subprocess.CompletedProcess[RunnerOutput]:
        """Record the start; the dry run reads its reports, not the exit status it is handed."""
        assert not check
        assert capture_output
        self.calls.append(_Call(argv, cwd, env))
        if self.writes_reports:
            options = {
                name: value
                for name, _, value in (arg.partition("=") for arg in argv)
                if name.startswith("--report-")
            }
            base = Path(options["--report-dir"]) / options["--report-name"]
            for suffix in CPP_LEG_REPORT_SUFFIXES:
                Path(f"{base}{suffix}").touch()
        return subprocess.CompletedProcess(argv, 0, RunnerOutput(b""), RunnerOutput(b""))


def _built_without_cmake(_cmake: CommandWord, _paths: LegPaths) -> Prose:
    """Take the leg's tree as built, with nothing in its build log."""
    return Prose("")


def test_the_tree_s_binary_is_the_lane_s_test_target(root: Path) -> None:
    """The binary the whole tree's runner runs is the lane's test target in that tree."""
    assert mutation_cpp_dry_run.lane_binary() == root / "cpp" / "build-mutation" / "unit_tests"


def test_a_dry_run_of_a_slice_runs_the_lane_s_command_for_it(
    root: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The slice's own tree, configuration and report name, and the runner told to run no mutant."""
    runner = _DryRunner(writes_reports=True)
    monkeypatch.setattr(mutation_cpp_dry_run, "subprocess", SimpleNamespace(run=runner.run))
    leg = CppLeg(2)
    build_dir = mutation_cpp_dry_run.leg_build_dir(leg)
    assert build_dir == root / "cpp" / "build-mutation-2"
    report_dir = root.parent / "reports"
    report_dir.mkdir()
    report = mutation_cpp_dry_run.dry_run_report(leg, report_dir)
    assert report == report_dir / f"{leg.report_name}.json"
    assert len(runner.calls) == 1
    call = runner.calls[0]
    assert call.cwd == root / "cpp"
    assert call.env == mutation_cpp.cpp_sweep_environment(leg, build_dir).variables()
    assert call.argv == mutation_cpp.cpp_lane_command(
        mutation_cpp_dry_run.MULL_RUNNER, build_dir, report_dir, leg, dry_run=True
    )


def test_a_dry_run_that_wrote_no_report_says_so(
    root: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A runner that ran and left no Elements report is reported, not read."""
    runner = _DryRunner(writes_reports=False)
    monkeypatch.setattr(mutation_cpp_dry_run, "subprocess", SimpleNamespace(run=runner.run))
    leg = CppLeg()
    assert mutation_cpp_dry_run.dry_run_report(leg, root.parent) == (
        f"the dry run of the {leg} leg wrote no {leg.report_name}.json"
    )
    assert len(runner.calls) == 1
    assert "--dry-run" in runner.calls[0].argv


def _argv_beside_its_reports(argv_file: Path) -> list[Path]:
    """Read a recorded argv less where its reports went and the option that runs no mutant."""
    argv = argv_file.read_text(encoding="utf-8").split("\0")
    return [Path(arg) for arg in argv if arg != "--dry-run" and not arg.startswith("--report-dir=")]


@pytest.mark.process(
    "which program the runner's bare name starts, and the environment it receives once"
    + " the lane's launcher has added to it, show only in the started runner's own record"
)
def test_the_lane_and_a_dry_run_run_the_runner_alike(
    root: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The CI lane's runner and a dry run's start in one directory, under one environment and argv.

    The lane is run for one leg as a CI job runs it, its tools stood in for on
    the search path, its tree taken as built and its binary's listing of its
    tests answered in-process, so the runner it starts is the one under test;
    only where each writes its reports, and the dry run's option, differ.
    """
    tools = root.parent / "bin"
    tools.mkdir()
    runner = _write_runner(tools / "mull-runner-23")
    # The lane looks cmake and clang++-23 up on the search path; neither runs.
    for stand_in in (tools / "cmake", tools / "clang++-23"):
        _ = stand_in.write_text("#!/bin/sh\n", encoding="utf-8")
        stand_in.chmod(0o755)
    home = root.parent / "home"
    plugin = home / ".local" / "bin" / "mull-ir-frontend-23"
    plugin.parent.mkdir(parents=True)
    _ = plugin.write_text("plugin", encoding="utf-8")
    monkeypatch.setenv("HOME", str(home))
    monkeypatch.setenv("PATH", f"{tools}{os.pathsep}{os.environ['PATH']}")
    monkeypatch.delenv(CPP_STAGE_ENV, raising=False)
    monkeypatch.setattr(mutation_cpp, "reap_dead_scratch_dirs", lambda: 0)
    monkeypatch.setattr(mutation_cpp, "build_cpp_mutation_tree", _built_without_cmake)
    listed: list[_Call] = []

    def list_tests(
        cmd: list[CommandWord], *, cwd: Path, env: dict[EnvName, EnvValue]
    ) -> subprocess.CompletedProcess[Listing]:
        listed.append(_Call(cmd, cwd, env))
        return subprocess.CompletedProcess(cmd, 0, Listing(_LISTING + "\n"), Listing(""))

    monkeypatch.setattr(mutation_cpp_order, "run_capture", list_tests)
    leg = CppLeg()
    lane, dry = root.parent / "lane", root.parent / "dry"
    lane.mkdir()
    dry.mkdir()
    _ = mutation_cpp.run_cpp(lane)
    _ = mutation_cpp_dry_run.dry_run_report(leg, dry)
    lane_base, dry_base = lane / leg.report_name, dry / leg.report_name
    assert lane_base.with_suffix(".cwd").read_text(encoding="utf-8") == (
        dry_base.with_suffix(".cwd").read_text(encoding="utf-8")
    )
    assert lane_base.with_suffix(".env").read_text(encoding="utf-8") == (
        dry_base.with_suffix(".env").read_text(encoding="utf-8")
    )
    lane_argv = _argv_beside_its_reports(lane_base.with_suffix(".argv"))
    assert lane_argv == _argv_beside_its_reports(dry_base.with_suffix(".argv"))
    assert lane_argv[0] == runner
    assert [(call.argv[0], call.cwd) for call in listed] == [
        (str(mutation_cpp_dry_run.lane_binary()), root / "cpp")
    ]
