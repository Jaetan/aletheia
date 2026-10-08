# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A dry run of a C++ leg runs the lane's own runner, in the lane's directory and environment.

What a dry run reports is the surface a sweep of the leg would cover, so it is
worth reading only while it runs the runner exactly as the lane does, with the
one option that runs no mutant.  The repository is faked under a scratch root,
and a runner standing in for Mull records where and how it was started.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

from tools import mutation_cpp, mutation_cpp_config, mutation_cpp_dry_run
from tools.mutation_cpp import CPP_LEG_REPORT_SUFFIXES
from tools.mutation_cpp_legs import CPP_SLICE_ENV, CPP_STAGE_ENV, CppLeg, CppTree

# A configuration with a mutator every tree keeps and one the address tree
# drops, so that tree is configured apart.
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


@pytest.fixture(name="root")
def _root(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Fake the repository under a scratch root, each tree configured as the lane configures it."""
    root = tmp_path / "repo"
    (root / "cpp").mkdir(parents=True)
    for module in (mutation_cpp, mutation_cpp_config):
        monkeypatch.setattr(module, "REPO_ROOT", root)
    _ = (root / "cpp" / "mull.yml").write_text(_MULL_CONFIG, encoding="utf-8")
    for tree in CppTree:
        leg = CppLeg(tree)
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


def _assert_ran_as_the_lane(root: Path, base: Path, leg: CppLeg, build_dir: Path) -> None:
    """Check the stand-in runner ran in the lane's directory and environment for ``leg``."""
    assert Path(base.with_suffix(".cwd").read_text(encoding="utf-8")) == root / "cpp"
    text = base.with_suffix(".env").read_text(encoding="utf-8")
    recorded = dict(item.split("=", 1) for item in text.split("\0"))
    assert recorded == mutation_cpp.cpp_sweep_environment(leg, build_dir).variables()


def test_a_tree_s_binary_is_the_lane_s_test_target(root: Path) -> None:
    """The binary a whole tree's runner runs is the lane's test target in that tree."""
    for tree in CppTree:
        binary = mutation_cpp_dry_run.tree_binary(tree)
        assert binary == root / "cpp" / tree.directory / "unit_tests"


def test_a_dry_run_of_a_slice_runs_the_lane_s_command_for_it(
    root: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The slice's own tree, configuration and report name, and the runner told to run no mutant."""
    runner = _write_runner(root.parent / "runner")
    monkeypatch.setattr(mutation_cpp_dry_run, "MULL_RUNNER", str(runner))
    leg = CppLeg(CppTree.PLAIN, 2)
    build_dir = mutation_cpp_dry_run.leg_build_dir(leg)
    assert build_dir == root / "cpp" / f"{CppTree.PLAIN.directory}-2"
    report_dir = root.parent / "reports"
    report_dir.mkdir()
    report = mutation_cpp_dry_run.dry_run_report(leg, report_dir)
    assert report == report_dir / f"{leg.report_name}.json"
    base = report_dir / leg.report_name
    _assert_ran_as_the_lane(root, base, leg, build_dir)
    argv = base.with_suffix(".argv").read_text(encoding="utf-8").split("\0")
    assert argv == mutation_cpp.cpp_lane_command(
        str(runner), build_dir, report_dir, leg, dry_run=True
    )


def test_a_dry_run_that_wrote_no_report_says_so(
    root: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A runner that ran and left no Elements report is reported, not read."""
    monkeypatch.setattr(mutation_cpp_dry_run, "MULL_RUNNER", "true")
    leg = CppLeg(CppTree.LEAK)
    assert mutation_cpp_dry_run.dry_run_report(leg, root.parent) == (
        f"the dry run of the {leg} leg wrote no {leg.report_name}.json"
    )


def _argv_beside_its_reports(argv_file: Path) -> list[Path]:
    """Read a recorded argv less where its reports went and the option that runs no mutant."""
    argv = argv_file.read_text(encoding="utf-8").split("\0")
    return [Path(arg) for arg in argv if arg != "--dry-run" and not arg.startswith("--report-dir=")]


def test_the_lane_and_a_dry_run_run_the_runner_alike(
    root: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The CI lane's runner and a dry run's start in one directory, under one environment and argv.

    The lane is run for one leg as a CI job runs it, its tools stood in for on
    the search path, a cmake that builds nothing among them, so the runner it
    starts is the one under test; only where each writes its reports, and the
    dry run's option, differ.
    """
    tools = root.parent / "bin"
    tools.mkdir()
    runner = _write_runner(tools / "mull-runner-23")
    for stand_in in (tools / "cmake", tools / "clang++-23"):
        _ = stand_in.write_text("#!/bin/sh\n", encoding="utf-8")
        stand_in.chmod(0o755)
    home = root.parent / "home"
    plugin = home / ".local" / "bin" / "mull-ir-frontend-23"
    plugin.parent.mkdir(parents=True)
    _ = plugin.write_text("plugin", encoding="utf-8")
    monkeypatch.setenv("HOME", str(home))
    monkeypatch.setenv("PATH", f"{tools}{os.pathsep}{os.environ['PATH']}")
    monkeypatch.setenv(CPP_STAGE_ENV, CppTree.LEAK.value)
    monkeypatch.delenv(CPP_SLICE_ENV, raising=False)
    monkeypatch.setattr(mutation_cpp, "reap_dead_scratch_dirs", lambda: 0)
    leg = CppLeg(CppTree.LEAK)
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
