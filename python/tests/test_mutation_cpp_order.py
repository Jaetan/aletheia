# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ lane pins the test order it sweeps under.

Catch2 shuffles its cases by default under a seed that changes every run, and
mull runs the test binary once per mutant, so an unpinned lane reads a
different kill-route census every sweep: two pinned sweeps of one tree agreed
on every mutant, where two shuffled ones read the fault route at 98 and 99
against the pinned 93. A fault ends the process, so the order decides which
test reports before the run stops. The recorded census is therefore taken
under a stated order, which is what makes it a measurement rather than one
sample of a shuffle.

A run also ends at its first failing assertion, which moves no route: the
census reads any failing assertion as the test's kill, whatever ended the
process after it, which ``test_a_run_is_read_by_what_ended_it`` holds, and a
run with none goes through the whole suite either way.

Under that order, the tests whose cost is the input's are the binary's tail
(``tools/mutation_cpp_order.py``): the lane lists the binary before its runner
starts and refuses one with a ``[costly]`` test ahead of an untagged one, or
with none at all.  The listing arms run on planted listings, and the one that
reaches the lane's sweep stops it at the listing.
"""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType

import pytest

from tools import mutation_cpp, mutation_cpp_order
from tools.mutation_cpp import (
    CPP_BUILD_JOBS_CAP,
    CPP_MUTANT_CAP_MS,
    cpp_build_command,
    cpp_lane_command,
    cpp_sweep_environment,
    run_cpp,
)
from tools.mutation_cpp_legs import CPP_STAGE_ENV, CppLeg
from tools.mutation_cpp_order import (
    CaseName,
    CatchTag,
    ListedCase,
    ListedTest,
    Listing,
    listed_tests,
    misplaced_costly_tests,
    order_refusal,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from tools.mutation_cpp import LegPaths, SweepEnvironment

# The path of a tool a leg runs, cmake or the runner, and what a build printed.
ToolPath = NewType("ToolPath", str)
BuildLog = NewType("BuildLog", str)


def _command(*, dry_run: bool = False) -> list[str]:
    """Build one leg's argv, a dry run's where asked, the paths being the only thing it reads."""
    leg = CppLeg(1)
    return cpp_lane_command(
        "mull-runner-23", Path("cpp") / leg.directory, Path("artifacts"), leg, dry_run=dry_run
    )


def test_the_lane_hands_the_binary_a_pinned_order() -> None:
    """The binary's argv, behind the separator, opens with the declaration order."""
    argv = _command()
    separator = argv.index("--")
    assert argv[separator + 1 : separator + 3] == ["--order", "decl"]


def test_a_run_ends_at_its_first_failing_assertion() -> None:
    """The binary is told to stop at the first failure rather than run the rest of the suite."""
    argv = _command()
    assert "--abort" in argv[argv.index("--") + 1 :]


def test_every_runner_option_stays_ahead_of_the_separator() -> None:
    """Mull parses what precedes the separator; only Catch2 reads what follows."""
    argv = _command()
    separator = argv.index("--")
    assert all(arg.startswith("--") for arg in argv[2:separator])
    assert "--order" not in argv[:separator]
    assert "--abort" not in argv[:separator]


def test_a_dry_run_is_the_lane_s_argv_with_the_runner_told_to_run_no_mutant() -> None:
    """The one runner option a dry run adds sits ahead of the separator; nothing else moves."""
    dry = _command(dry_run=True)
    assert "--dry-run" not in _command()
    assert dry.index("--dry-run") < dry.index("--")
    dry.remove("--dry-run")
    assert dry == _command()


def test_the_cap_per_mutant_is_the_runner_s_minimum_timeout() -> None:
    """The knob that raises Mull's ten-times-the-baseline, ahead of the separator.

    The cap on the unmutated runs is the configuration's, which every
    invocation inherits, so the command line carries no ``--timeout``.
    """
    argv = _command()
    assert f"--minimum-timeout={CPP_MUTANT_CAP_MS}" in argv[: argv.index("--")]
    assert not any(arg.startswith("--timeout") for arg in argv)


def test_the_mutation_build_compiles_several_units_at_once(tmp_path: Path) -> None:
    """The build carries a parallel count, bounded so the plugin compiles fit in memory."""
    argv = cpp_build_command("cmake", tmp_path)
    assert argv[:5] == ["cmake", "--build", str(tmp_path), "--target", "unit_tests"]
    assert argv[5] == "--parallel"
    assert 1 <= int(argv[6]) <= CPP_BUILD_JOBS_CAP


def test_the_mutation_build_counts_the_cpus_it_was_given(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Under the cap, a build given three CPUs of the machine's 24 runs three compiles."""
    monkeypatch.setattr(os, "cpu_count", lambda: 24)
    monkeypatch.setattr(os, "process_cpu_count", lambda: 3)
    assert cpp_build_command("cmake", tmp_path)[5:7] == ["--parallel", "3"]


def _case(name: CaseName, *tags: CatchTag) -> ListedCase:
    """One test as the JSON listing spells it."""
    return ListedCase(name=name, tags=list(tags))


def _listing(*cases: ListedCase) -> Listing:
    """Spell the listing a Catch2 binary prints under the JSON reporter, the cases in this order."""
    return Listing(json.dumps({"version": 2, "listings": {"tests": list(cases)}}))


# Two untagged tests, then the one tagged costly: the shape the rule wants.
_COSTLY_LAST = _listing(
    _case(CaseName("a"), CatchTag("json")),
    _case(CaseName("b")),
    _case(CaseName("c"), CatchTag("input_bounds"), CatchTag("costly")),
)


def test_a_listing_is_read_in_the_order_the_binary_runs() -> None:
    """Every case comes back with its name and tags, in the listing's order."""
    tests = listed_tests(_COSTLY_LAST)
    assert isinstance(tests, list)
    assert tests == [
        ListedTest(CaseName("a"), (CatchTag("json"),)),
        ListedTest(CaseName("b"), ()),
        ListedTest(CaseName("c"), (CatchTag("input_bounds"), CatchTag("costly"))),
    ]
    assert [test.costly for test in tests] == [False, False, True]


@pytest.mark.parametrize(
    "text",
    [
        Listing(""),
        Listing("not json"),
        Listing('{"listings": {}}'),
        Listing("[]"),
    ],
)
def test_text_that_is_no_listing_is_said(text: Listing) -> None:
    """A binary that printed anything but a listing is refused for what it printed instead."""
    assert listed_tests(text) == "order: the test binary printed no listing of its tests"


def test_a_listing_naming_no_test_is_said() -> None:
    """An empty listing is a binary with no test, which is not a binary to sweep."""
    assert listed_tests(_listing()) == "order: the test binary's listing names no test"


def test_every_costly_test_after_every_other_passes() -> None:
    """The rule holds when the tagged tests are the listing's tail."""
    tests = listed_tests(_COSTLY_LAST)
    assert isinstance(tests, list)
    assert misplaced_costly_tests(tests) is None


def test_a_costly_test_ahead_of_an_untagged_one_is_refused() -> None:
    """The refusal names the first tagged test and the first untagged one after it."""
    tests = listed_tests(
        _listing(
            _case(CaseName("a"), CatchTag("costly")),
            _case(CaseName("b"), CatchTag("costly")),
            _case(CaseName("c")),
            _case(CaseName("d"), CatchTag("costly")),
            _case(CaseName("e")),
        )
    )
    assert isinstance(tests, list)
    assert misplaced_costly_tests(tests) == (
        "order: 2 test(s) without [costly] run after 'a', the first with it: 'c'"
    )


def test_a_binary_with_no_costly_test_is_refused() -> None:
    """A tag dropped from every test would pass in silence, so none at all is a refusal."""
    tests = listed_tests(_listing(_case(CaseName("a")), _case(CaseName("b"), CatchTag("json"))))
    assert isinstance(tests, list)
    assert misplaced_costly_tests(tests) == "order: no test carries [costly], so none runs last"


class _Listed(NamedTuple):
    """What the lane handed the binary when it listed it: argv, directory and environment."""

    argv: list[ToolPath]
    cwd: Path | None
    variables: list[Prose]


def test_the_binary_is_listed_in_declaration_order_as_json(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The lane lists the binary as it runs it, in the leg's directory and environment."""
    seen: list[_Listed] = []

    def listing(
        cmd: list[ToolPath], *, cwd: Path | None = None, env: dict[Prose, Prose] | None = None
    ) -> subprocess.CompletedProcess[Listing]:
        variables = sorted(Prose(f"{name}={value}") for name, value in (env or {}).items())
        seen.append(_Listed(cmd, cwd, variables))
        return subprocess.CompletedProcess(cmd, 0, _COSTLY_LAST, Listing(""))

    monkeypatch.setattr(mutation_cpp_order, "run_capture", listing)
    environment = cpp_sweep_environment(CppLeg(), tmp_path)
    assert order_refusal(tmp_path / "unit_tests", cwd=tmp_path, environment=environment) is None
    assert seen == [
        _Listed(
            [
                ToolPath(str(tmp_path / "unit_tests")),
                ToolPath("--list-tests"),
                ToolPath("--order"),
                ToolPath("decl"),
                ToolPath("--reporter"),
                ToolPath("json"),
            ],
            tmp_path,
            sorted(Prose(f"{name}={value}") for name, value in environment.variables().items()),
        )
    ]


def _config_beside(_leg: CppLeg, build_dir: Path) -> Path:
    """Stand in for ``leg_config`` with a path beside the tree, written by nobody."""
    return build_dir / "mull.yml"


def test_the_lane_lists_the_binary_before_its_runner_starts(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A leg whose binary breaks the rule ends at the listing, and its runner never runs."""
    steps: list[Prose] = []
    leg = CppLeg(2)

    def built(_cmake: ToolPath, paths: LegPaths) -> BuildLog:
        steps.append(Prose(f"build {paths.build_dir.name}"))
        return BuildLog("=== built ===\n")

    def refused(binary: Path, *, cwd: Path, environment: SweepEnvironment) -> Prose:
        steps.append(Prose(f"list {binary.name} in {cwd.name} under {environment.locale}"))
        return Prose("order: no test carries [costly], so none runs last")

    def runner(_mull: ToolPath, _paths: LegPaths, _leg: CppLeg) -> BuildLog:
        steps.append(Prose("run"))
        return BuildLog("")

    monkeypatch.setattr(mutation_cpp, "check_cpp_tools", lambda: ("cmake", "mull-runner-23"))
    monkeypatch.setattr(mutation_cpp, "build_cpp_mutation_tree", built)
    monkeypatch.setattr(mutation_cpp, "order_refusal", refused)
    monkeypatch.setattr(mutation_cpp, "_run_cpp_lane", runner)
    monkeypatch.setattr(mutation_cpp, "leg_config", _config_beside)
    monkeypatch.setenv(CPP_STAGE_ENV, str(leg.slice_no))
    report = run_cpp(tmp_path)
    assert report.error == "the cpp-2 leg: order: no test carries [costly], so none runs last"
    assert report.raw_log.endswith(
        "=== built ===\norder: no test carries [costly], so none runs last\n"
    )
    assert steps == [
        Prose(f"build {leg.directory}"),
        Prose("list unit_tests in cpp under C.UTF-8"),
    ]
