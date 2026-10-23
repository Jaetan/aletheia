# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the Go and Rust lanes' checks of ``tools.check_mutation_setup_lanes``.

Each lane skips its doc-example harness by name, the Rust lane the benchmark
program's tests with it, and the check holds the skip to those and nothing
else.  The tests are planted and the module's paths monkeypatched to them,
the diagnostics compared whole; an input a check cannot read stops the gate
with exit 2, named on stderr.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, Literal, NewType

import pytest
from _gate_exit import stderr_of_exit_2
from _planted_tree import plant

from tools import check_mutation_setup_lanes
from tools._common import RelPath
from tools.check_mutation_setup_lanes import RUST_DOC_HARNESS, TestName
from tools.mutation_run import GO_DOC_HARNESS, GoFlags

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

# One argument of the test command cargo-mutants runs, as mutants.toml lists them.
CargoTestArg = NewType("CargoTestArg", str)


# The Go lane skips its doc-example harness alone.

_GO_HARNESS: Final = TestName(GO_DOC_HARNESS)
_GO_FIXTURE: Final = TestName(f"{GO_DOC_HARNESS}Fixture_ChecksYAMLLoads")
_GO_BESIDE: Final = TestName("TestOpen")
_NOTHING_BESIDE: Final = Prose("")


def _plant_go_tests(
    root: Path,
    monkeypatch: pytest.MonkeyPatch,
    harness: TestName = _GO_HARNESS,
    beside: Prose = _NOTHING_BESIDE,
) -> None:
    """Plant the Go package's tests, the harness named ``harness``, ``beside`` appended to one."""
    _ = plant(
        root,
        {
            RelPath("go/aletheia/doc_examples_test.go"): Prose(
                f"func {harness}(t *testing.T) {{}}\nfunc {_GO_FIXTURE}(t *testing.T) {{}}\n"
            ),
            RelPath("go/aletheia/client_test.go"): Prose(
                f"func TestMain(m *testing.M) {{}}\nfunc {_GO_BESIDE}(t *testing.T) {{}}\n{beside}"
            ),
        },
    )
    monkeypatch.setattr(check_mutation_setup_lanes, "REPO_ROOT", root)


def _runner_flags(monkeypatch: pytest.MonkeyPatch, flags: GoFlags) -> None:
    """Stand the runner's GOFLAGS in for the caller's followed by ``flags``."""

    def sweep_goflags(caller: GoFlags) -> GoFlags:
        return GoFlags(f"{caller} {flags}".strip())

    monkeypatch.setattr(check_mutation_setup_lanes, "go_sweep_goflags", sweep_goflags)


# A lane that skips its doc-example harness by name.
SkippingLane = Literal["go", "rust"]


def _reaches(lane: SkippingLane, name: TestName) -> Prose:
    """Return the diagnostic for a ``lane`` whose skip misses the harness ``name``."""
    return Prose(
        f"[{lane}/doc-harness] every mutant's run reaches {name}: the lane's skip does not "
        + "match it"
    )


def _drops(lane: SkippingLane, name: TestName) -> Prose:
    """Return the diagnostic for a ``lane`` whose skip also drops ``name``."""
    return Prose(
        f"[{lane}/doc-harness] the lane's skip also drops {name}, which is not the "
        + "doc-example harness, so no mutant is tested against it"
    )


def test_the_runners_own_goflags_skip_the_harness_alone(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The GOFLAGS the runner gives gremlins skip the harness and nothing else."""
    _plant_go_tests(tmp_path, monkeypatch)
    assert not check_mutation_setup_lanes.go_lane_runs_no_doc_harness()


@pytest.mark.parametrize(
    ("flags", "diagnostics"),
    [
        pytest.param(
            GoFlags("-count=1"),
            [
                Prose(
                    "[go/doc-harness] the GOFLAGS the runner gives gremlins carry no -skip, so "
                    + f"every mutant's run reaches {GO_DOC_HARNESS}"
                )
            ],
            id="no skip",
        ),
        pytest.param(
            GoFlags("-count=1 -skip=^TestDocFences$"),
            [_reaches("go", _GO_HARNESS)],
            id="a skip matching no test",
        ),
        pytest.param(
            GoFlags(f"-count=1 -skip=^{GO_DOC_HARNESS}"),
            [_drops("go", _GO_FIXTURE)],
            id="a skip matching the fixture test too",
        ),
        pytest.param(
            GoFlags(f"-skip=^{GO_DOC_HARNESS}$ -skip=^{_GO_BESIDE}$"),
            [_reaches("go", _GO_HARNESS), _drops("go", _GO_BESIDE)],
            id="the last skip is the one go keeps",
        ),
    ],
)
def test_a_go_skip_that_does_not_drop_the_harness_alone_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, flags: GoFlags, diagnostics: list[Prose]
) -> None:
    """A ``-skip`` absent, missing the harness or reaching past it is named, the last one read."""
    _plant_go_tests(tmp_path, monkeypatch)
    _runner_flags(monkeypatch, flags)
    assert check_mutation_setup_lanes.go_lane_runs_no_doc_harness() == diagnostics


@pytest.mark.parametrize(
    ("beside", "flags", "diagnostics"),
    [
        pytest.param(
            Prose("func TestUnnamed(*testing.T) {}\n"),
            GoFlags(f"-skip=^({GO_DOC_HARNESS}|TestUnnamed)$"),
            [_drops("go", TestName("TestUnnamed"))],
            id="a test taking an unnamed parameter is a test",
        ),
        pytest.param(
            Prose("func Testify(t *testing.T) {}\n"),
            GoFlags(f"-skip=^({GO_DOC_HARNESS}|Testify)$"),
            [],
            id="Test followed by a lowercase letter is no test",
        ),
        pytest.param(
            _NOTHING_BESIDE,
            GoFlags(f"-skip=^(TestMain|{GO_DOC_HARNESS})$"),
            [],
            id="TestMain is no test",
        ),
        pytest.param(
            Prose("func TestBroken(\n\tt *testing.T,\n) {}\n"),
            GoFlags(f"-skip=^({GO_DOC_HARNESS}|TestBroken)$"),
            [_drops("go", TestName("TestBroken"))],
            id="a parameter list gofmt broke across lines is a test",
        ),
        pytest.param(
            Prose("func TestÉcrire(t *testing.T) {}\n"),
            GoFlags(rf"-skip=^({GO_DOC_HARNESS}|Test\wcrire)$"),
            [],
            id="a word character is an ASCII one",
        ),
    ],
)
def test_the_go_tests_are_found_and_matched_as_go_does(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    beside: Prose,
    flags: GoFlags,
    diagnostics: list[Prose],
) -> None:
    """A test is what the go command runs, and a skip matches it as RE2 does."""
    _plant_go_tests(tmp_path, monkeypatch, beside=beside)
    _runner_flags(monkeypatch, flags)
    assert check_mutation_setup_lanes.go_lane_runs_no_doc_harness() == diagnostics


def test_a_go_package_that_cannot_be_listed_exits_2(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without the Go package's directory the check stops the gate rather than finding no test."""
    monkeypatch.setattr(check_mutation_setup_lanes, "REPO_ROOT", tmp_path)
    assert stderr_of_exit_2(capsys, check_mutation_setup_lanes.go_lane_runs_no_doc_harness) == (
        f"ERROR: cannot read {tmp_path / 'go' / 'aletheia'}: No such file or directory\n"
    )


def test_a_go_harness_renamed_is_named(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A harness renamed out from under the skip is named rather than checked against nothing."""
    _plant_go_tests(tmp_path, monkeypatch, TestName("TestDocFences"))
    assert check_mutation_setup_lanes.go_lane_runs_no_doc_harness() == [
        f"[go/doc-harness] {GO_DOC_HARNESS} is defined 0 times among the binding's tests "
        + "rather than once: the harness was renamed or duplicated, and the lane's skip is "
        + "checked against a name the tree does not settle"
    ]


def test_a_go_test_file_that_is_no_text_exits_2(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A test file the gate cannot read stops it rather than leaving its tests unread."""
    _plant_go_tests(tmp_path, monkeypatch)
    path = tmp_path / "go" / "aletheia" / "other_test.go"
    _ = path.write_bytes(b"\xff")
    assert stderr_of_exit_2(capsys, check_mutation_setup_lanes.go_lane_runs_no_doc_harness) == (
        f"ERROR: cannot read {path}: 'utf-8' codec can't decode byte 0xff in position 0: "
        + "invalid start byte\n"
    )


# The Rust lane skips its doc-example harness and the benchmark program's tests alone.

_RUST_BESIDE: Final = TestName("every_listed_document_is_tracked")
_RUST_PROGRAM: Final = (TestName("a_refusal_exits_1"), TestName("a_report_is_written"))
_MUTANTS_TOML: Final = RelPath("rust/.cargo/mutants.toml")
_PROGRAM_TESTS: Final = RelPath("rust/tests/benchmark_program.rs")
_RUST_HARNESS_RUN: Final = _reaches("rust", RUST_DOC_HARNESS)


def _skipping(*names: TestName) -> list[CargoTestArg]:
    """Return the lane's test arguments: ``--`` and a ``--skip`` for each of ``names``."""
    return [
        CargoTestArg("--"),
        *(arg for name in names for arg in (CargoTestArg("--skip"), CargoTestArg(name))),
    ]


def _plant_rust_tests(
    root: Path,
    monkeypatch: pytest.MonkeyPatch,
    args: list[CargoTestArg],
    harness: TestName = RUST_DOC_HARNESS,
    beside: Prose = _NOTHING_BESIDE,
) -> None:
    """Plant the Rust tests, named ``harness`` with ``beside`` appended, and a run with ``args``."""
    listed = ", ".join(f'"{arg}"' for arg in args)
    _ = plant(
        root,
        {
            RelPath("rust/tests/doc_examples.rs"): Prose(
                f"#[test]\nfn {harness}() {{}}\n#[test]\nfn {_RUST_BESIDE}() {{}}\n{beside}"
            ),
            _PROGRAM_TESTS: Prose(
                "".join(f"#[test]\nfn {name}() {{}}\n" for name in _RUST_PROGRAM)
            ),
            # The lane's other two source directories, read whole, each holding one file.
            RelPath("rust/src/lib.rs"): Prose(""),
            RelPath("rust/examples/benchmark.rs"): Prose(""),
            _MUTANTS_TOML: Prose(f"additional_cargo_test_args = [{listed}]\n"),
        },
    )
    monkeypatch.setattr(check_mutation_setup_lanes, "REPO_ROOT", root)
    monkeypatch.setattr(check_mutation_setup_lanes, "MUTANTS_TOML_PATH", root / _MUTANTS_TOML)
    monkeypatch.setattr(check_mutation_setup_lanes, "RUST_PROGRAM_TESTS", root / _PROGRAM_TESTS)


def _program_reached(name: TestName) -> Prose:
    """Return the diagnostic for a benchmark program test the Rust lane's skip misses."""
    return Prose(
        f"[rust/program-tests] every mutant's run reaches {name}, which builds the "
        + "benchmark example with a cargo of its own: the lane's skip does not match it"
    )


def test_the_harness_and_every_program_test_skipped_pass(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A skip of the harness and of every program test is the lane the gate expects."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM))
    assert not check_mutation_setup_lanes.rust_lane_runs_no_doc_harness()


def test_skips_written_as_one_argument_each_pass(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``--skip=NAME`` is read as ``--skip NAME`` is."""
    _plant_rust_tests(
        tmp_path,
        monkeypatch,
        [
            CargoTestArg("--"),
            *(CargoTestArg(f"--skip={name}") for name in (RUST_DOC_HARNESS, *_RUST_PROGRAM)),
        ],
    )
    assert not check_mutation_setup_lanes.rust_lane_runs_no_doc_harness()


def test_a_program_test_the_skip_misses_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A program test the skip does not reach is named, and nothing else is."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, _RUST_PROGRAM[0]))
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [
        _program_reached(_RUST_PROGRAM[1])
    ]


def test_an_example_test_a_skip_reaches_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An example's test, which cargo test runs too, is among the tests a skip may drop."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM))
    beside = TestName(f"{_RUST_PROGRAM[0]}_in_the_example")
    _ = plant(
        tmp_path, {RelPath("rust/examples/demo/tests.rs"): Prose(f"#[test]\nfn {beside}() {{}}\n")}
    )
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [_drops("rust", beside)]


def test_a_skip_beyond_the_harness_and_the_program_tests_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A skip reaching a test that is neither the harness nor a program test is named."""
    _plant_rust_tests(
        tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM, _RUST_BESIDE)
    )
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [
        _drops("rust", _RUST_BESIDE)
    ]


def test_a_rust_lane_skipping_no_harness_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A lane skipping the program's tests and not the harness is named."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(*_RUST_PROGRAM))
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [_RUST_HARNESS_RUN]


def test_skips_handed_to_cargo_rather_than_the_test_binaries_are_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Without ``--`` the filters reach cargo, not libtest, so every test runs."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM)[1:])
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [
        _RUST_HARNESS_RUN,
        *(_program_reached(name) for name in _RUST_PROGRAM),
    ]


def test_a_filter_matching_every_test_sharing_its_prefix_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A filter skips every test whose name contains it, so a prefix drops its neighbours."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(TestName("every_"), *_RUST_PROGRAM))
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [
        _drops("rust", _RUST_BESIDE)
    ]


@pytest.mark.parametrize(
    ("beside", "name"),
    [
        pytest.param(
            Prose('#[test]\n#[should_panic(expected = "x]y")]\nfn panics() {}\n'),
            TestName("panics"),
            id="an attribute whose string holds a bracket",
        ),
        pytest.param(
            Prose("#[test]\n// why it is here\n/// and its doc\nfn commented() {}\n"),
            TestName("commented"),
            id="comment lines before fn",
        ),
        pytest.param(
            Prose("#[test]\nconst fn constant() {}\n"), TestName("constant"), id="a const fn"
        ),
        pytest.param(
            Prose('#[test]\nextern "C" fn foreign() {}\n'), TestName("foreign"), id="an extern fn"
        ),
    ],
)
def test_the_rust_tests_are_found_as_rustc_lists_them(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, beside: Prose, name: TestName
) -> None:
    """A test under ``#[test]`` is found whatever sits between the attribute and ``fn``."""
    _plant_rust_tests(
        tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM, name), beside=beside
    )
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [_drops("rust", name)]


def test_a_filter_naming_a_module_path_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A ``--skip`` filter holding ``::`` names a path the gate cannot match by bare name."""
    pathed = TestName(f"tests::{_RUST_PROGRAM[0]}")
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, pathed, _RUST_PROGRAM[1]))
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [
        Prose(
            f"[rust/doc-harness] the lane's skip names {pathed!r}, a path libtest matches against "
            + "a test's module path, which this gate reads by bare name: name the test alone"
        )
    ]


@pytest.mark.parametrize(
    "args",
    [
        pytest.param(Prose("additional_cargo_test_args = 1\n"), id="no list"),
        pytest.param(Prose('additional_cargo_test_args = ["--", 1]\n'), id="an argument no string"),
    ],
)
def test_rust_arguments_that_are_no_strings_exit_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    args: Prose,
) -> None:
    """A configuration whose test arguments are no list of strings stops the gate, naming it."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM))
    _ = (tmp_path / _MUTANTS_TOML).write_text(args)
    assert stderr_of_exit_2(capsys, check_mutation_setup_lanes.rust_lane_runs_no_doc_harness) == (
        f"ERROR: cannot read {tmp_path / _MUTANTS_TOML}: its additional_cargo_test_args is not "
        + "a list of strings\n"
    )


def test_a_rust_source_directory_that_cannot_be_listed_exits_2(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without one of the three source directories the check stops the gate, reading no less."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM))
    examples = tmp_path / "rust" / "examples"
    (examples / "benchmark.rs").unlink()
    examples.rmdir()
    assert stderr_of_exit_2(capsys, check_mutation_setup_lanes.rust_lane_runs_no_doc_harness) == (
        f"ERROR: cannot read {examples}: No such file or directory\n"
    )


def test_a_filter_under_exact_matches_a_whole_name_alone(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Under ``--exact`` a filter skips the test it equals, so part of a name misses it."""
    _plant_rust_tests(
        tmp_path,
        monkeypatch,
        [*_skipping(TestName("every_rust_fence"), *_RUST_PROGRAM), CargoTestArg("--exact")],
    )
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [_RUST_HARNESS_RUN]


def test_a_rust_harness_renamed_is_named(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A harness renamed out from under the skip is named rather than checked against nothing."""
    _plant_rust_tests(
        tmp_path,
        monkeypatch,
        _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM),
        TestName("every_rust_fence_runs"),
    )
    assert check_mutation_setup_lanes.rust_lane_runs_no_doc_harness() == [
        f"[rust/doc-harness] {RUST_DOC_HARNESS} is defined 0 times among the binding's tests "
        + "rather than once: the harness was renamed or duplicated, and the lane's skip is "
        + "checked against a name the tree does not settle"
    ]


@pytest.mark.parametrize(
    "missing",
    [
        pytest.param(_MUTANTS_TOML, id="the configuration"),
        pytest.param(_PROGRAM_TESTS, id="the program's tests"),
    ],
)
def test_a_rust_lane_input_that_is_missing_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    missing: RelPath,
) -> None:
    """Without its configuration or the program's tests the check stops the gate, naming it."""
    _plant_rust_tests(tmp_path, monkeypatch, _skipping(RUST_DOC_HARNESS, *_RUST_PROGRAM))
    (tmp_path / missing).unlink()
    assert stderr_of_exit_2(capsys, check_mutation_setup_lanes.rust_lane_runs_no_doc_harness) == (
        f"ERROR: cannot read {tmp_path / missing}: No such file or directory\n"
    )
