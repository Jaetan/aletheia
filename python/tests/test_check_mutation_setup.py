# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_mutation_setup``'s Rust skip: the harness and the program's tests alone.

The gate is pointed at a planted tree: ``rust/tests`` defining the doc-example
harness, a test beside it, and the benchmark program's tests, and a
``rust/.cargo/mutants.toml`` whose skip filters are the case under test.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final

from tools import check_mutation_setup
from tools.check_mutation_setup import RUST_DOC_HARNESS, TestName

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

_BESIDE: Final = TestName("every_listed_document_is_tracked")
_PROGRAM: Final = (TestName("a_refusal_exits_1"), TestName("a_report_is_written"))


def _plant(root: Path, monkeypatch: pytest.MonkeyPatch, skips: list[TestName]) -> None:
    """Plant the Rust tests and a lane skipping ``skips``, and point the gate there."""
    tests = root / "rust" / "tests"
    tests.mkdir(parents=True)
    (root / "rust" / "src").mkdir()
    _ = (tests / "doc_examples.rs").write_text(
        f"#[test]\nfn {RUST_DOC_HARNESS}() {{}}\n#[test]\nfn {_BESIDE}() {{}}\n", encoding="utf-8"
    )
    program = tests / "benchmark_program.rs"
    _ = program.write_text(
        "".join(f"#[test]\nfn {name}() {{}}\n" for name in _PROGRAM), encoding="utf-8"
    )
    toml = root / "rust" / ".cargo" / "mutants.toml"
    toml.parent.mkdir()
    args = ", ".join(['"--"', *(f'"--skip", "{name}"' for name in skips)])
    _ = toml.write_text(f"additional_cargo_test_args = [{args}]\n", encoding="utf-8")
    monkeypatch.setattr(check_mutation_setup, "REPO_ROOT", root)
    monkeypatch.setattr(check_mutation_setup, "MUTANTS_TOML_PATH", toml)
    monkeypatch.setattr(check_mutation_setup, "RUST_PROGRAM_TESTS", program)


def test_the_harness_and_every_program_test_skipped_pass(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A skip of the harness and of every program test is the lane the gate expects."""
    _plant(tmp_path, monkeypatch, [RUST_DOC_HARNESS, *_PROGRAM])
    assert check_mutation_setup.rust_lane_runs_no_doc_harness() == []


def test_a_program_test_the_skip_misses_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A program test the skip does not reach is named, and nothing else is."""
    _plant(tmp_path, monkeypatch, [RUST_DOC_HARNESS, _PROGRAM[0]])
    assert check_mutation_setup.rust_lane_runs_no_doc_harness() == [
        f"[rust/program-tests] every mutant's run reaches {_PROGRAM[1]}, which builds the "
        + "benchmark example with a cargo of its own: the lane's skip does not match it"
    ]


def test_an_example_test_a_skip_reaches_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An example's test, which cargo test runs too, is among the tests a skip may drop."""
    _plant(tmp_path, monkeypatch, [RUST_DOC_HARNESS, *_PROGRAM])
    example = tmp_path / "rust" / "examples" / "demo" / "tests.rs"
    example.parent.mkdir(parents=True)
    beside = TestName(f"{_PROGRAM[0]}_in_the_example")
    _ = example.write_text(f"#[test]\nfn {beside}() {{}}\n", encoding="utf-8")
    assert check_mutation_setup.rust_lane_runs_no_doc_harness() == [
        f"[rust/doc-harness] the lane's skip also drops {beside}, which is not the "
        + "doc-example harness, so no mutant is tested against it"
    ]


def test_a_skip_beyond_the_harness_and_the_program_tests_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A skip reaching a test that is neither the harness nor a program test is named."""
    _plant(tmp_path, monkeypatch, [RUST_DOC_HARNESS, *_PROGRAM, _BESIDE])
    assert check_mutation_setup.rust_lane_runs_no_doc_harness() == [
        f"[rust/doc-harness] the lane's skip also drops {_BESIDE}, which is not the "
        + "doc-example harness, so no mutant is tested against it"
    ]
