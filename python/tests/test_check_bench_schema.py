# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools/check_bench_schema.py``'s reading of the runner: every lane is told what the schema pins.

The arm reads ``benchmarks/run_all.sh`` as text, so the cases plant a runner
of four lane arms and change one thing in it at a time; the last cases read
the real runner against the real schema for the modes the gate holds, and the
gate's own tiny workloads against the schema's flags.
"""

from __future__ import annotations

import re
from typing import Final, TypedDict, cast

import pytest
import yaml

from tools.check_bench_schema import (
    MODE_ARGS,
    RUNNER_MODES_HELD,
    RUNNER_PATH,
    SCHEMA_PATH,
    Finding,
    Flag,
    ModeName,
    ShellText,
    lanes_missing_pinned_flags,
)

from aletheia.common_types import Prose


class _Mode(TypedDict):
    """A mode of the schema, in the field this file reads."""

    flags: list[Flag]


class Schema(TypedDict):
    """The schema, in the field this file reads."""

    modes: dict[ModeName, _Mode]


LATENCY: Final = ModeName("latency")
PINNED: Final = [Flag("--ops"), Flag("--warmup")]
BINDINGS: Final = ("python", "cpp", "go", "rust")

# A runner whose four latency lanes carry both pinned flags from one word each,
# each count with a default, and hand their variables to the harnesses.
RUNNER: Final = ShellText(
    """FRAMES=10000
RUNS=5
WARMUP=500
case $BENCH in
    latency)    PYTHON_ARGS=(--ops "$FRAMES" --warmup "$WARMUP" "${PYTHON_ARGS[@]}") ;;
esac
run_benchmark Python out python3 -m "benchmarks.$BENCH" "${PYTHON_ARGS[@]}"
case $BENCH in
    latency)    CPP_ARGS+=(--ops "$FRAMES" --warmup "$WARMUP") ;;
    scaling)    CPP_ARGS+=(--runs "$RUNS")
                if [[ "$QUICK" == 1 ]]; then CPP_ARGS+=(--quick); fi ;;
esac
run_benchmark C++ out "$CPP_BIN" "${CPP_ARGS[@]}"
case $BENCH in
    latency)    GO_ARGS+=(--ops "$FRAMES" --warmup "$WARMUP") ;;
esac
run_benchmark Go out "$GO_BIN" "${GO_ARGS[@]}"
case $BENCH in
    latency)    RUST_ARGS+=(--ops "$FRAMES" --warmup "$WARMUP") ;;
esac
run_benchmark Rust out "$RUST_BIN" "${RUST_ARGS[@]}"
"""
)
GO_ARM: Final = Prose('    latency)    GO_ARGS+=(--ops "$FRAMES" --warmup "$WARMUP") ;;\n')


def _edited(old: Prose, new: Prose) -> ShellText:
    """Return the planted runner with ``old`` replaced once by ``new``."""
    text = str(RUNNER)
    assert text.count(old) == 1, old
    return ShellText(text.replace(old, new))


def _findings(runner: ShellText) -> list[Finding]:
    return lanes_missing_pinned_flags(runner, LATENCY, PINNED)


def test_a_runner_whose_lanes_carry_every_pinned_flag_has_no_finding() -> None:
    """Four lanes, both flags from one word each, both counts with a default: nothing to say."""
    assert not _findings(RUNNER)


def test_a_lane_not_told_a_pinned_flag_is_named_with_the_flag() -> None:
    """A lane that drops ``--warmup`` warms by its harness's own default, so it is named."""
    runner = _edited(GO_ARM, Prose('    latency)    GO_ARGS+=(--ops "$FRAMES") ;;\n'))
    assert _findings(runner) == [
        Finding("[go / latency] the lane is not told --warmup, which the schema pins")
    ]


def test_a_flag_a_comment_names_is_not_one_the_lane_is_told() -> None:
    """A comment saying why ``--warmup`` is absent does not pass it."""
    runner = _edited(
        GO_ARM,
        Prose(
            '    latency)    GO_ARGS+=(--ops "$FRAMES")  # the default stands in for --warmup\n;;\n'
        ),
    )
    assert _findings(runner) == [
        Finding("[go / latency] the lane is not told --warmup, which the schema pins")
    ]


def test_a_lane_arm_the_runner_lacks_is_named() -> None:
    """A binding with no latency arm is told nothing, which is the finding, and the whole of it."""
    runner = _edited(
        Prose('    latency)    RUST_ARGS+=(--ops "$FRAMES" --warmup "$WARMUP") ;;\n'), Prose("")
    )
    unhanded = ShellText(str(runner).replace(' "${RUST_ARGS[@]}"', ""))
    for text in (runner, unhanded):
        assert _findings(text) == [
            Finding("[rust / latency] the runner has no lane arm for the mode")
        ]


def test_every_arm_of_the_mode_is_read() -> None:
    """A second arm filling the same lane for the mode without the flag is the lane's last word."""
    runner = _edited(
        GO_ARM,
        Prose(GO_ARM + 'case $BENCH in\n    latency)    GO_ARGS=(--ops "$FRAMES") ;;\nesac\n'),
    )
    assert _findings(runner) == [
        Finding("[go / latency] the lane is not told --warmup, which the schema pins")
    ]


def test_a_variable_never_handed_to_the_harness_is_named() -> None:
    """A lane filled and never passed tells its harness nothing."""
    runner = _edited(Prose(' "${GO_ARGS[@]}"'), Prose(""))
    assert _findings(runner) == [Finding("[go / latency] GO_ARGS is never handed to the harness")]


def test_a_count_passed_from_a_variable_with_no_default_is_named() -> None:
    """A lane told ``--warmup "$WARMUP"`` with no ``WARMUP=<n>`` line passes an empty count."""
    runner = _edited(Prose("WARMUP=500\n"), Prose(""))
    assert _findings(runner) == [
        Finding(f"[{binding} / latency] --warmup passes $WARMUP, which has no default")
        for binding in BINDINGS
    ]


def test_a_default_that_is_not_a_whole_number_is_no_default() -> None:
    """``WARMUP=$OTHER`` records nothing a lane can be told."""
    runner = _edited(Prose("WARMUP=500\n"), Prose("WARMUP=$OTHER\n"))
    assert len(_findings(runner)) == len(BINDINGS)


@pytest.mark.parametrize("spelling", ['"${WARMUP}"', "$WARMUP", "${WARMUP}"])
def test_every_spelling_of_a_variable_reads_as_that_variable(spelling: Prose) -> None:
    """Braced or unquoted, the word names the same variable and its default."""
    runner = _edited(
        GO_ARM, Prose(f'    latency)    GO_ARGS+=(--ops "$FRAMES" --warmup {spelling}) ;;\n')
    )
    assert not _findings(runner)
    without = ShellText(str(runner).replace("WARMUP=500\n", ""))
    assert len(_findings(without)) == len(BINDINGS)


def test_a_variable_named_with_an_underscore_or_a_digit_is_read_whole() -> None:
    """``$WARMUP_2`` is one variable, and one with no default."""
    runner = _edited(
        GO_ARM, Prose('    latency)    GO_ARGS+=(--ops "$FRAMES" --warmup "$WARMUP_2") ;;\n')
    )
    assert Finding("[go / latency] --warmup passes $WARMUP_2, which has no default") in _findings(
        runner
    )


def test_lanes_told_a_flag_from_different_words_are_named() -> None:
    """Three lanes warming from ``$WARMUP`` and one from a literal measure two ways."""
    runner = _edited(GO_ARM, Prose('    latency)    GO_ARGS+=(--ops "$FRAMES" --warmup 2) ;;\n'))
    assert _findings(runner) == [
        Finding("[latency] the lanes are told --warmup from different words: $WARMUP, 2")
    ]


def test_a_hyphenated_flag_is_read_whole() -> None:
    """``--warm-up`` is one flag, not ``--warm``."""
    runner = ShellText(str(RUNNER).replace("--warmup", "--warm-up"))
    assert not lanes_missing_pinned_flags(runner, LATENCY, [Flag("--ops"), Flag("--warm-up")])
    assert lanes_missing_pinned_flags(runner, LATENCY, [Flag("--warm")]) == [
        Finding(f"[{binding} / latency] the lane is not told --warm, which the schema pins")
        for binding in BINDINGS
    ]


def test_a_flag_the_schema_does_not_pin_may_differ_between_lanes() -> None:
    """Only a pinned flag owes the lanes one word."""
    runner = _edited(GO_ARM, Prose('    latency)    GO_ARGS+=(--ops 7 --warmup "$WARMUP") ;;\n'))
    assert not lanes_missing_pinned_flags(runner, LATENCY, [Flag("--warmup")])
    assert _findings(runner) == [
        Finding("[latency] the lanes are told --ops from different words: $FRAMES, 7")
    ]


def test_a_flag_carried_by_a_later_line_of_the_arm_counts() -> None:
    """A multi-line arm, ``--quick`` added under an ``if``, carries the flag."""
    scaling = lanes_missing_pinned_flags(
        RUNNER, ModeName("scaling"), [Flag("--runs"), Flag("--quick")]
    )
    assert scaling == [
        Finding(f"[{binding} / scaling] the runner has no lane arm for the mode")
        for binding in ("python", "go", "rust")
    ]


def test_a_flag_in_another_mode_s_arm_does_not_count() -> None:
    """A flag the throughput arm carries is not one the latency lane was told."""
    runner = _edited(
        GO_ARM,
        Prose(
            '    throughput) GO_ARGS+=(--frames "$FRAMES" --warmup "$WARMUP") ;;\n'
            + '    latency)    GO_ARGS+=(--ops "$FRAMES") ;;\n'
        ),
    )
    assert _findings(runner) == [
        Finding("[go / latency] the lane is not told --warmup, which the schema pins")
    ]


def _schema() -> Schema:
    return cast("Schema", yaml.safe_load(SCHEMA_PATH.read_text(encoding="utf-8")))


@pytest.mark.parametrize("mode", RUNNER_MODES_HELD)
def test_the_real_runner_tells_every_lane_what_the_schema_pins(mode: ModeName) -> None:
    """The arm as the gate runs it, over the tree's runner and schema."""
    flags = _schema()["modes"][mode]["flags"]
    pinned = [Flag(flag) for flag in flags if flag != "--json"]
    runner = ShellText(RUNNER_PATH.read_text(encoding="utf-8"))
    assert not lanes_missing_pinned_flags(runner, mode, pinned)


def test_the_gate_s_workloads_pass_every_flag_the_schema_pins_and_no_other() -> None:
    """``MODE_ARGS`` is the schema's flag list per mode: a flag the schema drops or adds is seen."""
    for mode, pins in _schema()["modes"].items():
        passed = {Flag(word) for word in MODE_ARGS[mode] if word.startswith("--")}
        assert passed == set(pins["flags"]), mode


def test_the_planted_runner_s_arms_are_the_real_runner_s_shapes() -> None:
    """The planted latency arms are lines of the real runner, so the cases above read it."""
    runner = RUNNER_PATH.read_text(encoding="utf-8")
    for line in str(RUNNER).splitlines():
        if re.match(r"^\s*latency\)", line):
            assert line in runner, line
