# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The stated-measurements arm finds a BENCHMARKS.md number its sources do not hold.

A planted tree carries a reduced document, schema, baseline set and
residency test that agree; each test plants one disagreement and asserts the
whole list of findings, the clean fixture and each agreeing respelling of it return
none, and a fixture with nothing to compare is a finding of its own.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _benchmarks_tree import (
    CPP,
    DOCUMENT,
    FILES,
    HALF_PERCENT,
    LACK,
    LATENCY,
    PYTHON,
    RESIDENCY_TEST,
    SCALING,
    SCHEMA,
    THROUGHPUT,
    baseline,
    edited_files,
    planted_findings,
    recorded,
    recording,
    reported,
    scaling,
    spread,
    spread_about,
    spreading,
    without,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    from tools._common import RelPath


def test_clean_fixture_has_no_finding(tmp_path: Path) -> None:
    """A document agreeing with every source returns nothing."""
    assert planted_findings(tmp_path, FILES) == list[Prose]()


@pytest.mark.parametrize(
    "files",
    [
        pytest.param(
            edited_files(RESIDENCY_TEST, Prose("32 * 1024"), Prose("31 * 1024 + 1024")),
            id="budget-as-a-sum",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.14, the runtime that"),
            ),
            id="toolchain-release",
        ),
        pytest.param(recorded(compiler=True), id="files-record-both"),
        pytest.param(
            recording(Prose("Python 3.14"), Prose("python"), Prose("r3 3.14.5")),
            id="toolchain-release-after-a-lone-number",
        ),
        pytest.param(
            recording(Prose("Python 13.1"), Prose("python"), Prose("13.1.2")),
            id="toolchain-release-two-digit-major",
        ),
        pytest.param(
            recording(Prose("Python 3.14.5"), Prose("python"), Prose("3.14.5")),
            id="toolchain-release-in-full",
        ),
        pytest.param(
            recording(Prose("Go 1.20"), Prose("go"), Prose("go1.20")),
            id="toolchain-release-of-two-parts",
        ),
        pytest.param(
            recording(Prose("Python 3.14"), Prose("python"), Prose("r3-3.14.5")),
            id="toolchain-release-after-a-dash",
        ),
        pytest.param(
            recording(Prose("Go 1.26"), Prose("go"), Prose("go1.26.3")),
            id="toolchain-release-prefixed",
        ),
        pytest.param(
            recording(
                Prose("rustc 1.97"), Prose("rust"), Prose("rustc 1.97.1 (8bab26f4f 2026-07-14)")
            ),
            id="toolchain-release-named",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("Nothing measured here.\n"),
                Prose("Nothing measured here.\n\n```text\nPython 3.13.0\n```\n"),
            ),
            id="toolchain-version-in-a-fence",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records `Python 3.13`, the runtime that"),
            ),
            id="toolchain-version-in-inline-code",
        ),
        pytest.param(
            edited_files(
                baseline(CPP, THROUGHPUT),
                Prose('"runs": 10,'),
                Prose('"runs": 1000,'),
                edited_files(
                    baseline(PYTHON, THROUGHPUT),
                    Prose('"runs": 10,'),
                    Prose('"runs": 1000,'),
                    edited_files(DOCUMENT, Prose("is 10 runs of"), Prose("is 1,000 runs of")),
                ),
            ),
            id="run-count-with-a-separator",
        ),
        pytest.param(
            spread(Prose("610.0"), Prose("2.5")), id="spread-bound-tightest-above-the-worst"
        ),
        # Neither 2.4 nor 2.1 has an exact binary spelling: the nearest double to 2.4 lies
        # below it, the nearest to 2.1 above it.
        pytest.param(
            spread(Prose("600.0"), Prose("2.4")), id="spread-bound-equal-to-a-worst-of-2.4"
        ),
        pytest.param(
            spread(Prose("525.0"), Prose("2.1")), id="spread-bound-equal-to-a-worst-of-2.1"
        ),
        # The ratio is 2.5% exactly in the decimals the baseline spells, and above 2.5% in the
        # doubles they parse to.
        pytest.param(
            spread_about(Prose("600.1"), Prose("2.5"), Prose("24004.0"), Prose("24,004")),
            id="spread-bound-equal-to-a-worst-in-decimals",
        ),
        pytest.param(
            spread_about(Prose("600.07"), Prose("2.5"), Prose("24002.8"), Prose("24,003")),
            id="spread-bound-equal-to-a-worst-over-a-fractional-mean",
        ),
        pytest.param(spread(Prose("500.0"), Prose("2")), id="spread-bound-without-a-decimal"),
        # 2.404% is less than a tenth under 2.5% and more than an eleventh under it.
        pytest.param(spread(Prose("601.0"), Prose("2.5")), id="spread-bound-under-a-tenth-above"),
        pytest.param(spreading(HALF_PERCENT, Prose(".5")), id="spread-bound-with-a-leading-dot"),
    ],
)
def test_agreeing_respelling_has_no_finding(tmp_path: Path, files: Mapping[RelPath, Prose]) -> None:
    """A source spelled another way that still agrees with the document returns nothing."""
    assert planted_findings(tmp_path, files) == list[Prose]()


@pytest.mark.parametrize(
    ("p50_us", "mean_us", "median", "mean"),
    [
        pytest.param("3.0", "3.6", "3", "3.6", id="median-without-a-decimal"),
        pytest.param("3.2", "4.0", "3.2", "4", id="mean-without-a-decimal"),
        pytest.param("0.5", "3.6", ".5", "3.6", id="median-with-a-leading-dot"),
        pytest.param("3.2", "0.6", "3.2", ".6", id="mean-with-a-leading-dot"),
        pytest.param("13.2", "13.6", "13.2", "13.6", id="figures-of-two-digits"),
    ],
)
def test_latency_figures_spelled_another_way_agree(
    tmp_path: Path, p50_us: Prose, mean_us: Prose, median: Prose, mean: Prose
) -> None:
    """A median and mean the document spells otherwise than the latency baseline still agree."""
    rel = baseline(CPP, LATENCY)
    files = edited_files(rel, Prose('"p50_us": 3.2'), Prose(f'"p50_us": {p50_us}'))
    files = edited_files(rel, Prose('"mean_us": 3.6'), Prose(f'"mean_us": {mean_us}'), files)
    files = edited_files(
        DOCUMENT, Prose("median of 3.2 µs"), Prose(f"median of {median} µs"), files
    )
    files = edited_files(DOCUMENT, Prose("mean of 3.6 µs"), Prose(f"mean of {mean} µs"), files)
    assert planted_findings(tmp_path, files) == list[Prose]()


def test_each_stated_version_is_reported_once_in_the_order_stated(tmp_path: Path) -> None:
    """A version the prose states twice is one finding, and the findings follow the prose."""
    files = edited_files(
        DOCUMENT,
        Prose("records the runtime that"),
        Prose("records Python 3.13, then Python 3.12 and Python 3.13 again, the runtime that"),
    )
    assert planted_findings(tmp_path, files) == reported(
        [
            Prose("states Python 3.13; the baselines record ['3.14.5']"),
            Prose("states Python 3.12; the baselines record ['3.14.5']"),
        ]
    )


@pytest.mark.parametrize(
    ("files", "expected"),
    [
        pytest.param(
            edited_files(DOCUMENT, Prose("| Lane A | 200,000 |"), Prose("| Lane A | 210,000 |")),
            ["Lane A, cpp: the table says 210,000, the baseline 200,000"],
            id="table-cell",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("| 100,000 |"), Prose("| 100,000 | 7 |")),
            ["Lane A: 3 cells under 2 columns"],
            id="row-with-a-cell-past-the-columns",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("| 50,000 | 25,000 |"), Prose("| 50,000 |")),
            ["Lane B: 1 cells under 2 columns"],
            id="row-short-of-the-columns",
        ),
        pytest.param(
            spread(Prose("610.0"), Prose("2.4")),
            [
                "claims at most 2.4%, the baselines' worst is 2.44% (Lane B python),"
                + " which needs 2.5%"
            ],
            id="spread-bound-under-a-worst-it-rounds-to",
        ),
        pytest.param(
            spread(Prose("600.1"), Prose("2.4")),
            [
                "claims at most 2.4%, the baselines' worst is 2.40% (Lane B python),"
                + " which needs 2.5%"
            ],
            id="spread-bound-just-under-the-worst",
        ),
        # 2.3 less a tenth is 2.2 exactly, which binary floating point puts below 2.2.
        pytest.param(
            spread(Prose("550.0"), Prose("2.3")),
            [
                "claims at most 2.3%, the baselines' worst is 2.20% (Lane B python),"
                + " which needs 2.2%"
            ],
            id="spread-bound-a-tenth-above-the-worst",
        ),
        # The ratio is 2.4% exactly in the decimals the baseline spells, and above 2.4% in the
        # doubles they parse to.
        pytest.param(
            spread_about(Prose("600.6"), Prose("2.5"), Prose("25025.0"), Prose("25,025")),
            [
                "claims at most 2.5%, the baselines' worst is 2.40% (Lane B python),"
                + " which needs 2.4%"
            ],
            id="spread-bound-a-tenth-above-a-worst-in-decimals",
        ),
        pytest.param(
            edited_files(
                baseline(CPP, THROUGHPUT),
                Prose('"fps_stdev": 2000.0'),
                Prose('"fps_stdev": 6000.0'),
            ),
            [
                "claims at most 2.0%, the baselines' worst is 3.00% (Lane A cpp),"
                + " which needs 3.0%"
            ],
            id="spread-bound-under-the-worst-lane",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("| Lane B | 50,000 | 25,000 |\n"), Prose("")),
            ["the baselines carry a lane the table omits: 'Lane B'"],
            id="lane-omitted",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("| Lane B |"), Prose("| Lane C |")),
            [
                "the table has a lane the baselines do not: 'Lane C'",
                "the baselines carry a lane the table omits: 'Lane B'",
            ],
            id="lane-invented",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("| C++ (fps) |"), Prose("| Zig (fps) |")),
            ["the table has a column no binding answers to: 'Zig'"],
            id="column-unknown",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("| Python (fps) |"),
                Prose("| Python (fps) | Rust (fps) |"),
                edited_files(
                    DOCUMENT,
                    Prose("| 100,000 |"),
                    Prose("| 100,000 | 1 |"),
                    edited_files(DOCUMENT, Prose("| 25,000 |"), Prose("| 25,000 | 1 |")),
                ),
            ),
            [
                "Lane A, rust: no committed throughput baseline has the lane",
                "Lane B, rust: no committed throughput baseline has the lane",
            ],
            id="column-without-a-baseline",
        ),
        pytest.param(
            edited_files(
                DOCUMENT, Prose("is 10 runs of 10,000 frames"), Prose("is 5 runs of 10,000 frames")
            ),
            [
                f"benchmarks/results/{language}_throughput_baseline.json: {lane} is 10 runs of"
                + " 10000 frames, the section says 5 of 10000"
                for language in (PYTHON, CPP)
                for lane in ("Lane A", "Lane B")
            ],
            id="throughput-count",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("runs of 10,000 frames"), Prose("runs of 5,000 frames")),
            [
                f"benchmarks/results/{language}_throughput_baseline.json: {lane} is 10 runs of"
                + " 10000 frames, the section says 10 of 5000"
                for language in (PYTHON, CPP)
                for lane in ("Lane A", "Lane B")
            ],
            id="frame-count",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("is 10 runs of"), Prose("is 0 runs of")),
            ["the section states the throughput run count of 0"],
            id="zero-count",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("baseline 10,000 timed"), Prose("baseline 5,000 timed")),
            [
                f"benchmarks/results/{language}_latency_baseline.json: CAN 2.0B Streaming LTL"
                + " counts 10000 operations, the section says 5000"
                for language in (PYTHON, CPP)
            ],
            id="latency-count",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("baseline 10,000 timed"), Prose("baseline 20,000 timed")),
            [
                f"benchmarks/results/{language}_latency_baseline.json: CAN 2.0B Streaming LTL"
                + " counts 10000 operations, the section says 20000"
                for language in (PYTHON, CPP)
            ],
            id="latency-count-above-the-rows",
        ),
        pytest.param(
            edited_files(
                SCHEMA,
                Prose("full: [1000, 5000, 10000]"),
                Prose("full: [1000, 5000, 10000, 50000]"),
            ),
            [
                f"benchmarks/results/{language}_scaling_baseline.json: {sweep} has 3 sizes,"
                + " the full sweep has 4"
                for language in (PYTHON, CPP)
                for sweep in ("trace_size_can20", "trace_size_canfd")
            ],
            id="scaling-sweep",
        ),
        pytest.param(
            edited_files(SCHEMA, Prose("full: [1000, 5000, 10000]"), Prose("full: [1000, 5000]")),
            [
                f"benchmarks/results/{language}_scaling_baseline.json: {sweep} has 3 sizes,"
                + " the full sweep has 2"
                for language in (PYTHON, CPP)
                for sweep in ("trace_size_can20", "trace_size_canfd")
            ],
            id="scaling-sweep-past-the-schema",
        ),
        pytest.param(
            {**FILES, baseline(CPP, SCALING): scaling(CPP, canfd=(1000, 5000))},
            [
                "benchmarks/results/cpp_scaling_baseline.json: trace_size_canfd has 2 sizes,"
                + " the full sweep has 3"
            ],
            id="scaling-canfd-sweep",
        ),
        pytest.param(
            without(baseline(PYTHON, SCALING)),
            ["benchmarks/results/python_scaling_baseline.json is not a committed baseline"],
            id="baseline-missing",
        ),
        pytest.param(
            edited_files(baseline(CPP, LATENCY), Prose('"cpp"'), Prose('"go"')),
            ["benchmarks/results/cpp_latency_baseline.json says go latency"],
            id="baseline-mislabelled",
        ),
        pytest.param(
            edited_files(
                baseline(CPP, LATENCY),
                Prose('"benchmark": "latency"'),
                Prose('"benchmark": "throughput"'),
            ),
            ["benchmarks/results/cpp_latency_baseline.json says cpp throughput"],
            id="baseline-mode-mislabelled",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("median of 3.2 µs"), Prose("median of 3.1 µs")),
            ["the median reads 3.1 µs, the committed baseline holds 3.2 µs"],
            id="latency-median",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("grows by 32 MiB"), Prose("grows by 64 MiB")),
            ["states a 64 MiB budget, the test asserts 32 MiB"],
            id="residency-budget",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("grows by 32 MiB"), Prose("grows by 16 MiB")),
            ["states a 16 MiB budget, the test asserts 32 MiB"],
            id="residency-budget-below-the-test",
        ),
        pytest.param(
            edited_files(
                DOCUMENT, Prose("session of 100,000 frames"), Prose("session of 10,000 frames")
            ),
            ["names a session of 10,000 frames, the test runs [100000, 150000]"],
            id="residency-frames",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.13, the runtime that"),
            ),
            ["states Python 3.13; the baselines record ['3.14.5']"],
            id="toolchain-version",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 4.5, the runtime that"),
            ),
            ["states Python 4.5; the baselines record ['3.14.5']"],
            id="toolchain-version-inside-the-recorded",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.1, the runtime that"),
            ),
            ["states Python 3.1; the baselines record ['3.14.5']"],
            id="toolchain-version-prefix-of-the-recorded",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.14 and Python 3.13, the runtime that"),
            ),
            ["states Python 3.13; the baselines record ['3.14.5']"],
            id="toolchain-version-stated-second",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Go 1.26, the runtime that"),
            ),
            ["states Go 1.26; the baselines record []"],
            id="toolchain-version-unrecorded",
        ),
        pytest.param(
            recording(Prose("Go 1.26.2"), Prose("go"), Prose("go1.26.3")),
            ["states Go 1.26.2; the baselines record ['go1.26.3']"],
            id="toolchain-patch-release",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.14, the runtime that"),
                edited_files(
                    baseline(PYTHON, LATENCY),
                    Prose('"python": "3.14.5"'),
                    Prose('"python": "unknown"'),
                ),
            ),
            ["states Python 3.14; the baselines record ['3.14.5', 'unknown']"],
            id="toolchain-version-unnumbered",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("`system` object"), Prose("system entry")),
            ["does not name the system object as where the runtime versions are"],
            id="system-object-unnamed",
        ),
        pytest.param(
            edited_files(
                baseline(PYTHON, SCALING),
                Prose('"benchmark": "scaling",'),
                Prose('"benchmark": "scaling", "parameters": {"runs": 5},'),
            ),
            [
                "benchmarks/results/python_scaling_baseline.json records what the section says"
                + " the committed files lack"
            ],
            id="lack-sentence-stale",
        ),
        pytest.param(
            edited_files(
                baseline(CPP, LATENCY),
                Prose('"build_type": "Release"'),
                Prose('"build_type": "Release", "compiler": "c"'),
            ),
            [
                "benchmarks/results/cpp_latency_baseline.json records what the section says"
                + " the committed files lack"
            ],
            id="lack-sentence-stale-compiler",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("; the committed files carry neither"), Prose("")),
            [
                f"benchmarks/results/{language}_{mode}_baseline.json {LACK}"
                for language in (CPP, PYTHON)
                for mode in (LATENCY, SCALING, THROUGHPUT)
            ],
            id="lack-sentence-missing",
        ),
        pytest.param(
            recorded(compiler=False),
            [
                f"benchmarks/results/cpp_{mode}_baseline.json {LACK}"
                for mode in (LATENCY, SCALING, THROUGHPUT)
            ],
            id="lack-sentence-missing-compiler",
        ),
    ],
)
def test_planted_disagreement_is_found(
    tmp_path: Path, files: Mapping[RelPath, Prose], expected: Sequence[Prose]
) -> None:
    """Each planted disagreement between the document and a source yields the findings naming it."""
    assert planted_findings(tmp_path, files) == reported(expected)


@pytest.mark.parametrize("bound", [Prose("5.1"), Prose(".5"), Prose("10.0")])
def test_a_bound_off_the_worst_is_quoted_as_spelled(tmp_path: Path, bound: Prose) -> None:
    """A bound off the baselines' worst spread is reported as the document spells it."""
    files = edited_files(DOCUMENT, Prose("exceeds 2.0% of"), Prose(f"exceeds {bound}% of"))
    worst = Prose("the baselines' worst is 2.00% (Lane B python), which needs 2.0%")
    assert planted_findings(tmp_path, files) == reported(
        [Prose(f"claims at most {bound}%, {worst}")]
    )


@pytest.mark.parametrize(
    ("files", "expected"),
    [
        pytest.param(
            without(DOCUMENT),
            ["not among the tracked documents, so nothing it states is checked"],
            id="document-untracked",
        ),
        pytest.param(
            {rel: text for rel, text in FILES.items() if "_baseline.json" not in rel},
            ["no committed baseline under benchmarks/results/ to compare with"],
            id="no-baseline",
        ),
        pytest.param(
            edited_files(
                baseline(CPP, THROUGHPUT),
                Prose('"fps_mean"'),
                Prose('"mean_fps"'),
                edited_files(
                    baseline(PYTHON, THROUGHPUT), Prose('"fps_mean"'), Prose('"mean_fps"')
                ),
            ),
            [
                *[
                    f"benchmarks/results/{language}_throughput_baseline.json: a row has no mean"
                    + " and spread to compare the table with"
                    for language in (CPP, CPP, PYTHON, PYTHON)
                ],
                "no committed throughput baseline carries a lane to compare the table with",
            ],
            id="no-throughput-lane",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("## Canonical Results"), Prose("## Results")),
            ["has no Canonical Results section"],
            id="no-canonical-section",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("| Benchmark |"), Prose("| Lane |")),
            ["the canonical table has no header row opening on Benchmark"],
            id="no-table-header",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("| Benchmark |"), Prose("## Elsewhere\n\n| Benchmark |")),
            ["the canonical table has no header row opening on Benchmark"],
            id="table-past-the-section",
        ),
        pytest.param(
            edited_files(
                baseline(CPP, THROUGHPUT),
                Prose('"fps_mean": 200000.0,'),
                Prose('"mean_fps": 200000.0,'),
            ),
            [
                "benchmarks/results/cpp_throughput_baseline.json: a row has no mean and spread"
                + " to compare the table with",
                "Lane A, cpp: no committed throughput baseline has the lane",
            ],
            id="row-without-mean",
        ),
        pytest.param(
            edited_files(
                DOCUMENT, Prose("standard deviation exceeds"), Prose("spread stays under")
            ),
            ["the section no longer states a standard-deviation bound"],
            id="no-bound",
        ),
        pytest.param(
            edited_files(DOCUMENT, Prose("## Local baselines"), Prose("## Baselines")),
            ["has no Local baselines section"],
            id="no-local-section",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("`benchmarks/results/<binding>_<mode>_baseline.json`, one"),
                Prose("One baseline"),
            ),
            ["the section does not name the baseline files by their pattern"],
            id="no-file-pattern",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("A throughput baseline is 10 runs of"),
                Prose("Each lane ran 10 times over"),
            ),
            [
                "the section no longer states the throughput run count",
                "the section no longer states the throughput frame count",
            ],
            id="no-count-phrase",
        ),
        pytest.param(
            edited_files(
                DOCUMENT, Prose("10,000 frames per lane"), Prose("10,000 CAN frames per lane")
            ),
            ["the section no longer states the throughput frame count"],
            id="no-frame-count-phrase",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("latency baseline 10,000 timed operations"),
                Prose("latency baseline times 10,000 operations"),
            ),
            ["the section no longer states the latency operation count"],
            id="no-operation-count-phrase",
        ),
        pytest.param(
            without(SCHEMA),
            ["benchmarks/SCHEMA.yaml is not tracked, so the baseline roster goes unchecked"],
            id="no-schema",
        ),
        pytest.param(
            without(RESIDENCY_TEST),
            [
                "python/tests/test_streaming_residency.py is not tracked,"
                + " so the residency sentence goes unchecked"
            ],
            id="no-residency-test",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("median of 3.2 µs and a mean of 3.6 µs"),
                Prose("a few microseconds"),
            ),
            ["no longer states a per-frame median and mean"],
            id="no-latency-phrase",
        ),
        pytest.param(
            edited_files(
                baseline(CPP, LATENCY),
                Prose('"name": "CAN 2.0B Streaming LTL"'),
                Prose('"name": "CAN-FD Streaming LTL"'),
            ),
            [f"{baseline(CPP, LATENCY)} carries no 'CAN 2.0B Streaming LTL' lane"],
            id="no-latency-lane",
        ),
        pytest.param(
            without(baseline(CPP, LATENCY)),
            [
                "benchmarks/results/cpp_latency_baseline.json is not a committed baseline",
                "the per-frame median and mean go unchecked:"
                + " benchmarks/results/cpp_latency_baseline.json is not a committed baseline",
            ],
            id="no-latency-baseline",
        ),
        pytest.param(
            edited_files(
                DOCUMENT,
                Prose("fails a session of 100,000 frames whose peak resident set grows by 32 MiB"),
                Prose("bounds the peak resident set of a session"),
            ),
            ["no longer states a residency budget over a frame count"],
            id="no-residency-sentence",
        ),
        pytest.param(
            edited_files(RESIDENCY_TEST, Prose("_MAX_GROWTH_KIB"), Prose("_BUDGET_KIB")),
            ["python/tests/test_streaming_residency.py no longer names its budget and its cases"],
            id="no-residency-constants",
        ),
        pytest.param(
            edited_files(RESIDENCY_TEST, Prose("_CASES"), Prose("_SHAPES")),
            ["python/tests/test_streaming_residency.py no longer names its budget and its cases"],
            id="no-residency-cases",
        ),
        pytest.param(
            edited_files(RESIDENCY_TEST, Prose("32 * 1024"), Prose("0")),
            ["python/tests/test_streaming_residency.py no longer names its budget and its cases"],
            id="residency-budget-zero",
        ),
    ],
)
def test_nothing_to_compare_is_a_finding(
    tmp_path: Path, files: Mapping[RelPath, Prose], expected: Sequence[Prose]
) -> None:
    """A fixture the arm cannot compare, a phrase or a file gone, is reported rather than passed."""
    assert planted_findings(tmp_path, files) == reported(expected)


_NO_BOUND = Prose("the section no longer states a standard-deviation bound")
_NO_FIGURES = Prose("no longer states a per-frame median and mean")


@pytest.mark.parametrize(
    ("stated", "spelled", "expected"),
    [
        pytest.param("2.0%", "2..0%", _NO_BOUND, id="bound-with-a-doubled-dot"),
        pytest.param("2.0%", "2.0.%", _NO_BOUND, id="bound-with-a-trailing-dot"),
        pytest.param("2.0%", "2.0.1%", _NO_BOUND, id="bound-with-two-dots"),
        pytest.param("2.0%", "2.%", _NO_BOUND, id="bound-without-fraction-digits"),
        pytest.param("3.2 µs", "3..2 µs", _NO_FIGURES, id="median-with-a-doubled-dot"),
        pytest.param("3.2 µs", "3. µs", _NO_FIGURES, id="median-without-fraction-digits"),
        pytest.param("3.6 µs", "3.6. µs", _NO_FIGURES, id="mean-with-a-trailing-dot"),
        pytest.param("3.6 µs", "3..6 µs", _NO_FIGURES, id="mean-with-a-doubled-dot"),
        pytest.param("3.6 µs", "3. µs", _NO_FIGURES, id="mean-without-fraction-digits"),
    ],
)
def test_a_number_spelled_amiss_states_none(
    tmp_path: Path, stated: Prose, spelled: Prose, expected: Prose
) -> None:
    """A bound or latency figure with a stray dot, or no digit after its dot, states no number."""
    assert planted_findings(tmp_path, edited_files(DOCUMENT, stated, spelled)) == reported(
        [expected]
    )


_NOT_FINITE = Prose("has a mean or spread that is not finite")
_NOT_POSITIVE = Prose("has no positive mean to measure its spread against")


@pytest.mark.parametrize(
    ("held", "value", "reason"),
    [
        pytest.param(
            '"fps_stdev": 500.0', '"fps_stdev": 1e400', _NOT_FINITE, id="spread-past-a-double"
        ),
        pytest.param(
            '"fps_stdev": 500.0', '"fps_stdev": NaN', _NOT_FINITE, id="spread-not-a-number"
        ),
        pytest.param(
            '"fps_mean": 25000.0', '"fps_mean": 1e400', _NOT_FINITE, id="mean-past-a-double"
        ),
        pytest.param('"fps_mean": 25000.0', '"fps_mean": 0.0', _NOT_POSITIVE, id="mean-of-zero"),
    ],
)
def test_a_row_not_finite_is_left_out(
    tmp_path: Path, held: Prose, value: Prose, reason: Prose
) -> None:
    """A row whose mean or spread is not finite, or whose mean is not positive, joins no lane."""
    rel = baseline(PYTHON, THROUGHPUT)
    # Python's Lane B left out, every lane left spreads by 1.0% of its mean.
    files = edited_files(DOCUMENT, Prose("exceeds 2.0% of"), Prose("exceeds 1.0% of"))
    files = edited_files(rel, held, value, files)
    left_out = Prose(f"{rel}: Lane B {reason}")
    unheld = Prose("Lane B, python: no committed throughput baseline has the lane")
    assert planted_findings(tmp_path, files) == reported([left_out, unheld])


def test_a_mean_below_one_is_positive(tmp_path: Path) -> None:
    """A mean between zero and one is positive, so its row joins its lane and is compared."""
    rel = baseline(PYTHON, THROUGHPUT)
    files = edited_files(rel, Prose('"fps_mean": 25000.0'), Prose('"fps_mean": 0.5'))
    assert planted_findings(tmp_path, files) == reported(
        [
            Prose("Lane B, python: the table says 25,000, the baseline 0"),
            Prose(
                "claims at most 2.0%, the baselines' worst is 100000.00% (Lane B python),"
                + " which needs 100000.0%"
            ),
        ]
    )


def test_untracked_residency_test_is_not_read(tmp_path: Path) -> None:
    """A residency test on disk that git does not track is no source for the residency sentence."""
    assert planted_findings(tmp_path, FILES, untracked=[RESIDENCY_TEST]) == reported(
        [
            Prose(
                "python/tests/test_streaming_residency.py is not tracked,"
                + " so the residency sentence goes unchecked"
            )
        ]
    )
