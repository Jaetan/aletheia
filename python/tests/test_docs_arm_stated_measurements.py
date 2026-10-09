# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The stated-measurements arm finds a BENCHMARKS.md number its sources do not hold.

A planted tree carries a reduced document, schema, baseline set and
residency test that agree; each test plants one disagreement and asserts the
finding, the clean fixture and each agreeing respelling of it return none, and a
fixture with nothing to compare is a finding of its own.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.stated_measurements import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

_DOCUMENT = RelPath("docs/development/BENCHMARKS.md")
_SCHEMA = RelPath("benchmarks/SCHEMA.yaml")
_RESIDENCY_TEST = RelPath("python/tests/test_streaming_residency.py")

_BENCHMARKS = Prose(
    """# Benchmarks

## Canonical Results

Per-binding throughput, the committed baseline set.
No lane's standard deviation exceeds 2.0% of its mean.

| Benchmark | C++ (fps) | Python (fps) |
|---|---:|---:|
| Lane A | 200,000 | 100,000 |
| Lane B | 50,000 | 25,000 |

Per-frame C++ latency has a median of 3.2 µs and a mean of 3.6 µs.
The Python suite fails a session of 100,000 frames whose peak resident set grows by 32 MiB.

## Local baselines

`benchmarks/results/<binding>_<mode>_baseline.json`, one per binding and mode.
Each file's `system` object records the runtime that measured it.
A throughput baseline is 10 runs of 10,000 frames per lane,
a latency baseline 10,000 timed operations per lane, and a scaling baseline the full sweep.
A fresh report also records its `parameters` object; the committed files carry neither.

## Profiling

Nothing measured here.
"""
)

_SCHEMA_TEXT = Prose(
    """envelope:
  languages: [python, cpp]
  benchmarks: [throughput, latency, scaling]
experiment:
  trace_sizes:
    full: [1000, 5000, 10000]
    quick: [1000, 5000]
"""
)

_RESIDENCY_TEXT = Prose(
    """from typing import Final

_MAX_GROWTH_KIB: Final = 32 * 1024

_CASES: Final = [
    ("empty-message", 150_000),
    ("three-signals", 100_000),
]
"""
)

_SYSTEMS = {
    Prose("cpp"): {"cpu": "x86_64", "cores": 4, "platform": "Linux", "build_type": "Release"},
    Prose("python"): {"cpu": "x86_64", "cores": 4, "platform": "Linux", "python": "3.14.5"},
}
_MEANS = {
    Prose("cpp"): {Prose("Lane A"): 200000.0, Prose("Lane B"): 50000.0},
    Prose("python"): {Prose("Lane A"): 100000.0, Prose("Lane B"): 25000.0},
}


def _throughput(language: Prose) -> Prose:
    """Write a throughput baseline whose worst lane spreads by exactly the stated bound."""
    rows = [
        {"name": lane, "frames": 10000, "runs": 10, "fps_mean": mean, "fps_stdev": mean / 50}
        for lane, mean in _MEANS[language].items()
    ]
    body = {
        "benchmark": "throughput",
        "language": language,
        "system": _SYSTEMS[language],
        "results": rows,
    }
    return Prose(json.dumps(body, indent=1))


def _latency(language: Prose) -> Prose:
    """Write a latency baseline carrying the streaming lane the document quotes."""
    row = {"name": "CAN 2.0B Streaming LTL", "count": 10000, "mean_us": 3.6, "p50_us": 3.2}
    body = {
        "benchmark": "latency",
        "language": language,
        "system": _SYSTEMS[language],
        "results": [row],
    }
    return Prose(json.dumps(body, indent=1))


def _scaling(language: Prose) -> Prose:
    """Write a scaling baseline whose sweeps run the schema's full trace-size list."""
    sweep = [{"trace_size": size} for size in (1000, 5000, 10000)]
    body = {
        "benchmark": "scaling",
        "language": language,
        "system": _SYSTEMS[language],
        "results": {"trace_size_can20": sweep, "trace_size_canfd": sweep},
    }
    return Prose(json.dumps(body, indent=1))


def _baseline(language: Prose, mode: Prose) -> RelPath:
    """Name the committed path of one binding's baseline in one mode."""
    return RelPath(f"benchmarks/results/{language}_{mode}_baseline.json")


_FILES: dict[RelPath, Prose] = {
    _DOCUMENT: _BENCHMARKS,
    _SCHEMA: _SCHEMA_TEXT,
    _RESIDENCY_TEST: _RESIDENCY_TEXT,
    **{_baseline(language, Prose("throughput")): _throughput(language) for language in _MEANS},
    **{_baseline(language, Prose("latency")): _latency(language) for language in _MEANS},
    **{_baseline(language, Prose("scaling")): _scaling(language) for language in _MEANS},
}


def _edited(
    rel: RelPath, old: Prose, new: Prose, files: Mapping[RelPath, Prose] = _FILES
) -> dict[RelPath, Prose]:
    """Return ``files`` (the fixture by default) with one file changed at a phrase it does carry."""
    edited = dict(files)
    assert old in edited[rel], f"{rel} does not carry {old!r}"
    edited[rel] = Prose(edited[rel].replace(old, new))
    return edited


def _without(rel: RelPath) -> dict[RelPath, Prose]:
    """Return the fixture less one file."""
    files = dict(_FILES)
    del files[rel]
    return files


def _recorded(*, compiler: bool) -> dict[RelPath, Prose]:
    """Return the fixture with no lack sentence, every baseline carrying ``parameters``.

    With ``compiler``, each C++ baseline's ``system`` names its compiler as well.
    """
    files = _edited(_DOCUMENT, Prose("; the committed files carry neither"), Prose(""))
    for rel in [rel for rel in files if rel.endswith("_baseline.json")]:
        assert '"system": {' in files[rel], f"{rel} has no system object"
        text = files[rel].replace('"system": {', '"parameters": {"runs": 10},\n "system": {')
        if compiler:
            text = text.replace(
                '"build_type": "Release"', '"build_type": "Release", "compiler": "c"'
            )
        files[rel] = Prose(text)
    return files


def _recording(stated: Prose, key: Prose, value: Prose) -> dict[RelPath, Prose]:
    """Return the fixture stating ``stated``, every Python baseline recording ``value`` as ``key``.

    The arm reads a runtime's release from every baseline's ``system`` object, so the
    Python baselines can carry the recording of any runtime.
    """
    files = _edited(
        _DOCUMENT, Prose("records the runtime that"), Prose(f"records {stated}, the runtime that")
    )
    for mode in (Prose("throughput"), Prose("latency"), Prose("scaling")):
        files = _edited(
            _baseline(Prose("python"), mode),
            Prose('"python": "3.14.5"'),
            Prose(f"{json.dumps(key)}: {json.dumps(value)}"),
            files,
        )
    return files


def _findings(tmp_path: Path, files: Mapping[RelPath, Prose]) -> list[Prose]:
    """Plant ``files`` in a fresh tree and run the arm over it."""
    return run_planted(findings, plant(tmp_path / "repo", files))


def test_clean_fixture_has_no_finding(tmp_path: Path) -> None:
    """A document agreeing with every source returns nothing."""
    assert _findings(tmp_path, _FILES) == []


@pytest.mark.parametrize(
    "files",
    [
        pytest.param(
            _edited(_RESIDENCY_TEST, Prose("32 * 1024"), Prose("31 * 1024 + 1024")),
            id="budget-as-a-sum",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.14, the runtime that"),
            ),
            id="toolchain-release",
        ),
        pytest.param(_recorded(compiler=True), id="files-record-both"),
        pytest.param(
            _recording(Prose("Python 3.14"), Prose("python"), Prose("r3 3.14.5")),
            id="toolchain-release-after-a-lone-number",
        ),
        pytest.param(
            _recording(Prose("Python 13.1"), Prose("python"), Prose("13.1.2")),
            id="toolchain-release-two-digit-major",
        ),
        pytest.param(
            _recording(Prose("Python 3.14.5"), Prose("python"), Prose("3.14.5")),
            id="toolchain-release-in-full",
        ),
        pytest.param(
            _recording(Prose("Go 1.20"), Prose("go"), Prose("go1.20")),
            id="toolchain-release-of-two-parts",
        ),
        pytest.param(
            _recording(Prose("Python 3.14"), Prose("python"), Prose("r3-3.14.5")),
            id="toolchain-release-after-a-dash",
        ),
        pytest.param(
            _recording(Prose("Go 1.26"), Prose("go"), Prose("go1.26.3")),
            id="toolchain-release-prefixed",
        ),
        pytest.param(
            _recording(
                Prose("rustc 1.97"), Prose("rust"), Prose("rustc 1.97.1 (8bab26f4f 2026-07-14)")
            ),
            id="toolchain-release-named",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("Nothing measured here.\n"),
                Prose("Nothing measured here.\n\n```text\nPython 3.13.0\n```\n"),
            ),
            id="toolchain-version-in-a-fence",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("records the runtime that"),
                Prose("records `Python 3.13`, the runtime that"),
            ),
            id="toolchain-version-in-inline-code",
        ),
    ],
)
def test_agreeing_respelling_has_no_finding(tmp_path: Path, files: Mapping[RelPath, Prose]) -> None:
    """A source spelled another way that still agrees with the document returns nothing."""
    assert _findings(tmp_path, files) == []


def test_each_stated_version_is_reported_once_in_the_order_stated(tmp_path: Path) -> None:
    """A version the prose states twice is one finding, and the findings follow the prose."""
    files = _edited(
        _DOCUMENT,
        Prose("records the runtime that"),
        Prose("records Python 3.13, then Python 3.12 and Python 3.13 again, the runtime that"),
    )
    found = [text for text in map(str, _findings(tmp_path, files)) if "states Python" in text]
    assert found == [
        f"{_DOCUMENT}: states Python 3.13; the baselines record ['3.14.5']",
        f"{_DOCUMENT}: states Python 3.12; the baselines record ['3.14.5']",
    ]


@pytest.mark.parametrize(
    ("files", "expected"),
    [
        pytest.param(
            _edited(_DOCUMENT, Prose("| Lane A | 200,000 |"), Prose("| Lane A | 210,000 |")),
            "Lane A, cpp: the table says 210,000, the baseline 200,000",
            id="table-cell",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("exceeds 2.0% of"), Prose("exceeds 5.1% of")),
            "claims at most 5.1%, the baselines' worst is 2.0%",
            id="spread-bound",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("| Lane B | 50,000 | 25,000 |\n"), Prose("")),
            "the baselines carry a lane the table omits: 'Lane B'",
            id="lane-omitted",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("| Lane B |"), Prose("| Lane C |")),
            "the table has a lane the baselines do not: 'Lane C'",
            id="lane-invented",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("| C++ (fps) |"), Prose("| Zig (fps) |")),
            "the table has a column no binding answers to: 'Zig'",
            id="column-unknown",
        ),
        pytest.param(
            _edited(
                _DOCUMENT, Prose("is 10 runs of 10,000 frames"), Prose("is 5 runs of 10,000 frames")
            ),
            "Lane A is 10 runs of 10000 frames, the section says 5 of 10000",
            id="throughput-count",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("is 10 runs of"), Prose("is 0 runs of")),
            "the section states the throughput run count of 0",
            id="zero-count",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("baseline 10,000 timed"), Prose("baseline 5,000 timed")),
            "counts 10000 operations, the section says 5000",
            id="latency-count",
        ),
        pytest.param(
            _edited(
                _SCHEMA,
                Prose("full: [1000, 5000, 10000]"),
                Prose("full: [1000, 5000, 10000, 50000]"),
            ),
            "trace_size_can20 has 3 sizes, the full sweep has 4",
            id="scaling-sweep",
        ),
        pytest.param(
            _without(_baseline(Prose("python"), Prose("scaling"))),
            "benchmarks/results/python_scaling_baseline.json is not a committed baseline",
            id="baseline-missing",
        ),
        pytest.param(
            _edited(_baseline(Prose("cpp"), Prose("latency")), Prose('"cpp"'), Prose('"go"')),
            "cpp_latency_baseline.json says go latency",
            id="baseline-mislabelled",
        ),
        pytest.param(
            _edited(
                _baseline(Prose("cpp"), Prose("latency")),
                Prose('"benchmark": "latency"'),
                Prose('"benchmark": "throughput"'),
            ),
            "cpp_latency_baseline.json says cpp throughput",
            id="baseline-mode-mislabelled",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("median of 3.2 µs"), Prose("median of 3.1 µs")),
            "the median reads 3.1 µs, the committed baseline holds 3.2 µs",
            id="latency-median",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("grows by 32 MiB"), Prose("grows by 64 MiB")),
            "states a 64 MiB budget, the test asserts 32 MiB",
            id="residency-budget",
        ),
        pytest.param(
            _edited(
                _DOCUMENT, Prose("session of 100,000 frames"), Prose("session of 10,000 frames")
            ),
            "names a session of 10,000 frames, the test runs [100000, 150000]",
            id="residency-frames",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.13, the runtime that"),
            ),
            "states Python 3.13; the baselines record ['3.14.5']",
            id="toolchain-version",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 4.5, the runtime that"),
            ),
            "states Python 4.5; the baselines record ['3.14.5']",
            id="toolchain-version-inside-the-recorded",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.1, the runtime that"),
            ),
            "states Python 3.1; the baselines record ['3.14.5']",
            id="toolchain-version-prefix-of-the-recorded",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.14 and Python 3.13, the runtime that"),
            ),
            "states Python 3.13; the baselines record ['3.14.5']",
            id="toolchain-version-stated-second",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Go 1.26, the runtime that"),
            ),
            "states Go 1.26; the baselines record []",
            id="toolchain-version-unrecorded",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("records the runtime that"),
                Prose("records Python 3.14, the runtime that"),
                _edited(
                    _baseline(Prose("python"), Prose("latency")),
                    Prose('"python": "3.14.5"'),
                    Prose('"python": "unknown"'),
                ),
            ),
            "states Python 3.14; the baselines record ['3.14.5', 'unknown']",
            id="toolchain-version-unnumbered",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("`system` object"), Prose("system entry")),
            "does not name the system object",
            id="system-object-unnamed",
        ),
        pytest.param(
            _edited(
                _baseline(Prose("python"), Prose("scaling")),
                Prose('"benchmark": "scaling",'),
                Prose('"benchmark": "scaling", "parameters": {"runs": 5},'),
            ),
            "python_scaling_baseline.json records what the section says the committed files lack",
            id="lack-sentence-stale",
        ),
        pytest.param(
            _edited(
                _baseline(Prose("cpp"), Prose("latency")),
                Prose('"build_type": "Release"'),
                Prose('"build_type": "Release", "compiler": "c"'),
            ),
            "cpp_latency_baseline.json records what the section says the committed files lack",
            id="lack-sentence-stale-compiler",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("; the committed files carry neither"), Prose("")),
            "cpp_latency_baseline.json lacks its parameters or its compiler, and the section"
            + " no longer says so",
            id="lack-sentence-missing",
        ),
        pytest.param(
            _recorded(compiler=False),
            "cpp_latency_baseline.json lacks its parameters or its compiler, and the section"
            + " no longer says so",
            id="lack-sentence-missing-compiler",
        ),
    ],
)
def test_planted_disagreement_is_found(
    tmp_path: Path, files: Mapping[RelPath, Prose], expected: Prose
) -> None:
    """Each planted disagreement between the document and a source yields a finding naming it."""
    found = [str(finding) for finding in _findings(tmp_path, files)]
    assert any(expected in finding for finding in found), found
    assert all(finding.startswith(f"{_DOCUMENT}: ") for finding in found)


@pytest.mark.parametrize(
    ("files", "expected"),
    [
        pytest.param(
            _without(_DOCUMENT),
            "not among the tracked documents",
            id="document-untracked",
        ),
        pytest.param(
            {rel: text for rel, text in _FILES.items() if "_baseline.json" not in rel},
            "no committed baseline under benchmarks/results/",
            id="no-baseline",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("## Canonical Results"), Prose("## Results")),
            "has no Canonical Results section",
            id="no-canonical-section",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("| Benchmark |"), Prose("| Lane |")),
            "the canonical table has no header row",
            id="no-table-header",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("| Benchmark |"), Prose("## Elsewhere\n\n| Benchmark |")),
            "the canonical table has no header row",
            id="table-past-the-section",
        ),
        pytest.param(
            _edited(
                _baseline(Prose("cpp"), Prose("throughput")),
                Prose('"fps_mean": 200000.0,'),
                Prose('"mean_fps": 200000.0,'),
            ),
            "cpp_throughput_baseline.json: a row has no mean and spread",
            id="row-without-mean",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("standard deviation exceeds"), Prose("spread stays under")),
            "no longer states a standard-deviation bound",
            id="no-bound",
        ),
        pytest.param(
            _edited(_DOCUMENT, Prose("## Local baselines"), Prose("## Baselines")),
            "has no Local baselines section",
            id="no-local-section",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("A throughput baseline is 10 runs of"),
                Prose("Each lane ran 10 times over"),
            ),
            "no longer states the throughput run count",
            id="no-count-phrase",
        ),
        pytest.param(
            _without(_SCHEMA),
            "benchmarks/SCHEMA.yaml is not tracked",
            id="no-schema",
        ),
        pytest.param(
            _edited(
                _DOCUMENT,
                Prose("median of 3.2 µs and a mean of 3.6 µs"),
                Prose("a few microseconds"),
            ),
            "no longer states a per-frame median and mean",
            id="no-latency-phrase",
        ),
        pytest.param(
            _edited(_RESIDENCY_TEST, Prose("_MAX_GROWTH_KIB"), Prose("_BUDGET_KIB")),
            "test_streaming_residency.py no longer names its budget and its cases",
            id="no-residency-constants",
        ),
        pytest.param(
            _edited(_RESIDENCY_TEST, Prose("_CASES"), Prose("_SHAPES")),
            "test_streaming_residency.py no longer names its budget and its cases",
            id="no-residency-cases",
        ),
        pytest.param(
            _edited(_RESIDENCY_TEST, Prose("32 * 1024"), Prose("0")),
            "test_streaming_residency.py no longer names its budget and its cases",
            id="residency-budget-zero",
        ),
    ],
)
def test_nothing_to_compare_is_a_finding(
    tmp_path: Path, files: Mapping[RelPath, Prose], expected: Prose
) -> None:
    """A fixture the arm cannot compare, a phrase or a file gone, is reported rather than passed."""
    found = [str(finding) for finding in _findings(tmp_path, files)]
    assert any(expected in finding for finding in found), found
