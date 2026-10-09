# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The planted tree the stated-measurements arm's tests run over, and the edits made to it.

A reduced BENCHMARKS.md, schema, baseline set and residency test that agree;
each builder below returns that tree with one source or sentence changed.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING

from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.stated_measurements import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Collection, Mapping, Sequence
    from pathlib import Path

    from tools.docs_arms.stated_measurements import Spread

    from aletheia.common_types import PositiveInt


DOCUMENT = RelPath("docs/development/BENCHMARKS.md")
SCHEMA = RelPath("benchmarks/SCHEMA.yaml")
RESIDENCY_TEST = RelPath("python/tests/test_streaming_residency.py")
CPP = Prose("cpp")
PYTHON = Prose("python")
THROUGHPUT = Prose("throughput")
LATENCY = Prose("latency")
SCALING = Prose("scaling")
LACK = Prose("lacks its parameters or its compiler, and the section no longer says so")

BENCHMARKS = Prose(
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

SCHEMA_TEXT = Prose(
    """envelope:
  languages: [python, cpp]
  benchmarks: [throughput, latency, scaling]
experiment:
  trace_sizes:
    full: [1000, 5000, 10000]
    quick: [1000, 5000]
"""
)

RESIDENCY_TEXT = Prose(
    """from typing import Final

_MAX_GROWTH_KIB: Final = 32 * 1024

_CASES: Final = [
    ("empty-message", 150_000),
    ("three-signals", 100_000),
]
"""
)

SYSTEMS = {
    CPP: {"cpu": "x86_64", "cores": 4, "platform": "Linux", "build_type": "Release"},
    PYTHON: {"cpu": "x86_64", "cores": 4, "platform": "Linux", "python": "3.14.5"},
}
MEANS = {
    CPP: {Prose("Lane A"): 200000.0, Prose("Lane B"): 50000.0},
    PYTHON: {Prose("Lane A"): 100000.0, Prose("Lane B"): 25000.0},
}
# Python's Lane B spreads by 2.0% of its mean, every other row by 1.0%.
STDEVS = {
    CPP: {Prose("Lane A"): 2000.0, Prose("Lane B"): 500.0},
    PYTHON: {Prose("Lane A"): 1000.0, Prose("Lane B"): 500.0},
}
# Every row spreads by 0.5% of its mean.
HALF_PERCENT = {
    CPP: {Prose("Lane A"): 1000.0, Prose("Lane B"): 250.0},
    PYTHON: {Prose("Lane A"): 500.0, Prose("Lane B"): 125.0},
}
SIZES: tuple[PositiveInt, ...] = (1000, 5000, 10000)


def throughput(language: Prose, stdevs: Mapping[Prose, Mapping[Prose, Spread]]) -> Prose:
    """Write a throughput baseline whose rows spread by ``stdevs``."""
    rows = [
        {
            "name": lane,
            "frames": 10000,
            "runs": 10,
            "fps_mean": mean,
            "fps_stdev": stdevs[language][lane],
        }
        for lane, mean in MEANS[language].items()
    ]
    body = {
        "benchmark": "throughput",
        "language": language,
        "system": SYSTEMS[language],
        "results": rows,
    }
    return Prose(json.dumps(body, indent=1))


def latency(language: Prose) -> Prose:
    """Write a latency baseline carrying the streaming lane the document quotes."""
    row = {"name": "CAN 2.0B Streaming LTL", "count": 10000, "mean_us": 3.6, "p50_us": 3.2}
    body = {
        "benchmark": "latency",
        "language": language,
        "system": SYSTEMS[language],
        "results": [row],
    }
    return Prose(json.dumps(body, indent=1))


def scaling(language: Prose, canfd: tuple[PositiveInt, ...] = SIZES) -> Prose:
    """Write a scaling baseline whose sweeps run the full size list, or ``canfd`` for CAN-FD."""
    body = {
        "benchmark": "scaling",
        "language": language,
        "system": SYSTEMS[language],
        "results": {
            "trace_size_can20": [{"trace_size": size} for size in SIZES],
            "trace_size_canfd": [{"trace_size": size} for size in canfd],
        },
    }
    return Prose(json.dumps(body, indent=1))


def baseline(language: Prose, mode: Prose) -> RelPath:
    """Name the committed path of one binding's baseline in one mode."""
    return RelPath(f"benchmarks/results/{language}_{mode}_baseline.json")


FILES: dict[RelPath, Prose] = {
    DOCUMENT: BENCHMARKS,
    SCHEMA: SCHEMA_TEXT,
    RESIDENCY_TEST: RESIDENCY_TEXT,
    **{baseline(language, THROUGHPUT): throughput(language, STDEVS) for language in MEANS},
    **{baseline(language, LATENCY): latency(language) for language in MEANS},
    **{baseline(language, SCALING): scaling(language) for language in MEANS},
}


def edited_files(
    rel: RelPath, old: Prose, new: Prose, files: Mapping[RelPath, Prose] = FILES
) -> dict[RelPath, Prose]:
    """Return ``files`` (the fixture by default) with one file changed at a phrase it does carry."""
    edited = dict(files)
    assert old in edited[rel], f"{rel} does not carry {old!r}"
    edited[rel] = Prose(edited[rel].replace(old, new))
    return edited


def without(rel: RelPath) -> dict[RelPath, Prose]:
    """Return the fixture less one file."""
    files = dict(FILES)
    del files[rel]
    return files


def recorded(*, compiler: bool) -> dict[RelPath, Prose]:
    """Return the fixture with no lack sentence, every baseline carrying ``parameters``.

    With ``compiler``, each C++ baseline's ``system`` names its compiler as well.
    """
    files = edited_files(DOCUMENT, Prose("; the committed files carry neither"), Prose(""))
    for rel in [rel for rel in files if rel.endswith("_baseline.json")]:
        assert '"system": {' in files[rel], f"{rel} has no system object"
        text = files[rel].replace('"system": {', '"parameters": {"runs": 10},\n "system": {')
        if compiler:
            text = text.replace(
                '"build_type": "Release"', '"build_type": "Release", "compiler": "c"'
            )
        files[rel] = Prose(text)
    return files


def recording(stated: Prose, key: Prose, value: Prose) -> dict[RelPath, Prose]:
    """Return the fixture stating ``stated``, every Python baseline recording ``value`` as ``key``.

    The arm reads a runtime's release from every baseline's ``system`` object, so the
    Python baselines can carry the recording of any runtime.
    """
    files = edited_files(
        DOCUMENT, Prose("records the runtime that"), Prose(f"records {stated}, the runtime that")
    )
    for mode in (THROUGHPUT, LATENCY, SCALING):
        files = edited_files(
            baseline(PYTHON, mode),
            Prose('"python": "3.14.5"'),
            Prose(f"{json.dumps(key)}: {json.dumps(value)}"),
            files,
        )
    return files


def spread(stdev: Prose, bound: Prose) -> dict[RelPath, Prose]:
    """Return the fixture spreading Python's Lane B by ``stdev``, the document stating ``bound``."""
    return edited_files(
        baseline(PYTHON, THROUGHPUT),
        Prose('"fps_stdev": 500.0'),
        Prose(f'"fps_stdev": {stdev}'),
        edited_files(DOCUMENT, Prose("exceeds 2.0% of"), Prose(f"exceeds {bound}% of")),
    )


def spreading(stdevs: Mapping[Prose, Mapping[Prose, Spread]], bound: Prose) -> dict[RelPath, Prose]:
    """Return the fixture with its throughput rows spreading by ``stdevs``, its bound ``bound``."""
    files = edited_files(DOCUMENT, Prose("exceeds 2.0% of"), Prose(f"exceeds {bound}% of"))
    files.update(
        {baseline(language, THROUGHPUT): throughput(language, stdevs) for language in MEANS}
    )
    return files


def spread_about(stdev: Prose, bound: Prose, mean: Prose, cell: Prose) -> dict[RelPath, Prose]:
    """Return ``_spread(stdev, bound)`` with Python's Lane B about ``mean``, printed as ``cell``."""
    return edited_files(
        baseline(PYTHON, THROUGHPUT),
        Prose('"fps_mean": 25000.0'),
        Prose(f'"fps_mean": {mean}'),
        edited_files(DOCUMENT, Prose("| 25,000 |"), Prose(f"| {cell} |"), spread(stdev, bound)),
    )


def planted_findings(
    tmp_path: Path, files: Mapping[RelPath, Prose], untracked: Collection[RelPath] = ()
) -> list[Prose]:
    """Plant ``files`` in a fresh tree and run the arm over it, ``untracked`` left untracked."""
    return run_planted(findings, plant(tmp_path / "repo", files), untracked=untracked)


def reported(expected: Sequence[Prose]) -> list[Prose]:
    """Return the findings ``expected`` as the arm reports them, each naming the document."""
    return [Prose(f"{DOCUMENT}: {body}") for body in expected]
