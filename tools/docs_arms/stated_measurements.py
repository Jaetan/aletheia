# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every measurement docs/development/BENCHMARKS.md states is what its sources record.

The document states numbers a reader takes as current: the canonical throughput
table and the standard-deviation bound beside it, the per-frame latency figures,
the residency budget and the counts a fresh run must reproduce. Each is read out
of the document and compared with its source: the committed baseline set under
``benchmarks/results/``, the envelope ``benchmarks/SCHEMA.yaml`` pins and the
constants of the residency test. A phrase carrying one of them that the document
no longer carries is a finding too, so a reword cannot pass by taking the number
with it, and so is a baseline set or a table with nothing in it to compare. The
sentence on what the committed files lack is held to the files both ways, and a
Go, Python or rustc version stated outside code to the release every baseline's
``system`` object records for that runtime, an object the document must name.
"""

from __future__ import annotations

import ast
import json
import re
from typing import TYPE_CHECKING, Annotated, NamedTuple, NotRequired, TypedDict, cast

import yaml

from tools._common import RelPath, prose_lines

from aletheia.common_types import Gt, PositiveInt, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

_DOCUMENT = RelPath("docs/development/BENCHMARKS.md")
_SCHEMA = RelPath("benchmarks/SCHEMA.yaml")
_RESIDENCY_TEST = RelPath("python/tests/test_streaming_residency.py")
_LATENCY_BASELINE = RelPath("benchmarks/results/cpp_latency_baseline.json")
_LATENCY_LANE = Prose("CAN 2.0B Streaming LTL")
_BASELINE = re.compile(r"^benchmarks/results/(\w+?)_(\w+)_baseline\.json$")
_PATTERN = Prose("`benchmarks/results/<binding>_<mode>_baseline.json`")
_LACKING = Prose("the committed files carry neither")
_SYSTEM = Prose("`system` object")
_CANONICAL_NAME = Prose("Canonical Results")
_CANONICAL = Prose(f"## {_CANONICAL_NAME}")
_LOCAL_NAME = Prose("Local baselines")
_LOCAL = Prose(f"## {_LOCAL_NAME}")
_LATENCY_FIGURES = re.compile(r"median of ([\d.]+) µs and a mean of ([\d.]+) µs")
_RESIDENCY_SENTENCE = re.compile(
    r"a session of ([\d,]+) frames whose peak resident set grows by (\d+) MiB"
)
_SPREAD_BOUND = re.compile(r"standard deviation exceeds ([\d.]+)% of its mean")
_VERSION = re.compile(r"\d+(?:\.\d+)+")

# The table's column titles, less their unit, and the binding each names.
_COLUMNS: dict[Prose, Prose] = {
    Prose("C++"): Prose("cpp"),
    Prose("Rust"): Prose("rust"),
    Prose("Go"): Prose("go"),
    Prose("Python"): Prose("python"),
}

# A rate, a duration and a budget are above zero; a spread is zero or more, and
# the marker names a strict lower bound, so its bound sits below zero.
Rate = Annotated[float, Gt(0)]
Spread = Annotated[float, Gt(-1)]
Micros = Annotated[float, Gt(0)]
Mebibytes = Annotated[float, Gt(0)]


class _ThroughputRow(TypedDict):
    """One lane of a throughput baseline, the fields read here."""

    name: Prose
    frames: PositiveInt
    runs: PositiveInt
    fps_mean: Rate
    fps_stdev: Spread


class _LatencyRow(TypedDict):
    """One lane of a latency baseline, the fields read here."""

    name: Prose
    count: PositiveInt
    mean_us: Micros
    p50_us: Micros


class _ScalingPoint(TypedDict):
    """One point of a scaling sweep; only the sweep's length is read."""


class _ScalingSweeps(TypedDict):
    """The trace-size sweeps of a scaling baseline."""

    trace_size_can20: list[_ScalingPoint]
    trace_size_canfd: list[_ScalingPoint]


class _System(TypedDict, total=False):
    """What a baseline's ``system`` object records of its toolchain."""

    python: Prose
    go: Prose
    rust: Prose
    compiler: Prose


class _Parameters(TypedDict):
    """The flags a report's run read; only its presence is read here."""


class _Baseline(TypedDict):
    """A committed baseline file, the fields read here."""

    language: Prose
    benchmark: Prose
    system: _System
    parameters: NotRequired[_Parameters]
    results: list[_ThroughputRow] | list[_LatencyRow] | _ScalingSweeps


class _Envelope(TypedDict):
    """The bindings and modes the schema's envelope lists."""

    languages: list[Prose]
    benchmarks: list[Prose]


class _TraceSizes(TypedDict):
    """The scaling suite's trace-size sweeps."""

    full: list[PositiveInt]


class _Experiment(TypedDict):
    """The experiment the schema pins, the part read here."""

    trace_sizes: _TraceSizes


class _Schema(TypedDict):
    """``benchmarks/SCHEMA.yaml``, the parts read here."""

    envelope: _Envelope
    experiment: _Experiment


class _Counts(NamedTuple):
    """The counts a baseline row must record.

    ``runs``, ``frames`` and ``operations`` are the Local baselines section's, None where
    its phrase is gone; ``sweep`` is the length of the schema's full trace-size list.
    """

    runs: PositiveInt | None
    frames: PositiveInt | None
    operations: PositiveInt | None
    sweep: PositiveInt


class _Residency(NamedTuple):
    """What the residency test asserts: its budget and the frame counts it runs."""

    budget_mib: Mebibytes
    frame_counts: frozenset[PositiveInt]


Lanes = dict[Prose, dict[Prose, _ThroughputRow]]


def _section(doc: Prose, heading: Prose) -> Prose | None:
    """Return the section ``heading`` opens, up to the next level-two heading; None when absent."""
    lines = doc.splitlines()
    if heading not in lines:
        return None
    body: list[Prose] = []
    for line in lines[lines.index(heading) + 1 :]:
        if line.startswith("## "):
            break
        body.append(Prose(line))
    return Prose("\n".join(body))


def _baselines(root: Path, tracked: frozenset[RelPath]) -> dict[RelPath, _Baseline]:
    """Load every committed baseline the tracked set names, keyed by its path."""
    loaded: dict[RelPath, _Baseline] = {}
    for rel in sorted(tracked):
        if _BASELINE.match(rel):
            loaded[rel] = cast("_Baseline", json.loads((root / rel).read_text(encoding="utf-8")))
    return loaded


def _throughput_lanes(baselines: dict[RelPath, _Baseline]) -> tuple[Lanes, list[Prose]]:
    """Index the throughput baselines' rows by lane and binding, naming a row missing its mean."""
    lanes: Lanes = {}
    out: list[Prose] = []
    for rel, data in baselines.items():
        match = _BASELINE.match(rel)
        if match is None or match.group(2) != "throughput":
            continue
        for row in cast("list[_ThroughputRow]", data["results"]):
            if "fps_mean" not in row or "fps_stdev" not in row:
                out.append(Prose(f"{rel}: a row has no mean and spread to compare the table with"))
            else:
                lanes.setdefault(row["name"], {})[data["language"]] = row
    return lanes, out


def _table_rows(section: Prose) -> list[Prose]:
    """Return the lines of ``section`` that are rows of a table, the header among them."""
    return [Prose(line) for line in section.splitlines() if line.startswith("| ")]


def _canonical_table(doc: Prose, baselines: dict[RelPath, _Baseline]) -> list[Prose]:
    """Hold every cell, the lane roster and the spread bound of the canonical table."""
    section = _section(doc, _CANONICAL)
    if section is None:
        return [Prose(f"has no {_CANONICAL_NAME} section")]
    lanes, out = _throughput_lanes(baselines)
    if not lanes:
        out.append(
            Prose("no committed throughput baseline carries a lane to compare the table with")
        )
        return out
    rows = _table_rows(section)
    header = next((line for line in rows if line.startswith("| Benchmark ")), None)
    if header is None:
        out.append(Prose("the canonical table has no header row opening on Benchmark"))
        return out
    bindings: list[Prose | None] = []
    for cell in header.strip().strip("|").split("|")[1:]:
        title = Prose(cell.strip().removesuffix(" (fps)"))
        if title not in _COLUMNS:
            out.append(Prose(f"the table has a column no binding answers to: {title!r}"))
        bindings.append(_COLUMNS.get(title))
    seen: set[Prose] = set()
    for line in rows:
        if line is header:
            continue
        cells = [Prose(cell.strip()) for cell in line.strip().strip("|").split("|")]
        lane, printed = cells[0], cells[1:]
        if lane not in lanes:
            out.append(Prose(f"the table has a lane the baselines do not: {lane!r}"))
            continue
        seen.add(lane)
        if len(printed) != len(bindings):
            out.append(Prose(f"{lane}: {len(printed)} cells under {len(bindings)} columns"))
            continue
        out.extend(_cell_findings(lane, lanes[lane], bindings, printed))
    out.extend(
        Prose(f"the baselines carry a lane the table omits: {lane!r}")
        for lane in lanes
        if lane not in seen
    )
    out.extend(_bound_findings(section, lanes))
    return out


def _cell_findings(
    lane: Prose,
    held: dict[Prose, _ThroughputRow],
    bindings: Sequence[Prose | None],
    printed: Sequence[Prose],
) -> list[Prose]:
    """Compare one table row's cells with the lane's mean in each binding's baseline."""
    out: list[Prose] = []
    for binding, cell in zip(bindings, printed, strict=True):
        if binding is None:
            continue
        row = held.get(binding)
        if row is None:
            out.append(Prose(f"{lane}, {binding}: no committed throughput baseline has the lane"))
        elif cell != f"{row['fps_mean']:,.0f}":
            want = f"{row['fps_mean']:,.0f}"
            out.append(Prose(f"{lane}, {binding}: the table says {cell}, the baseline {want}"))
    return out


def _bound_findings(section: Prose, lanes: Lanes) -> list[Prose]:
    """Compare the stated standard-deviation bound with the baselines' worst lane."""
    match = _SPREAD_BOUND.search(section)
    if match is None:
        return [Prose("the section no longer states a standard-deviation bound")]
    claimed = float(match.group(1))
    worst_lane, worst = max(
        (
            (Prose(f"{lane} {binding}"), 100 * row["fps_stdev"] / row["fps_mean"])
            for lane, held in lanes.items()
            for binding, row in held.items()
        ),
        key=lambda pair: pair[1],
    )
    if round(worst, 1) != claimed:
        return [
            Prose(f"claims at most {claimed}%, the baselines' worst is {worst:.1f}% ({worst_lane})")
        ]
    return []


def _stated(section: Prose, pattern: Prose, what: Prose, out: list[Prose]) -> PositiveInt | None:
    """Read a count the section states, or record that the phrase carrying it is gone."""
    match = re.search(pattern, section)
    if match is None:
        out.append(Prose(f"the section no longer states {what}"))
        return None
    value = int(match.group(1).replace(",", ""))
    if value <= 0:
        out.append(Prose(f"the section states {what} of {value}"))
        return None
    count: PositiveInt = value
    return count


def _stated_counts(section: Prose, schema: _Schema, out: list[Prose]) -> _Counts:
    """Read the counts the section states, and the full sweep's length from the schema."""
    runs = _stated(
        section,
        Prose(r"throughput baseline is ([\d,]+) runs of"),
        Prose("the throughput run count"),
        out,
    )
    frames = _stated(
        section,
        Prose(r"throughput baseline is [\d,]+ runs of ([\d,]+) frames"),
        Prose("the throughput frame count"),
        out,
    )
    operations = _stated(
        section,
        Prose(r"latency baseline ([\d,]+) timed operations"),
        Prose("the latency operation count"),
        out,
    )
    sweep: PositiveInt = len(schema["experiment"]["trace_sizes"]["full"])
    return _Counts(runs, frames, operations, sweep)


def _row_findings(rel: RelPath, data: _Baseline, mode: Prose, counts: _Counts) -> list[Prose]:
    """Compare every row of one baseline with the counts its mode must record."""
    out: list[Prose] = []
    if mode == "throughput" and counts.runs is not None and counts.frames is not None:
        out.extend(
            Prose(
                f"{rel}: {row['name']} is {row['runs']} runs of {row['frames']} frames,"
                + f" the section says {counts.runs} of {counts.frames}"
            )
            for row in cast("list[_ThroughputRow]", data["results"])
            if (row["frames"], row["runs"]) != (counts.frames, counts.runs)
        )
    elif mode == "latency" and counts.operations is not None:
        out.extend(
            Prose(
                f"{rel}: {row['name']} counts {row['count']} operations,"
                + f" the section says {counts.operations}"
            )
            for row in cast("list[_LatencyRow]", data["results"])
            if row["count"] != counts.operations
        )
    elif mode == "scaling":
        sweeps = cast("_ScalingSweeps", data["results"])
        lengths = (
            (Prose("trace_size_can20"), len(sweeps["trace_size_can20"])),
            (Prose("trace_size_canfd"), len(sweeps["trace_size_canfd"])),
        )
        out.extend(
            Prose(f"{rel}: {sweep} has {n} sizes, the full sweep has {counts.sweep}")
            for sweep, n in lengths
            if n != counts.sweep
        )
    return out


def _roster_findings(
    section: Prose, baselines: dict[RelPath, _Baseline], schema: _Schema
) -> list[Prose]:
    """Hold each binding and mode the envelope lists to its baseline, and its rows to the counts.

    Only the envelope's pairs are looked up, so a committed baseline outside it is no finding.
    """
    out: list[Prose] = []
    if _PATTERN not in section:
        out.append(Prose("the section does not name the baseline files by their pattern"))
    counts = _stated_counts(section, schema, out)
    for language in schema["envelope"]["languages"]:
        for mode in schema["envelope"]["benchmarks"]:
            rel = RelPath(f"benchmarks/results/{language}_{mode}_baseline.json")
            data = baselines.get(rel)
            if data is None:
                out.append(Prose(f"{rel} is not a committed baseline"))
            elif data["language"] != language or data["benchmark"] != mode:
                out.append(Prose(f"{rel} says {data['language']} {data['benchmark']}"))
            else:
                out.extend(_row_findings(rel, data, mode, counts))
    return out


def _lacking_findings(section: Prose, baselines: dict[RelPath, _Baseline]) -> list[Prose]:
    """Hold the sentence on what the committed files lack to the files, in both directions."""
    says_lacking = _LACKING in section
    out: list[Prose] = []
    for rel, data in baselines.items():
        has_parameters = "parameters" in data
        names_compiler = "compiler" in data["system"]
        complete = has_parameters and (data["language"] != "cpp" or names_compiler)
        if says_lacking and (has_parameters or names_compiler):
            out.append(Prose(f"{rel} records what the section says the committed files lack"))
        if not says_lacking and not complete:
            out.append(
                Prose(
                    f"{rel} lacks its parameters or its compiler, and the section no longer says so"
                )
            )
    return out


def _int_value(node: ast.expr) -> PositiveInt | None:
    """Fold a positive integer spelled as literals, products and sums; None for any other."""
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and node.value > 0:
        value: PositiveInt = node.value
        return value
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Mult, ast.Add)):
        left, right = _int_value(node.left), _int_value(node.right)
        if left is not None and right is not None:
            folded: PositiveInt = left * right if isinstance(node.op, ast.Mult) else left + right
            return folded
    return None


def _residency(root: Path, tracked: frozenset[RelPath]) -> _Residency | None:
    """Read the residency test's budget and frame counts from its source; None when gone."""
    if _RESIDENCY_TEST not in tracked:
        return None
    module = ast.parse((root / _RESIDENCY_TEST).read_text(encoding="utf-8"))
    named: dict[Prose, ast.expr] = {}
    for node in ast.walk(module):
        if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.value:
            named[Prose(node.target.id)] = node.value
    budget, cases = named.get(Prose("_MAX_GROWTH_KIB")), named.get(Prose("_CASES"))
    budget_kib = _int_value(budget) if budget is not None else None
    if budget_kib is None or not isinstance(cases, ast.List):
        return None
    counts: set[PositiveInt] = set()
    for case in cases.elts:
        match case:
            case ast.Tuple(elts=[_, frames_node]):
                frames = _int_value(frames_node)
                if frames is not None:
                    counts.add(frames)
            case _:
                pass
    return _Residency(budget_kib / 1024, frozenset(counts))


def _latency_findings(doc: Prose, baselines: dict[RelPath, _Baseline]) -> list[Prose]:
    """Hold the per-frame median and mean to the streaming lane of the C++ latency baseline."""
    latency = baselines.get(_LATENCY_BASELINE)
    if latency is None:
        return [Prose(f"{_LATENCY_BASELINE} is not a committed baseline")]
    rows = cast("list[_LatencyRow]", latency["results"])
    row = next((r for r in rows if r["name"] == _LATENCY_LANE), None)
    if row is None:
        return [Prose(f"{_LATENCY_BASELINE} carries no {_LATENCY_LANE!r} lane")]
    match = _LATENCY_FIGURES.search(doc)
    if match is None:
        return [Prose("no longer states a per-frame median and mean")]
    figures = (
        (Prose("median"), match.group(1), row["p50_us"]),
        (Prose("mean"), match.group(2), row["mean_us"]),
    )
    return [
        Prose(f"the {what} reads {printed} µs, the committed baseline holds {held} µs")
        for what, printed, held in figures
        if float(printed) != held
    ]


def _residency_findings(doc: Prose, root: Path, tracked: frozenset[RelPath]) -> list[Prose]:
    """Hold the residency sentence's frame count and budget to the test that asserts them."""
    residency = _residency(root, tracked)
    if residency is None:
        return [Prose(f"{_RESIDENCY_TEST} no longer names its budget and its cases")]
    match = _RESIDENCY_SENTENCE.search(doc)
    if match is None:
        return [Prose("no longer states a residency budget over a frame count")]
    out: list[Prose] = []
    frames = int(match.group(1).replace(",", ""))
    if frames not in residency.frame_counts:
        runs = sorted(residency.frame_counts)
        out.append(Prose(f"names a session of {frames:,} frames, the test runs {runs}"))
    if float(match.group(2)) != residency.budget_mib:
        budget = f"{residency.budget_mib:.0f}"
        out.append(Prose(f"states a {match.group(2)} MiB budget, the test asserts {budget} MiB"))
    return out


def _same_release(stated: Prose, recorded: Prose) -> bool:
    """Whether the version ``recorded`` names opens on every component of ``stated``."""
    held = _VERSION.search(recorded)
    parts = stated.split(".")
    return held is not None and held.group().split(".")[: len(parts)] == parts


def _toolchain_findings(doc: Prose, baselines: dict[RelPath, _Baseline]) -> list[Prose]:
    """Hold each runtime version the prose states to the release every baseline records for it.

    A version stated twice is one finding; the findings follow the order the prose states them.
    """
    out: list[Prose] = []
    if _SYSTEM not in doc:
        out.append(Prose("does not name the system object as where the runtime versions are"))
    prose = "\n".join(line for _, line in prose_lines(_DOCUMENT, doc))
    systems = [data["system"] for data in baselines.values()]
    runtimes = (
        (Prose("Go"), r"\bGo (\d+\.\d+(?:\.\d+)?)", [s.get("go") for s in systems]),
        (Prose("Python"), r"\bPython (\d+\.\d+(?:\.\d+)?)", [s.get("python") for s in systems]),
        (Prose("rustc"), r"\brustc (\d+\.\d+(?:\.\d+)?)", [s.get("rust") for s in systems]),
    )
    for runtime, pattern, held in runtimes:
        recorded = sorted({version for version in held if version is not None})
        out.extend(
            Prose(f"states {runtime} {stated}; the baselines record {recorded}")
            for stated in map(Prose, dict.fromkeys(re.findall(pattern, prose)))
            if not recorded or not all(_same_release(stated, version) for version in recorded)
        )
    return out


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per measurement the document states that its sources do not hold.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Every tracked Markdown file's text, by its repo-relative path.

    Returns:
        The findings, each naming the document; empty when every stated measurement holds.

    """
    if _DOCUMENT not in documents:
        return [
            Prose(f"{_DOCUMENT}: not among the tracked documents, so nothing it states is checked")
        ]
    doc = documents[_DOCUMENT]
    tracked_set = frozenset(tracked)
    baselines = _baselines(root, tracked_set)
    if not baselines:
        return [
            Prose(f"{_DOCUMENT}: no committed baseline under benchmarks/results/ to compare with")
        ]
    what = _canonical_table(doc, baselines)
    local = _section(doc, _LOCAL)
    if local is None:
        what.append(Prose(f"has no {_LOCAL_NAME} section"))
    else:
        if _SCHEMA in tracked_set:
            schema = cast("_Schema", yaml.safe_load((root / _SCHEMA).read_text(encoding="utf-8")))
            what.extend(_roster_findings(local, baselines, schema))
        else:
            what.append(Prose(f"{_SCHEMA} is not tracked, so the baseline roster goes unchecked"))
        what.extend(_lacking_findings(local, baselines))
    what.extend(_latency_findings(doc, baselines))
    what.extend(_residency_findings(doc, root, tracked_set))
    what.extend(_toolchain_findings(doc, baselines))
    return [Prose(f"{_DOCUMENT}: {item}") for item in what]
