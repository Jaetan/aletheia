# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Count the instructions one operation of each throughput lane costs, in every binding.

Each binding's throughput harness runs one lane at a time (``--lane K``, one
run, no warmup) under valgrind's cachegrind, once at ``FRAMES_LOW`` frames and
once at ``FRAMES_HIGH``.  The difference of the two instruction totals over
the difference of the frame counts is the lane's instructions per operation:
the process's start, the kernel's load and the lane's own setup are in both
totals and cancel.  Every Python run compiles its modules afresh, so neither
total reads bytecode the other wrote, and every run turns the GHC runtime's
idle-time collector off, so no total rests on how long the process idled.

A count barely moves with the machine's speed or load: measured on one host,
a Python lane repeats to within two instructions in 283,716 and a Go lane to
within about 60 per operation, and three runs of one tree on three runner
classes spread the widest lane, Go's CAN-FD signal extraction, by 1.76%.  The
report records the toolchain the counts rest on, so
``tools/benchmark_gate.py --bench instructions`` can refuse a comparison
across toolchains by name.

Writes ``benchmarks/results/instructions.json``: the toolchain, the host it
ran on (recorded, never compared), and ``{binding: {lane: instructions}}``.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

import yaml

from tools._common import COUNTED_RTS_OPTS, ExecutorFactory, WorkerCount, shim_ghc
from tools._progress import ItemCount, counted, reporting
from tools._resources import cpu_budget
from tools.check_bench_schema import REPO, SCHEMA_PATH, Binding, bindings, lib_env

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence

# A count of instructions valgrind reports, and one operation's share of it.
InstructionCount = NewType("InstructionCount", int)
# A throughput lane's name as benchmarks/SCHEMA.yaml spells it, and its
# number, counted from 1 in that order.
LaneName = NewType("LaneName", str)
LaneNumber = NewType("LaneNumber", int)
# A binding as the schema names it.
BindingName = NewType("BindingName", str)
# How many frames one counted run drives through its lane.
FrameCount = NewType("FrameCount", int)
# A tool whose build the counts rest on, and the version it reports.
ToolName = NewType("ToolName", str)
ToolVersion = NewType("ToolVersion", str)
# One word of a command line, and the text a run left.
CommandWord = NewType("CommandWord", str)
RunText = NewType("RunText", str)

# The two frame counts each lane runs at.  Their difference divides the two
# totals' difference, so a run's fixed cost cancels and its per-run noise is
# shared by every operation of the difference.
FRAMES_LOW = FrameCount(100)
FRAMES_HIGH = FrameCount(1100)

VALGRIND = (
    CommandWord("valgrind"),
    CommandWord("--tool=cachegrind"),
    CommandWord("--cache-sim=no"),
    CommandWord("--cachegrind-out-file=/dev/null"),
)

# The total valgrind prints at a run's end, in its own log.
_TOTAL = re.compile(r"^==\d+== I\s+refs:\s+([\d,]+)$", re.MULTILINE)

RESULT_PATH = REPO / "benchmarks" / "results" / "instructions.json"


class _ThroughputSchema(TypedDict):
    lane_names: list[LaneName]


class _Modes(TypedDict):
    throughput: _ThroughputSchema


class _Schema(TypedDict):
    modes: _Modes


class CountedRun(NamedTuple):
    """One process valgrind counts: a binding's lane at one frame count."""

    binding: Binding
    lane: LaneNumber
    frames: FrameCount


class InstructionReport(TypedDict):
    """The report this tool writes and the gate reads."""

    toolchain: dict[ToolName, ToolVersion]
    host: dict[ToolName, ToolVersion]
    frames: list[FrameCount]
    counts: dict[BindingName, dict[LaneName, InstructionCount]]


class CountError(Exception):
    """A counted run that ended badly or reported no total."""


def lane_names() -> list[LaneName]:
    """Return the throughput lanes in the order the schema lists them."""
    schema = cast("_Schema", yaml.safe_load(SCHEMA_PATH.read_text(encoding="utf-8")))
    names = schema["modes"]["throughput"]["lane_names"]
    if not names:
        message = f"{SCHEMA_PATH} lists no throughput lane names"
        raise CountError(message)
    return names


def run_argv(run: CountedRun) -> list[CommandWord]:
    """Return the command that counts one run: valgrind around the harness, one lane, one pass."""
    binding = run.binding
    harness = (
        [CommandWord(str(binding.exe)), CommandWord("-m"), CommandWord("benchmarks.throughput")]
        if binding.python_module
        else [CommandWord(str(binding.exe)), CommandWord("throughput")]
    )
    flags = ("--frames", str(run.frames), "--runs", "1", "--warmup", "0", "--lane", str(run.lane))
    return [*VALGRIND, *harness, *map(CommandWord, flags)]


def parse_total(log: RunText) -> InstructionCount:
    """Return the instruction total a valgrind log ends with, refusing a log without one."""
    totals = _TOTAL.findall(log)
    if len(totals) != 1:
        message = f"valgrind's log holds {len(totals)} instruction totals, not one"
        raise CountError(message)
    return InstructionCount(int(totals[0].replace(",", "")))


def count_run(run: CountedRun) -> InstructionCount:
    """Run one counted process and return the instructions valgrind counted in it."""
    with tempfile.TemporaryDirectory(prefix="aletheia-count-") as scratch:
        log = Path(scratch) / "valgrind.log"
        env = {
            **lib_env(),
            "ALETHEIA_RTS_OPTS": COUNTED_RTS_OPTS,
            "PYTHONHASHSEED": "0",
            "PYTHONPYCACHEPREFIX": str(Path(scratch) / "pycache"),
        }
        valgrind, *rest = run_argv(run)
        done = subprocess.run(
            [valgrind, f"--log-file={log}", *rest],
            cwd=run.binding.cwd,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        if done.returncode != 0:
            message = (
                f"{run.binding.name} lane {run.lane} at {run.frames} frames exited "
                f"{done.returncode}: {done.stderr.strip()[-500:]}"
            )
            raise CountError(message)
        return parse_total(RunText(log.read_text(encoding="utf-8")))


def per_operation(low: InstructionCount, high: InstructionCount) -> InstructionCount:
    """Return one operation's instructions: the totals' difference over the frames' difference."""
    if high <= low:
        message = (
            f"{FRAMES_HIGH} frames counted {high} instructions, "
            f"not more than {FRAMES_LOW} frames' {low}"
        )
        raise CountError(message)
    return InstructionCount((high - low) // (FRAMES_HIGH - FRAMES_LOW))


def count_lanes(
    targets: Sequence[Binding],
    lanes: Sequence[LaneName],
    *,
    count: Callable[[CountedRun], InstructionCount] = count_run,
    executor: ExecutorFactory = ThreadPoolExecutor,
    workers: WorkerCount | None = None,
) -> dict[BindingName, dict[LaneName, InstructionCount]]:
    """Count every lane of every binding at both frame counts, on ``workers`` runs at once."""
    runs = [
        CountedRun(binding, LaneNumber(number), frames)
        for binding in targets
        for number in range(1, len(lanes) + 1)
        for frames in (FRAMES_LOW, FRAMES_HIGH)
    ]
    with executor(workers or WorkerCount(cpu_budget())) as pool:
        futures = [pool.submit(count, run) for run in runs]
        arriving = counted(
            zip(runs, futures, strict=True), ItemCount(len(runs)), Prose("lane runs counted")
        )
        totals = {run: future.result() for run, future in arriving}
    return {
        BindingName(binding.name): {
            lane: per_operation(
                totals[CountedRun(binding, LaneNumber(number), FRAMES_LOW)],
                totals[CountedRun(binding, LaneNumber(number), FRAMES_HIGH)],
            )
            for number, lane in enumerate(lanes, start=1)
        }
        for binding in targets
    }


def _first_line(argv: Sequence[CommandWord]) -> ToolVersion:
    """Return the first line a version command prints."""
    done = subprocess.run(argv, cwd=REPO, capture_output=True, text=True, check=True)
    return ToolVersion((done.stdout or done.stderr).strip().splitlines()[0])


def _cxx_compiler() -> CommandWord:
    """Return the C++ compiler cpp/build was configured with."""
    cache = (REPO / "cpp" / "build" / "CMakeCache.txt").read_text(encoding="utf-8")
    found = re.search(r"^CMAKE_CXX_COMPILER:\w+=(.+)$", cache, re.MULTILINE)
    if found is None:
        message = "cpp/build/CMakeCache.txt names no C++ compiler"
        raise CountError(message)
    return CommandWord(found.group(1))


def toolchain(targets: Sequence[Binding]) -> dict[ToolName, ToolVersion]:
    """Return the version of every tool the counts rest on: a different one counts differently."""
    python = next(binding for binding in targets if binding.python_module)
    words = (
        CommandWord(str(python.exe)),
        CommandWord("-c"),
        CommandWord("import sys; print(sys.version)"),
    )
    return {
        ToolName("python"): _first_line(words),
        ToolName("ghc"): _first_line((CommandWord(shim_ghc()), CommandWord("--numeric-version"))),
        ToolName("c++"): _first_line((_cxx_compiler(), CommandWord("--version"))),
        ToolName("go"): _first_line(
            (CommandWord("go"), CommandWord("env"), CommandWord("GOVERSION"))
        ),
        ToolName("rustc"): _first_line((CommandWord("rustc"), CommandWord("--version"))),
        ToolName("valgrind"): _first_line((CommandWord("valgrind"), CommandWord("--version"))),
        ToolName("glibc"): ToolVersion(os.confstr("CS_GNU_LIBC_VERSION") or "unknown"),
    }


def host() -> dict[ToolName, ToolVersion]:
    """Return the CPU the counts ran on, recorded beside them and compared with nothing."""
    cpuinfo = Path("/proc/cpuinfo").read_text(encoding="utf-8")
    model = re.search(r"^model name\s*:\s*(.+)$", cpuinfo, re.MULTILINE)
    return {ToolName("cpu"): ToolVersion(model.group(1) if model else "unknown")}


def report(
    targets: Sequence[Binding],
    counts: Mapping[BindingName, dict[LaneName, InstructionCount]],
) -> InstructionReport:
    """Return the report of one counting run."""
    return {
        "toolchain": toolchain(targets),
        "host": host(),
        "frames": [FRAMES_LOW, FRAMES_HIGH],
        "counts": dict(counts),
    }


def main() -> ExitStatus:
    """Count every lane of every built binding and write the report."""
    parser = argparse.ArgumentParser(description="Count each throughput lane's instructions")
    _ = parser.add_argument("--out", type=Path, default=RESULT_PATH, help="Report path")
    out = cast("Path", parser.parse_args().out)
    targets = bindings(built=True)
    missing = [binding.name for binding in targets if not binding.available]
    if missing:
        _ = sys.stderr.write(f"benchmark-instructions: not built: {', '.join(missing)}\n")
        return ExitStatus(1)
    try:
        counts = count_lanes(targets, lane_names())
        written = report(targets, counts)
    except (CountError, subprocess.CalledProcessError) as exc:
        _ = sys.stderr.write(f"benchmark-instructions: {exc}\n")
        return ExitStatus(1)
    out.parent.mkdir(parents=True, exist_ok=True)
    _ = out.write_text(json.dumps(written, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    for binding, lanes in counts.items():
        for lane, instructions in lanes.items():
            _ = sys.stdout.write(f"  {binding:7s} {lane:32s} {instructions:>12,}\n")
    _ = sys.stdout.write(f"benchmark-instructions: wrote {out}\n")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(reporting(main, Prose("instruction counts")))
