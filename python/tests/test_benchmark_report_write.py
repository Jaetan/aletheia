# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The benchmark modes' report on stdout, the run that cannot write it, and a stray argument.

The report is everything a mode writes to stdout: its text tables, or the JSON
report under ``--json``, encoded and buffered as stdout is, after what stdout
already held.  A report stdout refuses, at whichever write first reaches the
system, fails the run with status 1 and a stderr line naming the report and the
system's reason, and stdout is left closed, so the interpreter's exit flush has
nothing to write and the status stays 1.  An error that is not the report's, a
file load's, passes through, and leaves stdout closed when stdout refused the
report too.  Each mode runs in process with stdout on ``/dev/full``, buffered
each way ``_full_stdout`` names, and with its measurements replaced: the
suite's clock stands still, and a rate over no elapsed time is undefined.  A
positional argument, which neither a mode nor the stability harness takes, is
refused with status 2 before anything loads a DBC or opens a client.
"""

from __future__ import annotations

import errno
import os
import platform
import sys
import tempfile
from typing import TYPE_CHECKING, Final, Literal, NamedTuple, Never, NewType

import pytest
from _canonical_dbc import make_dbc
from _full_stdout import (
    BUFFERING_IDS,
    BUFFERINGS,
    BY_BLOCKS,
    BY_SHORT_BLOCKS,
    NO_SPACE,
    Buffering,
    full_stdout,
)
from _processes import CommandWord

from aletheia.common_types import AllocatedBytes, ExitStatus, Prose
from benchmarks import (
    _common,
    latency,
    scaling,
    simplification,
    stability,
    throughput,
    violations,
)

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path
    from types import ModuleType

    from aletheia.checks import CheckResult
    from aletheia.types import DBCDefinition, LTLFormula

# A streaming pass's rate, as the scaling sweeps average it.
FramesPerSecond = NewType("FramesPerSecond", float)
# A path as a harness hands it to a loader, the name of one of violations' frame
# generators, and how many violations a pass found.
PathText = NewType("PathText", str)
FrameGenerator = NewType("FrameGenerator", str)
ViolationCount = NewType("ViolationCount", int)

_JSON_FLAGS: Final = [[], [CommandWord("--json")]]
_JSON_IDS: Final = ["text", "json"]


def _refusal(mode: _common.BenchmarkMode) -> Prose:
    """Answer the stderr line a run ends on when ``/dev/full`` refused its ``mode`` report."""
    return Prose(f"benchmark: writing the {mode} report failed: {NO_SPACE}")


def _print_report() -> None:
    """Write a report of one line, as a mode does."""
    sys.stdout.write("the report\n")


def test_a_report_stdout_takes_is_written_after_what_stdout_held(tmp_path: Path) -> None:
    """The report follows what stdout held, stdout stays open, and the status is 0."""
    report = tmp_path / "report.txt"
    with report.open("w", encoding="utf-8") as out, pytest.MonkeyPatch.context() as patch:
        patch.setattr(sys, "stdout", out)
        sys.stdout.write("before the run\n")
        assert _common.run_mode("throughput", _print_report) == 0
        assert sys.stdout is out
        assert not out.closed
        assert report.read_text(encoding="utf-8") == "before the run\nthe report\n"


def test_the_report_is_encoded_and_buffered_as_stdout_is(tmp_path: Path) -> None:
    """A line reaches a line-buffered stdout as it is written, encoded as stdout encodes.

    Stdout here encodes ASCII and replaces what it cannot encode, and the report
    names itself as stdout does.
    """
    report = tmp_path / "report.txt"

    def write_a_line() -> None:
        sys.stdout.write("caf\u00e9\n")
        assert report.read_bytes() == b"caf?\n"
        assert sys.stdout.name == str(report)

    with (
        report.open("w", buffering=1, encoding="ascii", errors="replace") as out,
        pytest.MonkeyPatch.context() as patch,
    ):
        patch.setattr(sys, "stdout", out)
        assert _common.run_mode("throughput", write_a_line) == 0


def test_bytes_written_to_the_buffer_of_stdout_are_the_report_too(tmp_path: Path) -> None:
    """A write to stdout's buffer reaches stdout and answers how many bytes it took."""
    report = tmp_path / "report.bin"

    def write_bytes() -> None:
        assert sys.stdout.buffer.write(b"raw\n") == len(b"raw\n")

    with report.open("w", encoding="utf-8") as out, pytest.MonkeyPatch.context() as patch:
        patch.setattr(sys, "stdout", out)
        assert _common.run_mode("throughput", write_bytes) == 0
    assert report.read_bytes() == b"raw\n"


@pytest.mark.parametrize("buffering", BUFFERINGS, ids=BUFFERING_IDS)
def test_a_report_stdout_refuses_fails_the_run_and_closes_stdout(buffering: Buffering) -> None:
    """A refused report is named on stderr with the reason, and stdout is closed with status 1."""
    with full_stdout(buffering) as streams:
        assert _common.run_mode("latency", _print_report) == 1
        assert sys.stdout is streams.out
        assert streams.out.closed
    assert streams.err.getvalue() == f"{_refusal('latency')}\n"


def _report_then_missing_file() -> None:
    """Write a line of the report, then fail to open a file, as a load that finds none does."""
    sys.stdout.write("the report so far\n")
    raise FileNotFoundError(errno.ENOENT, os.strerror(errno.ENOENT), "absent.dbc")


def test_an_error_that_is_not_the_reports_passes_through(tmp_path: Path) -> None:
    """A file load's ``OSError`` leaves the run as it was raised, the report so far written."""
    report = tmp_path / "report.txt"
    with report.open("w", encoding="utf-8") as out, pytest.MonkeyPatch.context() as patch:
        patch.setattr(sys, "stdout", out)
        with pytest.raises(FileNotFoundError, match=r"absent\.dbc"):
            _common.run_mode("scaling", _report_then_missing_file)
        assert sys.stdout is out
        assert not out.closed
    assert report.read_text(encoding="utf-8") == "the report so far\n"


@pytest.mark.parametrize(
    "buffering", [BY_BLOCKS, BY_SHORT_BLOCKS], ids=["by blocks", "by short blocks"]
)
def test_an_error_that_is_not_the_reports_passes_through_a_refused_report(
    buffering: Buffering,
) -> None:
    """A file load's ``OSError`` leaves the run as raised, though stdout refused the report too.

    Stdout is left closed, so the bytes it refused are not left in its buffer
    for the interpreter's exit flush to fail on, which would turn the status
    into 120.  Stdout buffered by lines refuses the report's first line, before
    the load is reached, so that run is a refused report alone.
    """
    with full_stdout(buffering) as streams:
        with pytest.raises(FileNotFoundError, match=r"absent\.dbc"):
            _common.run_mode("scaling", _report_then_missing_file)
        assert streams.out.closed


# A name a program's module binds that would load the kernel: a DBC loader, the
# client, or the backend.
Loader = Literal["load_dbc", "load_canfd_dbc", "dbc_to_json", "AletheiaClient", "FFIBackend"]


class _Entry(NamedTuple):
    """A program's ``main``, its module, and the names in it that would load the kernel."""

    main: Callable[[], ExitStatus]
    module: ModuleType
    loaders: list[Loader]


_ENTRIES: Final = [
    _Entry(throughput.main, throughput, ["load_dbc", "load_canfd_dbc", "AletheiaClient"]),
    _Entry(latency.main, latency, ["load_dbc", "load_canfd_dbc", "AletheiaClient"]),
    _Entry(scaling.main, scaling, ["load_dbc", "load_canfd_dbc", "AletheiaClient", "FFIBackend"]),
    _Entry(simplification.main, simplification, ["load_dbc", "AletheiaClient"]),
    _Entry(violations.main, violations, ["dbc_to_json", "AletheiaClient"]),
    _Entry(stability.main, stability, ["load_dbc", "AletheiaClient"]),
]
_ENTRY_IDS: Final = [entry.module.__name__.rpartition(".")[2] for entry in _ENTRIES]


def _kernel_must_not_load(*_args: DBCDefinition | PathText) -> Never:
    """Fail the test: the run reached the kernel."""
    pytest.fail("the run reached the kernel")


@pytest.mark.parametrize("entry", _ENTRIES, ids=_ENTRY_IDS)
def test_a_stray_argument_is_refused_before_the_kernel_loads(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], entry: _Entry
) -> None:
    """A positional argument exits 2 naming it on stderr, and nothing loads a DBC or a client."""
    for loader in entry.loaders:
        monkeypatch.setattr(entry.module, loader, _kernel_must_not_load)
    program = entry.module.__name__.rpartition(".")[2] + ".py"
    monkeypatch.setattr(sys, "argv", [CommandWord(f"benchmarks/{program}"), CommandWord("stray")])
    with pytest.raises(SystemExit) as exited:
        entry.main()
    assert exited.value.code == 2
    captured = capsys.readouterr()
    assert captured.err.splitlines()[-1] == f"{program}: error: unrecognized arguments: stray"
    assert not captured.out


def _no_benchmarks(*_dbcs: DBCDefinition) -> list[throughput.NamedBenchmark]:
    """Answer a throughput suite of no benchmark."""
    return []


def _no_lanes(_ctx: latency.LatencyContext) -> list[latency.NamedLatency]:
    """Answer a latency suite of no lane."""
    return []


def _fixed_rate(
    *_point: DBCDefinition | _common.FrameCount | _common.FrameSpec | list[LTLFormula],
) -> tuple[FramesPerSecond, scaling.Seconds]:
    """Answer one rate over one second, as a streaming pass does."""
    return FramesPerSecond(1000.0), scaling.Seconds(1.0)


def _fixed_load(_source: scaling.LoadSource) -> scaling.LoadCost:
    """Answer one second and one byte, as a DBC, DBC text or ``parseDBC`` command load does."""
    return scaling.LoadCost(scaling.Seconds(1.0), AllocatedBytes(1))


def _fixed_formula_rate(
    *_run: DBCDefinition | list[LTLFormula] | _common.FrameCount,
) -> FramesPerSecond:
    """Answer one rate, as a simplification pass does."""
    return FramesPerSecond(1000.0)


def _fixed_client_rate(
    *_run: DBCDefinition | list[CheckResult] | _common.FrameCount | FrameGenerator,
) -> FramesPerSecond:
    """Answer one rate, as a pass through the client does."""
    return FramesPerSecond(1000.0)


def _fixed_cli_rate(
    *_run: DBCDefinition | list[CheckResult] | PathText,
) -> tuple[FramesPerSecond, ViolationCount]:
    """Answer one rate and no violation, as a pass through ``run_checks`` does."""
    return FramesPerSecond(1000.0), ViolationCount(0)


def _canonical_dbc(_path: PathText) -> DBCDefinition:
    """Answer the canonical DBC, as the kernel would the file at ``_path``."""
    return make_dbc()


@pytest.fixture(autouse=True)
def _no_processor_probe(monkeypatch: pytest.MonkeyPatch) -> None:
    """Name the machine where a JSON report's system information would name the processor.

    ``platform`` asks ``uname -p`` for the processor, a process of its own.
    """
    monkeypatch.setattr(platform, "processor", platform.machine)


def _on_canonical_dbcs(monkeypatch: pytest.MonkeyPatch, module: ModuleType) -> None:
    """Give ``module`` the canonical DBC where it would have the kernel load the example DBCs."""
    monkeypatch.setattr(module, "load_dbc", make_dbc)
    monkeypatch.setattr(module, "load_canfd_dbc", make_dbc)


def _refused_run(
    monkeypatch: pytest.MonkeyPatch,
    mode: _common.BenchmarkMode,
    main: Callable[[], ExitStatus],
    words: list[CommandWord],
    buffering: Buffering,
) -> None:
    """Run ``mode``'s ``main`` on ``words`` with stdout refusing, and check the refusal."""
    monkeypatch.setattr(sys, "argv", [CommandWord(mode), *words])
    with full_stdout(buffering) as streams:
        assert main() == 1
        assert streams.out.closed
    assert streams.err.getvalue().splitlines()[-1] == _refusal(mode)


@pytest.mark.parametrize("buffering", BUFFERINGS, ids=BUFFERING_IDS)
@pytest.mark.parametrize("json_flag", _JSON_FLAGS, ids=_JSON_IDS)
def test_a_refused_throughput_report_fails_the_run(
    monkeypatch: pytest.MonkeyPatch, json_flag: list[CommandWord], buffering: Buffering
) -> None:
    """Throughput's report, tables or JSON, refused by stdout fails the run with status 1."""
    _on_canonical_dbcs(monkeypatch, throughput)
    monkeypatch.setattr(throughput, "_build_benchmarks", _no_benchmarks)
    words = ["--frames", "1", "--runs", "1", "--warmup", "0"]
    _refused_run(
        monkeypatch,
        "throughput",
        throughput.main,
        [*map(CommandWord, words), *json_flag],
        buffering,
    )


@pytest.mark.parametrize("buffering", BUFFERINGS, ids=BUFFERING_IDS)
@pytest.mark.parametrize("json_flag", _JSON_FLAGS, ids=_JSON_IDS)
def test_a_refused_latency_report_fails_the_run(
    monkeypatch: pytest.MonkeyPatch, json_flag: list[CommandWord], buffering: Buffering
) -> None:
    """Latency's report, tables or JSON, refused by stdout fails the run with status 1."""
    _on_canonical_dbcs(monkeypatch, latency)
    monkeypatch.setattr(latency, "run_latency_suite", _no_lanes)
    words = ["--ops", "1", "--warmup", "0"]
    _refused_run(
        monkeypatch, "latency", latency.main, [*map(CommandWord, words), *json_flag], buffering
    )


@pytest.mark.parametrize("buffering", BUFFERINGS, ids=BUFFERING_IDS)
@pytest.mark.parametrize("json_flag", _JSON_FLAGS, ids=_JSON_IDS)
def test_a_refused_scaling_report_fails_the_run(
    monkeypatch: pytest.MonkeyPatch, json_flag: list[CommandWord], buffering: Buffering
) -> None:
    """Scaling's report, tables or JSON, refused by stdout fails the run with status 1.

    Every load, the raw ``parseDBC`` command's included, is answered by the
    stub, and the client and the backend fail the test if a load reaches them.
    """
    _on_canonical_dbcs(monkeypatch, scaling)
    monkeypatch.setattr(scaling, "run_streaming_benchmark", _fixed_rate)
    monkeypatch.setattr(scaling, "_load_cost", _fixed_load)
    monkeypatch.setattr(scaling, "AletheiaClient", _kernel_must_not_load)
    monkeypatch.setattr(scaling, "FFIBackend", _kernel_must_not_load)
    words = ["--quick", "--runs", "1"]
    _refused_run(
        monkeypatch, "scaling", scaling.main, [*map(CommandWord, words), *json_flag], buffering
    )


@pytest.mark.parametrize("buffering", BUFFERINGS, ids=BUFFERING_IDS)
@pytest.mark.parametrize("json_flag", _JSON_FLAGS, ids=_JSON_IDS)
def test_a_refused_simplification_report_fails_the_run(
    monkeypatch: pytest.MonkeyPatch, json_flag: list[CommandWord], buffering: Buffering
) -> None:
    """Simplification's report, tables or JSON, refused by stdout fails the run with status 1."""
    monkeypatch.setattr(simplification, "load_dbc", make_dbc)
    monkeypatch.setattr(simplification, "bench_formula", _fixed_formula_rate)
    words = [CommandWord("--quick"), *json_flag]
    _refused_run(monkeypatch, "simplification", simplification.main, words, buffering)


@pytest.mark.parametrize("buffering", BUFFERINGS, ids=BUFFERING_IDS)
def test_a_refused_violations_report_fails_the_run(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, buffering: Buffering
) -> None:
    """Violations' report, its tables, refused by stdout fails the run with status 1.

    The logs its ``run_checks`` layer reads are written under the test's own directory.
    """
    monkeypatch.setattr(violations, "dbc_to_json", _canonical_dbc)
    monkeypatch.setattr(violations, "bench_client", _fixed_client_rate)
    monkeypatch.setattr(violations, "bench_cli", _fixed_cli_rate)
    monkeypatch.setattr(tempfile, "tempdir", str(tmp_path))
    words = [CommandWord(w) for w in ("--frames", "1", "--runs", "1")]
    _refused_run(monkeypatch, "violations", violations.main, words, buffering)
