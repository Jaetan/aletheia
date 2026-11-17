# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``aletheia.start_runtime`` starts the kernel's runtime before any client.

The kernel reads every number a check carries, and its runtime starts once per
process.  A program starts it with ``start_runtime(cores)``, then loads checks
holding decimals and hands them to a client's constructor; a client or backend
naming no core count asks for the count running, one when nothing runs.  A
count outside one to the CPUs the process may use is refused, the bound being
the runtime's own count of them.

The tests in this process read the recording stand-in, which counts four CPUs
and whose runtime entry starts nothing and records the command line it is
handed, under a runtime latch of the test's own
(``unstarted``).  The claims about a process whose runtime has not started run
as programs of their own against the built library.  The command line's
builder is read as a table, with nothing loaded.
"""

from __future__ import annotations

import ctypes
import logging
import os
import sys
from fractions import Fraction
from typing import TYPE_CHECKING, NamedTuple, Never, NewType

import pytest
from _cli_check_helpers import FFI_LIB, dbc_text, never_exceeds_yaml, run_captured, skip_without_ffi
from _excel_helpers import (
    BRAKE_RESPONSE_WT_ROW,
    ENGINE_RPM_ROW,
    make_checks_workbook,
    make_dbc_workbook,
    make_when_then_workbook,
)
from _stand_in import StandInName, keeping, stand_in_kernel

from aletheia import (
    AletheiaClient,
    FFIBackend,
    FFIError,
    ProtocolError,
    RTSState,
    ValidationError,
    start_runtime,
)
from aletheia.checks import signal
from aletheia.client._enrichment import format_rational
from aletheia.client._ffi import RuntimeOverride, rts_arguments, take_error_envelope
from aletheia.common_types import CoreCount, Prose

if TYPE_CHECKING:
    from pathlib import Path

# A program run in a process of its own by this interpreter, and one word of its command line.
ProgramSource = NewType("ProgramSource", str)
ProgramArgument = NewType("ProgramArgument", str)

_IN_A_FRESH_RUNTIME = (
    "the GHC runtime starts once per process, so a claim about one no client has started"
    + " runs in a process of its own"
)

# EngineSpeed factor 0.25: raw 800 decodes to 200.0 rpm, over the 199.5 limit.
_SIGNAL = 'EngineSpeed : 0|16@1+ (0.25,0) [0|8000] "rpm"'


def _run(program: ProgramSource, *args: ProgramArgument) -> tuple[list[Prose], list[Prose]]:
    """Run ``program`` in a process of its own against the built library; answer its lines."""
    skip_without_ffi()
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(FFI_LIB)
    done = run_captured([sys.executable, "-c", program, *args], env, cwd=FFI_LIB.parent)
    assert done.returncode == 0, f"exit={done.returncode}\n{done.stdout}{done.stderr}"
    return [Prose(line) for line in done.stdout.splitlines()], [
        Prose(line) for line in done.stderr.splitlines()
    ]


_DEFAULT_CHECKS_AFTER_A_START = ProgramSource(
    """\
import sys
import aletheia
from aletheia import AletheiaClient, load_checks

print("count before:", aletheia.allocated_bytes())
aletheia.start_runtime(1)
print("count after:", type(aletheia.allocated_bytes()).__name__)
checks = load_checks(sys.argv[2])
with AletheiaClient(default_checks=checks) as client:
    client.parse_dbc_text(sys.argv[1])
    client.add_checks([])
    client.start_stream()
    reply = client.send_frame(1000, 0x100, 8, bytes([0x20, 0x03, 0, 0, 0, 0, 0, 0]))
    client.end_stream()
print("verdicts:", [entry["status"] for entry in reply["results"]])
"""
)


@pytest.mark.process(_IN_A_FRESH_RUNTIME)
def test_default_checks_holding_a_decimal_load_after_a_start_and_stream() -> None:
    """A program starts the runtime, loads a 199.5 limit, and its client's default check fails."""
    dbc = ProgramArgument(dbc_text(256, "EngineStatus", _SIGNAL))
    checks = ProgramArgument(never_exceeds_yaml("Speed limit", "EngineSpeed", "199.5", "critical"))
    out, _ = _run(_DEFAULT_CHECKS_AFTER_A_START, dbc, checks)
    assert out == ["count before: None", "count after: int", "verdicts: ['fails']"]


_REFUSED_BEFORE_A_START = ProgramSource(
    """\
from aletheia import AletheiaError, checks, from_decimal

def render():
    return checks.signal("S").never_exceeds(220).condition_desc

for read in (lambda: from_decimal("1.5"), render):
    try:
        read()
    except AletheiaError as refused:
        print(type(refused).__name__, refused)
"""
)


@pytest.mark.process(_IN_A_FRESH_RUNTIME)
def test_a_number_read_before_any_start_is_refused_naming_the_remedy() -> None:
    """Parsing a decimal and building a check before any start each name ``start_runtime``.

    The kernel checks a check as it is built, so its build is refused before
    its threshold could render.
    """
    out, _ = _run(_REFUSED_BEFORE_A_START)
    assert out == [
        "FFIError GHC runtime not initialized: call aletheia.start_runtime or open a client"
        + " before parsing decimals",
        "FFIError GHC runtime not initialized: call aletheia.start_runtime or open a client"
        + " before building a check",
    ]


_LOADS_BEFORE_A_START = ProgramSource(
    """\
import sys
from pathlib import Path
import aletheia
from aletheia import AletheiaError, load_checks, load_checks_from_excel, load_dbc_from_excel

text, when_then, file, checks, when_then_sheet, dbc = sys.argv[1:]
for load in (
    lambda: load_checks(text),
    lambda: load_checks(when_then),
    lambda: load_checks(Path(file)),
    lambda: load_checks_from_excel(checks),
    lambda: load_checks_from_excel(when_then_sheet),
    lambda: load_dbc_from_excel(dbc),
    lambda: load_checks("not: a checks list"),
    lambda: load_checks_from_excel("does-not-exist.xlsx"),
):
    try:
        load()
        print("loaded")
    except AletheiaError as refused:
        print(type(refused).__name__, refused.code, refused.location, refused.key, refused)
    except OSError as refused:
        print(type(refused).__name__, refused)
print("allocated:", aletheia.allocated_bytes())
"""
)


@pytest.mark.process(_IN_A_FRESH_RUNTIME)
def test_every_check_and_dbc_loader_raises_the_runtime_refusal_unlocated_before_any_start(
    tmp_path: Path,
) -> None:
    """A check or DBC loader reading a number before any start raises the parser's refusal.

    The refusal carries no code and no location, and the load starts nothing; a YAML
    when-then check reads its time bound first. A loader's own refusal of its input,
    a document holding no checks list or a workbook that does not exist, answers on
    that input.
    """
    document = never_exceeds_yaml("Speed limit", "EngineSpeed", "199.5", "critical")
    when_then = (
        "checks:\n  - name: w\n    when:\n      signal: Brake\n      condition: exceeds\n"
        + "      value: 50\n    then:\n      signal: Light\n      condition: equals\n"
        + "      value: 1\n    within_us: 100000\n"
    )
    file = tmp_path / "checks.yaml"
    _ = file.write_text(document, encoding="utf-8")
    checks = make_checks_workbook(
        tmp_path, [[None, "Speed", "never_exceeds", 220, None, None, None, None]], "checks.xlsx"
    )
    when_then_sheet = make_when_then_workbook(tmp_path, [BRAKE_RESPONSE_WT_ROW], "when_then.xlsx")
    dbc = make_dbc_workbook(tmp_path, [ENGINE_RPM_ROW], "dbc.xlsx")
    arguments = (document, when_then, str(file), str(checks), str(when_then_sheet), str(dbc))
    out, _ = _run(_LOADS_BEFORE_A_START, *(ProgramArgument(word) for word in arguments))
    refused = (
        "FFIError None None None GHC runtime not initialized: call aletheia.start_runtime or"
        + " open a client before parsing decimals"
    )
    refused_time = (
        "FFIError None None None GHC runtime not initialized: call aletheia.start_runtime or"
        + " open a client before reading a time bound"
    )
    assert out == [
        refused,
        refused_time,
        *[refused] * 4,
        "ValidationError None None None YAML must contain a 'checks' list",
        "FileNotFoundError Excel file not found: does-not-exist.xlsx",
        "allocated: None",
    ]


_A_COUNT_OF_ZERO = ProgramSource(
    """\
from aletheia import AletheiaClient, RTSState, ValidationError, start_runtime

for start in (lambda: start_runtime(0), lambda: AletheiaClient(rts_cores=0).__enter__()):
    try:
        start()
    except ValidationError as refused:
        print(refused)
print("started:", RTSState.initialized)
"""
)


@pytest.mark.process(_IN_A_FRESH_RUNTIME)
def test_a_count_of_zero_is_refused_before_the_runtime_starts() -> None:
    """Zero is outside the bound on every machine, from ``start_runtime`` and a client alike.

    The bound's own figure is the machine's; the stand-in tests below hold the
    text whole, on the four CPUs the recording stand-in counts.
    """
    out, _ = _run(_A_COUNT_OF_ZERO)
    *refusals, started = out
    assert started == "started: False"
    assert len(refusals) == 2
    for refusal in refusals:
        assert str(refusal).startswith("core count 0 is outside 1 to "), refusal
        assert str(refusal).endswith(", the CPUs this process may use"), refusal


_THE_RUNNING_COUNT = ProgramSource(
    """\
import logging
import aletheia
from aletheia import AletheiaClient, FFIBackend

logging.basicConfig(level=logging.WARNING, format="%(message)s")
aletheia.start_runtime(2)
aletheia.start_runtime(2)
print("a backend naming no count:", FFIBackend().rts_cores)
with AletheiaClient():
    pass
with AletheiaClient(rts_cores=1):
    pass
"""
)


@pytest.mark.process(_IN_A_FRESH_RUNTIME)
def test_a_client_naming_no_count_asks_the_running_one_and_another_count_is_warned() -> None:
    """After ``start_runtime(2)`` a count-less backend and client are silent; one asking 1 warns."""
    out, err = _run(_THE_RUNNING_COUNT)
    assert out == ["a backend naming no count: 2"]
    assert err == ["rts.cores_mismatch active_cores=2 requested_cores=1"]


# --- In this process, on the recording stand-in.

_RECORDING = StandInName("recording_kernel")
# The CPUs the recording stand-in counts.
_STAND_IN_CPUS = 4


def _mismatches(caplog: pytest.LogCaptureFixture) -> list[Prose]:
    """Return the ``rts.cores_mismatch`` lines the ``aletheia`` logger wrote, in order."""
    return [
        Prose(r.getMessage())
        for r in caplog.records
        if r.getMessage().startswith("rts.cores_mismatch")
    ]


# A logger's name, a record's level and the event it carries, as ``logging`` holds them.
LoggerName = NewType("LoggerName", str)
LogLevel = NewType("LogLevel", int)
EventName = NewType("EventName", str)


class _Record(NamedTuple):
    """A captured record with the fields an ``rts.cores_mismatch`` warning carries."""

    logger: LoggerName
    level: LogLevel
    line: Prose
    event: EventName | None
    active_cores: CoreCount | None
    requested_cores: CoreCount | None


def _records(caplog: pytest.LogCaptureFixture) -> list[_Record]:
    """Return every record the test captured, in order."""
    return [
        _Record(
            LoggerName(r.name),
            LogLevel(r.levelno),
            Prose(r.getMessage()),
            getattr(r, "event", None),
            getattr(r, "active_cores", None),
            getattr(r, "requested_cores", None),
        )
        for r in caplog.records
    ]


# The one record four asked of a runtime running on one writes.
_FOUR_ASKED_OF_ONE = [
    _Record(
        LoggerName("aletheia"),
        LogLevel(logging.WARNING),
        Prose(f"rts.cores_mismatch active_cores=1 requested_cores={_STAND_IN_CPUS}"),
        EventName("rts.cores_mismatch"),
        CoreCount(1),
        CoreCount(_STAND_IN_CPUS),
    )
]


# A word of the command line the runtime's start entry is handed, and their
# count, as the recording stand-in read them.
RuntimeArgument = NewType("RuntimeArgument", bytes)
ArgumentCount = NewType("ArgumentCount", int)
# The flags a caller appends to the runtime's own through the override variable.
RtsOptions = NewType("RtsOptions", str)

_RTS_OVERRIDE = "ALETHEIA_RTS_OPTS"


class _CommandLine(NamedTuple):
    """The override a start reads, and the command line its runtime entry is then handed."""

    override: RtsOptions | None
    words: list[RuntimeArgument]


_COMMAND_LINES = [
    _CommandLine(
        None, [RuntimeArgument(word) for word in (b"aletheia", b"+RTS", b"-M3G", b"-RTS")]
    ),
    _CommandLine(
        RtsOptions("  -M12M   -hT "),
        [
            RuntimeArgument(word)
            for word in (b"aletheia", b"+RTS", b"-M3G", b"-M12M", b"-hT", b"-RTS")
        ],
    ),
    # The environment holds the byte 0xff, which os.environ spells U+DCFF.
    _CommandLine(
        RtsOptions("-\udcff -é"),
        [
            RuntimeArgument(word)
            for word in (b"aletheia", b"+RTS", b"-M3G", b"-\xff", b"-\xc3\xa9", b"-RTS")
        ],
    ),
]


def _handed(lib: ctypes.CDLL) -> tuple[ArgumentCount, list[RuntimeArgument]]:
    """Return the count and the words the recording stand-in's runtime entry was last handed."""
    arguments = lib.aletheia_test_rts_arguments
    arguments.restype = ctypes.c_char_p
    words = [RuntimeArgument(word) for word in arguments().split(b"\n")]
    return ArgumentCount(lib.aletheia_test_rts_argc()), words


@pytest.mark.usefixtures("unstarted")
@pytest.mark.parametrize(
    "line", _COMMAND_LINES, ids=["no override", "an override", "an override outside UTF-8"]
)
def test_a_start_hands_the_runtime_its_name_then_its_heap_cap_then_the_override(
    line: _CommandLine, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A start on one core hands the runtime entry its name, its heap cap and the override.

    The words sit between ``+RTS`` and ``-RTS``, the cap before the override so
    a caller's own ``-M`` lands later and wins; the override is split on
    whitespace and its words handed as their bytes, and one core writes no ``-N``.
    """
    if line.override is None:
        monkeypatch.delenv(_RTS_OVERRIDE, raising=False)
    else:
        monkeypatch.setenv(_RTS_OVERRIDE, line.override)
    start_runtime(1, lib_path=stand_in_kernel(_RECORDING))
    assert RTSState.lib is not None
    assert _handed(RTSState.lib) == (ArgumentCount(len(line.words)), line.words)


@pytest.mark.usefixtures("unstarted")
def test_a_word_that_is_not_bytes_is_refused_before_the_runtime_starts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A command line holding something other than bytes raises before the runtime entry runs.

    The runtime reads every word it is handed, so a null in place of one would
    end the process; the start refuses it in Python instead.
    """
    lib = ctypes.CDLL(str(stand_in_kernel(_RECORDING)))
    before = _handed(lib)

    def with_a_null(_cores: CoreCount, _override: RuntimeOverride) -> list[RuntimeArgument | None]:
        return [*_OPENING, None, _CLOSING]

    monkeypatch.setattr("aletheia.client._ffi.rts_arguments", with_a_null)
    with pytest.raises(TypeError):
        start_runtime(1, lib_path=stand_in_kernel(_RECORDING))
    assert _handed(lib) == before


# The words every command line opens and closes on: the runtime's name, its
# heap cap and the closing marker.
_OPENING = [RuntimeArgument(word) for word in (b"aletheia", b"+RTS", b"-M3G")]
_CLOSING = RuntimeArgument(b"-RTS")


class _Built(NamedTuple):
    """A core count and an override, and the words the builder writes after the cap."""

    cores: CoreCount
    override: RuntimeOverride
    added: list[RuntimeArgument]


_BUILT = [
    _Built(CoreCount(1), RuntimeOverride(b""), []),
    _Built(CoreCount(4), RuntimeOverride(b""), [RuntimeArgument(b"-N4")]),
    _Built(
        CoreCount(1),
        RuntimeOverride(b"  -M12M   -hT "),
        [RuntimeArgument(b"-M12M"), RuntimeArgument(b"-hT")],
    ),
    _Built(
        CoreCount(2), RuntimeOverride(b"-hT"), [RuntimeArgument(b"-N2"), RuntimeArgument(b"-hT")]
    ),
]


@pytest.mark.parametrize(
    "built", _BUILT, ids=["one core", "four cores", "an override", "an override and two cores"]
)
def test_the_command_line_names_a_core_count_past_one_then_the_override(built: _Built) -> None:
    """The builder writes ``-N`` past one core, then the override's words, after the cap.

    It is read directly, as every binding's test reads its own; the override
    is split on ASCII whitespace.
    """
    assert rts_arguments(built.cores, built.override) == [*_OPENING, *built.added, _CLOSING]


# An argument's position in a call, counted from one as ctypes's refusal names it.
ArgumentPosition = NewType("ArgumentPosition", int)


class _Mistyped(NamedTuple):
    """The runtime entry's argument handed another type of its layout, and ctypes's refusal."""

    position: ArgumentPosition
    refusal: Prose


_MISTYPED = [
    _Mistyped(
        ArgumentPosition(1),
        Prose("argument 1: TypeError: expected LP_c_int instance instead of pointer to c_uint"),
    ),
    _Mistyped(
        ArgumentPosition(2),
        Prose(
            "argument 2: TypeError: expected LP_LP_c_char_p instance"
            + " instead of pointer to LP_c_void_p"
        ),
    ),
]


@pytest.mark.usefixtures("unstarted")
@pytest.mark.parametrize("mistyped", _MISTYPED, ids=["the count", "the list"])
def test_the_runtime_entry_refuses_an_argument_of_another_type_before_it_runs(
    mistyped: _Mistyped,
) -> None:
    """After a start, the runtime entry holds its count to ``int *`` and its list to ``char ***``.

    An ``unsigned`` count and a list of untyped addresses share the right
    ones' layout, so an entry declared looser would run on them; each is
    refused at the call, and the entry keeps the command line the start handed it.
    """
    start_runtime(1, lib_path=stand_in_kernel(_RECORDING))
    lib = RTSState.lib
    assert lib is not None
    started = _handed(lib)
    count = ctypes.byref(ctypes.c_int(0))
    words = ctypes.byref(ctypes.POINTER(ctypes.c_char_p)())
    if mistyped.position == 1:
        count = ctypes.byref(ctypes.c_uint(0))
    else:
        words = ctypes.byref(ctypes.POINTER(ctypes.c_void_p)())
    with pytest.raises(ctypes.ArgumentError) as refused:
        lib.hs_init_with_rtsopts(count, words)
    assert str(refused.value) == mistyped.refusal
    assert _handed(lib) == started


@pytest.mark.usefixtures("unstarted")
def test_a_backend_gives_back_the_reference_it_took_and_no_more() -> None:
    """A backend's close gives back the reference its open took, and a second close keeps none."""
    backend = FFIBackend(lib_path=stand_in_kernel(_RECORDING))
    assert RTSState.refcount == 1
    backend.close(0)
    assert RTSState.refcount == 0
    backend.close(0)
    assert RTSState.refcount == 0


@pytest.mark.usefixtures("unstarted")
def test_each_open_backend_holds_a_reference_of_its_own() -> None:
    """Two backends open at once hold two references, and each close gives back its own."""
    recording = stand_in_kernel(_RECORDING)
    first, second = FFIBackend(lib_path=recording), FFIBackend(lib_path=recording)
    assert RTSState.refcount == 2
    first.close(0)
    assert RTSState.refcount == 1
    second.close(0)
    assert RTSState.refcount == 0


@pytest.mark.usefixtures("unstarted")
def test_a_start_latches_a_library_and_its_count_and_takes_no_reference(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """The start records a library and its count, takes no reference, and a repeat is silent."""
    recording = stand_in_kernel(_RECORDING)
    with caplog.at_level(logging.WARNING, logger="aletheia"):
        start_runtime(1, lib_path=recording)
        start_runtime(1, lib_path=recording)
    assert RTSState.initialized
    assert RTSState.lib is not None
    assert (RTSState.cores, RTSState.refcount) == (1, 0)
    assert _mismatches(caplog) == []


def _no_search() -> Never:
    pytest.fail("the renderer searched for a library instead of reading the started one")


@pytest.mark.usefixtures("unstarted")
def test_a_render_after_a_start_reads_the_started_library(monkeypatch: pytest.MonkeyPatch) -> None:
    """With no backend registered, a threshold renders through the library the start opened."""
    start_runtime(1, lib_path=stand_in_kernel(_RECORDING))
    # A renderer opening a library of its own fails here, before it calls one.
    monkeypatch.setattr("aletheia.client._ffi.find_ffi_library", _no_search)
    # The recording stand-in renders a rational as its two components.
    assert format_rational(Fraction(220)) == "220/1"


@pytest.mark.usefixtures("unstarted")
def test_a_check_built_after_a_start_sends_its_property_to_the_started_library(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A check's build hands its property's JSON to the library the start opened.

    The recording stand-in refuses every property, quoting the text it was
    handed, under a code no error code names: its envelope is read as the
    build took it, before the build refuses that code.
    """
    start_runtime(1, lib_path=stand_in_kernel(_RECORDING))
    monkeypatch.setattr("aletheia.client._ffi.find_ffi_library", _no_search)
    take, taken = keeping(take_error_envelope)
    monkeypatch.setattr("aletheia.client._helpers.property_check.take_error_envelope", take)
    with pytest.raises(ProtocolError) as refused:
        _ = signal("S").never_exceeds(220)
    assert (refused.type, refused.value.code, str(refused.value)) == (
        ProtocolError,
        None,
        'reply code: expected an error code, got "recording_kernel"',
    )
    assert taken == [
        {
            "status": "error",
            "code": "recording_kernel",
            "message": 'check_property {"operator": "atomic", "predicate":'
            + ' {"predicate": "lessThanOrEqual", "signal": "S", "value": 220}}',
        }
    ]


@pytest.mark.usefixtures("unstarted")
def test_a_check_built_while_the_runtime_is_down_is_refused_naming_the_remedy() -> None:
    """A check's build before any start names ``start_runtime`` and what it was building."""
    with pytest.raises(FFIError) as refused:
        _ = signal("S").never_exceeds(220)
    assert str(refused.value) == (
        "GHC runtime not initialized: call aletheia.start_runtime or open a client"
        + " before building a check"
    )


@pytest.mark.usefixtures("unstarted")
def test_a_check_refused_without_an_envelope_is_a_protocol_error() -> None:
    """A property check the library refuses with no error envelope is a wire fault.

    The null stand-in kernel answers the check entry with failure and no
    envelope; its backend starts the runtime on it, under a latch of the test's
    own, so the build calls it, and the fault is a ``ProtocolError`` with no code.
    """
    _ = FFIBackend(lib_path=stand_in_kernel(StandInName("null_kernel")))
    with pytest.raises(ProtocolError) as refused:
        _ = signal("S").never_exceeds(220)
    assert str(refused.value) == "aletheia_check_property refused without an error"
    assert refused.value.code is None


@pytest.mark.usefixtures("unstarted")
@pytest.mark.runtime_cores("the refusals and the warning are the claim")
def test_counts_are_held_to_one_through_the_cpus_the_runtime_counts(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """On a stand-in counting four CPUs, 0 and 5 are refused, and 4 asked of one on 1 warns.

    The warning is the ``aletheia`` logger's ``rts.cores_mismatch`` record,
    carrying both counts as fields.
    """
    recording = stand_in_kernel(_RECORDING)
    start_runtime(1, lib_path=recording)
    for past in (0, _STAND_IN_CPUS + 1):
        with pytest.raises(ValidationError) as refused:
            start_runtime(past, lib_path=recording)
        assert str(refused.value) == (
            f"core count {past} is outside 1 to {_STAND_IN_CPUS}, the CPUs this process may use"
        )
    with caplog.at_level(logging.WARNING, logger="aletheia"):
        start_runtime(_STAND_IN_CPUS, lib_path=recording)
    assert RTSState.cores == 1
    assert _records(caplog) == _FOUR_ASKED_OF_ONE


@pytest.mark.usefixtures("unstarted")
def test_a_client_naming_no_count_asks_the_running_count(
    monkeypatch: pytest.MonkeyPatch, caplog: pytest.LogCaptureFixture
) -> None:
    """With the runtime running on four, a count-less client's backend asks four, silently."""
    recording = stand_in_kernel(_RECORDING)
    start_runtime(1, lib_path=recording)
    monkeypatch.setattr(RTSState, "cores", _STAND_IN_CPUS)
    monkeypatch.setenv("ALETHEIA_LIB", str(recording))
    with caplog.at_level(logging.WARNING, logger="aletheia"):
        with AletheiaClient():
            assert RTSState.refcount == 1
        asked = FFIBackend(lib_path=recording).rts_cores
        with AletheiaClient(rts_cores=1):
            pass
    assert asked == _STAND_IN_CPUS
    assert _mismatches(caplog) == ["rts.cores_mismatch active_cores=4 requested_cores=1"]


@pytest.mark.usefixtures("unstarted")
@pytest.mark.runtime_cores("the count the backend reports beside the running one is the claim")
def test_a_backend_asking_another_count_reports_the_count_it_asked(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """A backend asking four of a runtime running on one reports four, and the ask is warned.

    The runtime keeps its one; the warning is the ``aletheia`` logger's
    ``rts.cores_mismatch`` record, carrying both counts as fields.
    """
    recording = stand_in_kernel(_RECORDING)
    start_runtime(1, lib_path=recording)
    with caplog.at_level(logging.WARNING, logger="aletheia"):
        asked = FFIBackend(rts_cores=_STAND_IN_CPUS, lib_path=recording).rts_cores
    assert (asked, RTSState.cores) == (_STAND_IN_CPUS, 1)
    assert _records(caplog) == _FOUR_ASKED_OF_ONE


@pytest.mark.usefixtures("rts_up")
def test_a_start_of_a_started_runtime_on_its_count_changes_nothing(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """``start_runtime(1)`` of a runtime up on one is silent and keeps the latch and the count."""
    lib, refcount = RTSState.lib, RTSState.refcount
    with caplog.at_level(logging.WARNING, logger="aletheia"):
        start_runtime(1)
    assert (RTSState.lib, RTSState.cores, RTSState.refcount) == (lib, 1, refcount)
    assert _mismatches(caplog) == []


def test_a_library_path_that_names_nothing_is_refused(tmp_path: Path) -> None:
    """``lib_path`` naming no file is refused as a backend refuses it, before any start."""
    with pytest.raises(OSError, match="cannot open shared object file"):
        start_runtime(1, lib_path=tmp_path / "absent.so")
