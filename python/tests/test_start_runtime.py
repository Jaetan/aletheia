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
and whose runtime entry is a no-op, under a runtime latch of the test's own
(``unstarted``).  The claims about a process whose runtime has not started run
as programs of their own against the built library.
"""

from __future__ import annotations

import logging
import os
import sys
from typing import TYPE_CHECKING, Never, NewType

import pytest
from _cli_check_helpers import FFI_LIB, dbc_text, never_exceeds_yaml, run_captured, skip_without_ffi
from _stand_in import StandInName, stand_in_kernel

from aletheia import AletheiaClient, FFIBackend, RTSState, ValidationError, start_runtime
from aletheia.checks import signal
from aletheia.common_types import Prose

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
    """Parsing a decimal and rendering a threshold before any start each name ``start_runtime``."""
    out, _ = _run(_REFUSED_BEFORE_A_START)
    assert out == [
        "FFIError GHC runtime not initialized: call aletheia.start_runtime or open a client"
        + " before parsing decimals",
        "FFIError GHC runtime not initialized: call aletheia.start_runtime or open a client"
        + " before rendering",
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
    rendered = signal("S").never_exceeds(220).condition_desc
    # The recording stand-in renders a rational as its two components.
    assert rendered == "<= 220/1"


@pytest.mark.usefixtures("unstarted")
@pytest.mark.runtime_cores("the refusals and the warning are the claim")
def test_counts_are_held_to_one_through_the_cpus_the_runtime_counts(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """On a stand-in counting four CPUs, 0 and 5 are refused, and 4 asked of one on 1 warns."""
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
    assert _mismatches(caplog) == ["rts.cores_mismatch active_cores=1 requested_cores=4"]


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
