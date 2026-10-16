# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold every test of the suite to determinism while it runs.

A test reads no clock, waits on no duration and starts no thread (AGENTS.md,
Universal Rules).  The static gate reads what a test spells; this plugin holds
what a test reaches, the code under test and the libraries it calls included.

While a session runs, the plugin replaces the clock: ``time``'s clocks, the
defaults of its calendar functions, ``datetime.datetime.now`` and ``utcnow``,
and ``datetime.date.today``, which reads ``time.time``, all read :data:`CLOCK`,
which stands still unless a test moves it through the ``clock`` fixture.  Every
test starts from the same instant.
Code that bound a clock function or class before the session started keeps the
real one: pytest's own timing, and the ``threading`` and ``subprocess``
internals, which read it only for the waits refused below.

A test that starts a thread, sleeps, schedules a callback for later or waits
with a timeout fails at the call, named, and again at its teardown if the
call's error was caught: ``Thread.start`` and ``_thread``'s starters,
``time.sleep``, an event loop's ``call_at`` past the clock's instant
(``asyncio.sleep``, ``call_later`` and a positive ``asyncio.timeout`` all
schedule through it), ``Popen.wait`` and ``Popen.communicate`` with a timeout
(``subprocess.run(timeout=...)`` included), ``Condition.wait`` with a timeout
(which ``Event.wait``, ``Queue.get`` and ``Semaphore.acquire`` wait through),
``select.select`` with a timeout, and ``signal.alarm`` and ``signal.setitimer``
with a positive delay.  A lock's timed ``acquire`` is C and is left as it is:
with no second thread, no lock is ever contended.

A test starts a process only where its claim is that process's own answer, and
says so with ``@pytest.mark.process("<reason>")``.  An audit hook sees every
process start (``subprocess``, ``os.fork``, ``os.posix_spawn``, ``os.system``,
the ``exec`` and ``spawn`` families) and fails one made by a test without the
mark, or outside any test, at import or collection.  A mark that gives no
reason fails the test at its setup, and so does a mark on a test that runs to
its end without starting a process, itself or through a fixture recorded as
starting one: a fixture cached for a module or a session starts its process
once, in its first user's setup, so its later users rely on that record.
"""

from __future__ import annotations

import _thread
import asyncio
import datetime as dt
import select
import signal
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from typing import TYPE_CHECKING, Never, NewType, Self

import pytest

from aletheia.common_types import Prose

if TYPE_CHECKING:
    import contextvars
    from collections.abc import Callable, Generator, Iterable, Iterator

    from _typeshed import FileDescriptorLike

Seconds = NewType("Seconds", float)
Nanoseconds = NewType("Nanoseconds", int)
# A whole number of seconds, as ``signal.alarm`` takes and returns them.
WholeSeconds = NewType("WholeSeconds", int)
# The clock a ``clock_gettime`` call names, and the timer a ``setitimer`` call names.
ClockId = NewType("ClockId", int)
TimerId = NewType("TimerId", int)
# A ``strftime`` format, and the text ``ctime``, ``asctime`` and ``strftime`` return.
TimeFormat = NewType("TimeFormat", str)
TimeText = NewType("TimeText", str)
# What a process reads and writes on its standard streams, as bytes.
ProcessBytes = NewType("ProcessBytes", bytes)

_NS_PER_S = 1_000_000_000
# The instant every test starts from, 2026-01-01T00:00:00Z, read by the wall
# clock and the steady clocks alike.
_START = Nanoseconds(1_767_225_600 * _NS_PER_S)


class Clock:
    """The one clock the suite reads: it moves only when a test advances it."""

    def __init__(self) -> None:
        """Start at the instant every test starts from."""
        self._now = _START

    def advance(self, seconds: Seconds) -> None:
        """Move the clock forward by ``seconds``; a clock never moves back."""
        if seconds < 0:
            msg = f"a clock moves forward, not by {seconds} s"
            raise ValueError(msg)
        self._now = Nanoseconds(self._now + round(seconds * _NS_PER_S))

    def reset(self) -> None:
        """Return to the instant every test starts from."""
        self._now = _START

    def seconds(self) -> Seconds:
        """Read the clock in seconds, as ``time.time`` does."""
        return Seconds(self._now / _NS_PER_S)

    def nanoseconds(self) -> Nanoseconds:
        """Read the clock in nanoseconds, as ``time.time_ns`` does."""
        return self._now


CLOCK = Clock()

# One list per running test, innermost last: a session run inside a test (the
# guard's own tests) records its refusals apart from the test that runs it.
_REFUSALS: list[list[Prose]] = []


# What a test may not do, as a refusal states it.
_TIME_RULE = Prose("a test reads no clock, waits on no duration and starts no thread")
_PROCESS_RULE = Prose(
    "a test starts a process only where its claim is that process's own answer,"
    + ' and says which with @pytest.mark.process("<reason>")'
)


def _refuse(what: Prose, rule: Prose = _TIME_RULE, *, in_a_test: bool = True) -> Never:
    """Fail the running test, or the collection outside any test, at a call that breaks ``rule``."""
    message = Prose(f"{what}: {rule}")
    if in_a_test and _REFUSALS:
        _REFUSALS[-1].append(message)
    pytest.fail(message)


# --- The clock.


def _seconds() -> Seconds:
    return CLOCK.seconds()


def _nanoseconds() -> Nanoseconds:
    return CLOCK.nanoseconds()


def _clock_seconds(_clock: ClockId) -> Seconds:
    return CLOCK.seconds()


def _clock_nanoseconds(_clock: ClockId) -> Nanoseconds:
    return CLOCK.nanoseconds()


_real_localtime = time.localtime
_real_gmtime = time.gmtime
_real_ctime = time.ctime
_real_asctime = time.asctime
_real_strftime = time.strftime


def _localtime(secs: Seconds | None = None) -> time.struct_time:
    return _real_localtime(CLOCK.seconds() if secs is None else secs)


def _gmtime(secs: Seconds | None = None) -> time.struct_time:
    return _real_gmtime(CLOCK.seconds() if secs is None else secs)


def _ctime(secs: Seconds | None = None) -> TimeText:
    return TimeText(_real_ctime(CLOCK.seconds() if secs is None else secs))


def _asctime(t: time.struct_time | None = None) -> TimeText:
    return TimeText(_real_asctime(_real_localtime(CLOCK.seconds()) if t is None else t))


def _strftime(fmt: TimeFormat, t: time.struct_time | None = None) -> TimeText:
    return TimeText(_real_strftime(fmt, _real_localtime(CLOCK.seconds()) if t is None else t))


class _DateTime(dt.datetime):
    """``datetime.datetime`` whose current instant is the clock's."""

    @classmethod
    def now(cls, tz: dt.tzinfo | None = None) -> Self:
        """Read the clock as a date and time, in ``tz`` or in local time."""
        return cls.fromtimestamp(CLOCK.seconds(), tz)

    @classmethod
    def utcnow(cls) -> Self:
        """Read the clock as a naive UTC date and time."""
        return cls.fromtimestamp(CLOCK.seconds(), dt.UTC).replace(tzinfo=None)


# --- Waits and threads.


def _sleep(secs: Seconds) -> Never:
    _refuse(Prose(f"time.sleep({secs})"))


def _thread_start(self: threading.Thread) -> Never:
    _refuse(Prose(f"a thread started ({self.name})"))


def _start_thread(function: Callable[..., None], *_rest: Never) -> Never:
    _refuse(Prose(f"a thread started on {function.__qualname__}"))


_real_call_at = asyncio.BaseEventLoop.call_at


def _call_at[*Ts](
    self: asyncio.BaseEventLoop,
    when: Seconds,
    callback: Callable[[*Ts], None],
    *args: *Ts,
    context: contextvars.Context | None = None,
) -> asyncio.TimerHandle:
    if when > self.time():
        ahead = when - self.time()
        _refuse(Prose(f"a callback scheduled {ahead} s ahead ({callback.__qualname__})"))
    return _real_call_at(self, when, callback, *args, context=context)


# Read as a process of bytes; a process of text runs the same method.
_real_popen_wait = subprocess.Popen[ProcessBytes].wait
_real_popen_communicate = subprocess.Popen[ProcessBytes].communicate


def _popen_wait(
    self: subprocess.Popen[ProcessBytes], timeout: Seconds | None = None
) -> WholeSeconds:
    if timeout is not None:
        _refuse(Prose(f"a process waited on for {timeout} s"))
    return WholeSeconds(_real_popen_wait(self))


def _popen_communicate(
    self: subprocess.Popen[ProcessBytes],
    stdin: ProcessBytes | None = None,
    timeout: Seconds | None = None,
) -> tuple[ProcessBytes, ProcessBytes]:
    if timeout is not None:
        _refuse(Prose(f"a process waited on for {timeout} s"))
    out, err = _real_popen_communicate(self, stdin)
    return ProcessBytes(out), ProcessBytes(err)


_real_condition_wait = threading.Condition.wait


def _condition_wait(self: threading.Condition, timeout: Seconds | None = None) -> bool:
    if timeout is not None:
        _refuse(Prose(f"a wait of {timeout} s on a condition"))
    return _real_condition_wait(self)


_real_select = select.select


def _select[R: FileDescriptorLike, W: FileDescriptorLike, X: FileDescriptorLike](
    rlist: Iterable[R], wlist: Iterable[W], xlist: Iterable[X], timeout: Seconds | None = None
) -> tuple[list[R], list[W], list[X]]:
    if timeout is not None:
        _refuse(Prose(f"a select of {timeout} s"))
    return _real_select(rlist, wlist, xlist)


_real_alarm = signal.alarm
_real_setitimer = signal.setitimer


def _alarm(seconds: WholeSeconds) -> WholeSeconds:
    if seconds > 0:
        _refuse(Prose(f"an alarm set {seconds} s ahead"))
    return WholeSeconds(_real_alarm(seconds))


def _setitimer(
    which: TimerId, seconds: Seconds, interval: Seconds | None = None
) -> tuple[Seconds, Seconds]:
    if seconds > 0:
        _refuse(Prose(f"a timer set {seconds} s ahead"))
    delay, every = _real_setitimer(which, seconds, 0.0 if interval is None else interval)
    return Seconds(delay), Seconds(every)


# --- Processes.

# An audit event's name, as ``sys.audit`` raises it.
AuditEvent = NewType("AuditEvent", str)
# How many process starts a running test has made.
StartCount = NewType("StartCount", int)
# A fixture as the guard records it: the node it is defined in, and its name.
FixtureKey = NewType("FixtureKey", str)
# The name a test or a fixture asks a fixture by.
FixtureName = NewType("FixtureName", str)

# The events a process start raises: one ``subprocess`` call raises its own and
# the ``posix_spawn`` or fork-and-exec beneath it; ``os.spawnv`` and its family
# fork, raising ``os.fork``.
_PROCESS_EVENTS = frozenset(
    {
        AuditEvent("subprocess.Popen"),
        AuditEvent("_posixsubprocess.fork_exec"),
        AuditEvent("os.posix_spawn"),
        AuditEvent("os.fork"),
        AuditEvent("os.forkpty"),
        AuditEvent("os.exec"),
        AuditEvent("os.system"),
    }
)


@dataclass
class _Running:
    """A test while it runs: its mark's reason, the fixtures it asks for, its starts.

    ``scopes`` are the node ids of the test and of every collector above it, where
    a fixture it can see is defined, as pytest matches a fixture to a test.
    """

    nodeid: Prose
    reason: Prose | None
    fixtures: frozenset[FixtureName]
    scopes: frozenset[Prose]
    started: StartCount = StartCount(0)


# The tests running, innermost last, each session's opened by None: a session
# run inside a test collects and runs tests of its own.  The fixtures being set
# up, innermost last, and those whose setup started a process, recorded for
# their later users.
_RUNNING: list[_Running | None] = []
_SETTING_UP: list[FixtureKey] = []
_STARTING_FIXTURES: set[FixtureKey] = set()


def _fixture_key(baseid: Prose, name: FixtureName) -> FixtureKey:
    return FixtureKey(f"{baseid}::{name}")


def _marked_reason(item: pytest.Item) -> Prose | None:
    """Return the reason ``item``'s process mark gives, or None for no mark or no reason."""
    marker = item.get_closest_marker("process")
    if marker is None or marker.kwargs or len(marker.args) != 1:
        return None
    reason = marker.args[0]
    return Prose(reason) if isinstance(reason, str) and reason.strip() else None


def _relies_on_a_starting_fixture(running: _Running) -> bool:
    """Say whether a fixture ``running`` asks for, visible where it runs, started a process."""
    return any(
        _fixture_key(base, name) in _STARTING_FIXTURES
        for name in running.fixtures
        for base in running.scopes
    )


def _audit(event: AuditEvent) -> None:
    """Refuse a process start in a test whose mark gives no reason, or outside any test."""
    if not _SESSIONS:
        return
    running = _RUNNING[-1] if _RUNNING else None
    if running is None:
        outside = Prose(f"a process started outside any test ({event})")
        _refuse(outside, _PROCESS_RULE, in_a_test=False)
    if running.reason is None:
        _refuse(Prose(f"{running.nodeid} started a process ({event})"), _PROCESS_RULE)
    running.started = StartCount(running.started + 1)
    if _SETTING_UP:
        _STARTING_FIXTURES.add(_SETTING_UP[-1])


def _audit_hook(event: str, _args: tuple[object, ...]) -> None:
    """Hand a process start to :func:`_audit`; every other event passes untouched."""
    if event in _PROCESS_EVENTS:
        _audit(AuditEvent(event))


# The audit hook, added once per interpreter: a hook cannot be removed, so it
# acts only while a session runs.
_AUDITING: list[bool] = []


# What the guard replaced, undone when the last session that installed it ends,
# and the sessions running: a session can run inside another, as the guard's
# own tests run theirs, and a harness can run pytest inside a process of its
# own, as the mutation lane's mutmut does, which goes on with the real clock.
_REPLACED = pytest.MonkeyPatch()
_SESSIONS: list[pytest.Config] = []


def _install() -> None:
    for _name in ("time", "monotonic", "perf_counter", "process_time", "thread_time"):
        _REPLACED.setattr(time, _name, _seconds)
    for _name in (
        "time_ns",
        "monotonic_ns",
        "perf_counter_ns",
        "process_time_ns",
        "thread_time_ns",
    ):
        _REPLACED.setattr(time, _name, _nanoseconds)
    _REPLACED.setattr(time, "clock_gettime", _clock_seconds)
    _REPLACED.setattr(time, "clock_gettime_ns", _clock_nanoseconds)
    _REPLACED.setattr(time, "localtime", _localtime)
    _REPLACED.setattr(time, "gmtime", _gmtime)
    _REPLACED.setattr(time, "ctime", _ctime)
    _REPLACED.setattr(time, "asctime", _asctime)
    _REPLACED.setattr(time, "strftime", _strftime)
    _REPLACED.setattr(time, "sleep", _sleep)
    _REPLACED.setattr(dt, "datetime", _DateTime)
    _REPLACED.setattr(threading.Thread, "start", _thread_start)
    _REPLACED.setattr(_thread, "start_new_thread", _start_thread)
    _REPLACED.setattr(_thread, "start_joinable_thread", _start_thread)
    _REPLACED.setattr(asyncio.BaseEventLoop, "call_at", _call_at)
    _REPLACED.setattr(subprocess.Popen, "wait", _popen_wait)
    _REPLACED.setattr(subprocess.Popen, "communicate", _popen_communicate)
    _REPLACED.setattr(threading.Condition, "wait", _condition_wait)
    _REPLACED.setattr(select, "select", _select)
    _REPLACED.setattr(signal, "alarm", _alarm)
    _REPLACED.setattr(signal, "setitimer", _setitimer)


def installed() -> bool:
    """Say whether the guard holds the clock and the waits, as it does while a session runs."""
    return threading.Thread.start is _thread_start


def pytest_configure(config: pytest.Config) -> None:
    """Replace the clock and the waits when the first session starts, and hold its processes."""
    config.addinivalue_line(
        "markers", "process(reason): the test starts a process, whose answer is its claim"
    )
    if not _SESSIONS:
        _install()
    if not _AUDITING:
        sys.addaudithook(_audit_hook)
        _AUDITING.append(True)
    _SESSIONS.append(config)


def pytest_unconfigure(config: pytest.Config) -> None:
    """Put the real clock and waits back when the last session ends."""
    _SESSIONS.remove(config)
    if not _SESSIONS:
        _REPLACED.undo()


def pytest_sessionstart() -> None:
    """Open a session's place on the running stack: until a test of it runs, none does."""
    _RUNNING.append(None)


def pytest_sessionfinish() -> None:
    """Close the session's place on the running stack."""
    _ = _RUNNING.pop()


@pytest.hookimpl(wrapper=True)
def pytest_runtest_protocol(item: pytest.Item) -> Generator[None]:
    """Hold a test's process starts to its mark, from its first fixture to its last."""
    fixtures = frozenset(FixtureName(name) for name in getattr(item, "fixturenames", ()))
    scopes = frozenset(Prose(node.nodeid) for node in item.iter_parents())
    _RUNNING.append(_Running(Prose(item.nodeid), _marked_reason(item), fixtures, scopes))
    try:
        yield
    finally:
        _ = _RUNNING.pop()


@pytest.hookimpl(tryfirst=True)
def pytest_runtest_setup(item: pytest.Item) -> None:
    """Fail a test whose process mark gives no reason, before its fixtures run."""
    if item.get_closest_marker("process") is not None and _marked_reason(item) is None:
        pytest.fail(f'{item.nodeid}: @pytest.mark.process takes one reason, as "<reason>"')


@pytest.hookimpl(wrapper=True)
def pytest_fixture_setup[V](fixturedef: pytest.FixtureDef[V]) -> Generator[None, V, V]:
    """Record a fixture whose setup starts a process, for the tests that rely on it later."""
    _SETTING_UP.append(_fixture_key(Prose(fixturedef.baseid), FixtureName(fixturedef.argname)))
    try:
        return (yield)
    finally:
        _ = _SETTING_UP.pop()


@pytest.hookimpl(wrapper=True)
def pytest_runtest_call() -> Generator[None]:
    """Report a refusal once, and fail a process mark its test had no use for."""
    try:
        yield
    except pytest.fail.Exception as failure:
        if _REFUSALS and failure.msg is not None and failure.msg in _REFUSALS[-1]:
            _REFUSALS[-1].remove(Prose(failure.msg))
        raise
    running = _RUNNING[-1] if _RUNNING else None
    if (
        running is not None
        and running.reason is not None
        and running.started == 0
        and not _relies_on_a_starting_fixture(running)
    ):
        pytest.fail(f"{running.nodeid}: its process mark allows a process it never starts")


@pytest.fixture(autouse=True)
def clock() -> Iterator[Clock]:
    """Start each test at the same instant, and fail it at teardown on a refusal its code caught."""
    CLOCK.reset()
    refusals: list[Prose] = []
    _REFUSALS.append(refusals)
    try:
        yield CLOCK
    finally:
        _ = _REFUSALS.pop()
    if refusals:
        pytest.fail("\n".join(refusals))
