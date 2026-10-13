# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The words the determinism gate's wide net finds in tests, dismissed with their reasons.

``tools/check_test_determinism.py`` reads each test's code with a second net,
each binding's own and wider than its catalogue, for words that name a clock, a
timer, a wait, a thread, a task or a process.  A word it finds that no catalogue
site covers fails the gate unless a row below dismisses it, with the reason
recorded for it: for one file, or with no file for every test of its binding.
A row no site needs fails too, since it would stand as permission past what the
tests spell.  Adding a row needs user approval, on the same footing as a
suppression.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NamedTuple

from tools._common import RelPath
from tools._determinism_syntax import CPP, GO, PYTHON, RUST, BindingName, NetWord

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping


class Dismissal(NamedTuple):
    """What a row covers: a binding's word in one file, or with no file in every one."""

    binding: BindingName
    word: NetWord
    file: RelPath | None


# The reasons a process a test starts is one its claim needs, shared by the files below.
_FRESH_RUNTIME = Prose(
    "the claim holds only where the GHC runtime starts fresh, which it does once per process"
)
_CAP_ENDS_PROCESS = Prose(
    "a tight heap cap ends its process, and the runtime starts once per process"
)
_LOCALE = Prose(
    "the runtime reads the locale once, when it starts, so another locale needs another process"
)
_FENCES = Prose("each fence of the documents is built and run as the program a reader would run")
_TRACKED = Prose("the claim is over git's tracked files, which only git answers")

DISMISSED: Mapping[Dismissal, Prose] = {
    Dismissal(GO, NetWord("runtime.Caller"), None): (
        Prose("the caller's source position, no scheduling")
    ),
    Dismissal(GO, NetWord("time.Second"), None): (
        Prose("a duration compared as a value, no clock read")
    ),
    Dismissal(GO, NetWord("exec.Command"), RelPath("go/aletheia/doc_examples_test.go")): _FENCES,
    Dismissal(GO, NetWord("exec.Command"), RelPath("go/aletheia/doc_files_test.go")): _TRACKED,
    Dismissal(GO, NetWord("exec.Command"), RelPath("go/aletheia/loader_failures_test.go")): (
        Prose("a library is opened once per process")
    ),
    Dismissal(GO, NetWord("exec.Command"), RelPath("go/aletheia/locale_test.go")): _LOCALE,
    Dismissal(GO, NetWord("exec.Command"), RelPath("go/aletheia/main_test.go")): _FRESH_RUNTIME,
    Dismissal(GO, NetWord("exec.Command"), RelPath("go/aletheia/rts_heap_cap_test.go")): (
        _CAP_ENDS_PROCESS
    ),
    Dismissal(PYTHON, NetWord("asyncio.CancelledError"), None): Prose("an exception type"),
    Dismissal(PYTHON, NetWord("asyncio.Task"), None): Prose("a type annotation"),
    Dismissal(PYTHON, NetWord("asyncio.current_task"), None): (
        Prose("the running task, on the test's one thread")
    ),
    Dismissal(PYTHON, NetWord("asyncio.run"), None): (
        Prose("the event loop on the test's own thread")
    ),
    Dismissal(PYTHON, NetWord("asyncio.sleep"), None): (
        Prose("the zero sleep, one turn of the loop, which the catalogue exempts")
    ),
    Dismissal(PYTHON, NetWord("asyncio.testing"), None): Prose("the turn executor's module"),
    Dismissal(PYTHON, NetWord("asyncio.timeout"), None): (
        Prose("the zero timeout, the next turn, which the catalogue exempts")
    ),
    Dismissal(PYTHON, NetWord("concurrent"), None): Prose(
        "the module the executor interface and its future come from; a pool it starts is "
        + "counted by its own name, and the runtime guard refuses its thread"
    ),
    Dismissal(PYTHON, NetWord("os.getpid"), None): Prose("the test's own process id"),
    Dismissal(PYTHON, NetWord("os.kill"), None): (
        Prose("a signal to a child the test drives through a handshake")
    ),
    Dismissal(PYTHON, NetWord("os.utime"), None): Prose("file times set to fixed instants"),
    Dismissal(PYTHON, NetWord("os.waitpid"), None): (
        Prose("a wait for a child's exit, with no duration")
    ),
    Dismissal(PYTHON, NetWord("queue.Empty"), None): Prose("an exception type"),
    Dismissal(PYTHON, NetWord("resource.RUSAGE_SELF"), None): Prose("a memory reading's selector"),
    Dismissal(PYTHON, NetWord("resource.getrusage"), None): (
        Prose("the peak resident memory, not a time")
    ),
    Dismissal(PYTHON, NetWord("signal.SIGINT"), None): Prose("a signal number"),
    Dismissal(PYTHON, NetWord("signal.SIGKILL"), None): Prose("a signal number"),
    Dismissal(PYTHON, NetWord("signal.SIGTERM"), None): Prose("a signal number"),
    Dismissal(PYTHON, NetWord("sleep"), None): Prose("a local name, not the function"),
    Dismissal(PYTHON, NetWord("st_mtime"), None): (
        Prose("a file time moved by a fixed offset, the result never compared with a clock")
    ),
    Dismissal(PYTHON, NetWord("st_mtime_ns"), None): (
        Prose("a file's own time compared before and after a run, never with a clock")
    ),
    Dismissal(PYTHON, NetWord("subprocess.CompletedProcess"), None): Prose("a type annotation"),
    Dismissal(PYTHON, NetWord("subprocess.DEVNULL"), None): Prose("a stream redirection"),
    Dismissal(PYTHON, NetWord("subprocess.PIPE"), None): Prose("a stream redirection"),
    Dismissal(PYTHON, NetWord("subprocess.STDOUT"), None): Prose("a stream redirection"),
    Dismissal(PYTHON, NetWord("wait("), None): Prose("a wait for a child's exit, with no duration"),
    Dismissal(CPP, NetWord("atomic"), None): (
        Prose("an atomic read or write on the test's one thread")
    ),
    Dismissal(CPP, NetWord("chrono"), None): (
        Prose("durations as values and the timestamp type, no clock read")
    ),
    Dismissal(CPP, NetWord("steady_clock"), None): (
        Prose("a clock type naming the stepping clock's unit, never read")
    ),
    Dismissal(CPP, NetWord("stop_source"), None): (
        Prose("a cancellation requested on the test's own thread")
    ),
    Dismissal(CPP, NetWord("stop_token"), None): (
        Prose("a cancellation token, read on the test's own thread")
    ),
    Dismissal(CPP, NetWord("wait("), None): Prose("a blocking lock wait with no duration"),
    Dismissal(CPP, NetWord("wait_until_free("), None): (
        Prose("a blocking lock wait with no duration")
    ),
    Dismissal(CPP, NetWord("waitpid("), None): Prose("a wait for a child's exit, with no duration"),
    Dismissal(CPP, NetWord("fork("), RelPath("cpp/tests/fresh_process_tests.cpp")): Prose(
        "each suite it starts claims what holds only in a process of its own: the renderer "
        + "refusing where no runtime was ever started, its library search kept once per "
        + "process, the heap cap ending its process; the mutation binary folds them in, so "
        + "they run as its children"
    ),
    Dismissal(CPP, NetWord("fork("), RelPath("cpp/tests/test_rts_heap_cap.cpp")): _CAP_ENDS_PROCESS,
    Dismissal(CPP, NetWord("popen("), RelPath("cpp/tests/doc_example_tests.cpp")): _FENCES,
    Dismissal(RUST, NetWord("Mutex"), None): Prose("a lock no second thread contends"),
    Dismissal(RUST, NetWord("block_on"), None): (
        Prose("the turn executor's driver, on the test's own thread")
    ),
    Dismissal(RUST, NetWord("Command"), RelPath("rust/tests/doc_examples.rs")): (
        Prose(f"{_FENCES}; {_TRACKED}")
    ),
    Dismissal(RUST, NetWord("Command"), RelPath("rust/tests/locale.rs")): _LOCALE,
    Dismissal(RUST, NetWord("Command"), RelPath("rust/tests/rts_heap_cap.rs")): _CAP_ENDS_PROCESS,
}
