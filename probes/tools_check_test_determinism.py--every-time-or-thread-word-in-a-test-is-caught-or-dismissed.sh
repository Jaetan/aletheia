#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_test_determinism.py.
# Claim: every word in a test that names a clock, a timer, a wait, a thread, a
# task or a process, in any binding, is either a site the gate's catalogue
# counts or a spelling dismissed below with the reason it reads no physical
# time and starts nothing beside the test; a word that starts a process is
# dismissed only in the files named, each a process the test's claim needs. The net is wider than the
# catalogue, read over the same code the gate reads (comments and literals
# blanked, aliases spelled out), skipping what the catalogue counts, so a
# spelling the catalogue does not know lands here as undismissed instead of
# passing unseen. A dismissal is a reason, not a count: a test that adds
# another use of a dismissed word passes, and a new word does not.
# Non-zero exit: a word the net finds is neither counted by the catalogue nor
# dismissed, or the gate's modules cannot be imported. Exits 2 without the
# virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2
PYTHONPATH=$PWD:$PWD/python exec "$py" - << 'PY'
import re
import sys
from pathlib import Path

from tools._common import git_ls_files
from tools.check_test_determinism import BINDINGS, SourceText

GO, PYTHON, CPP, RUST = BINDINGS
NETS = {
    GO: r"\btime\.\w+|\bsync\.\w+|\berrgroup\b|\bselect\s*\{|\bchan\b|\bruntime\.\w+"
    r"|\bexec\.Command\w*|\bsignal\.\w+|\bb\.(?:Elapsed|ResetTimer|StartTimer|StopTimer|Loop)\b"
    r"|\bos\.StartProcess\b|\bSetDeadline\b|\bsynctest\b",
    PYTHON: r"\btime\b|\bthreading\.\w+|\bThread\b|\bTimer\b|\basyncio\.\w+|\bloop\.\w+"
    r"|\bconcurrent\b|\bsubprocess\.\w+|\bPopen\b|\bsignal\.\w+|\bselect\.\w+|\bselectors\b"
    r"|\bsched\b|\btimeit\b|\bdatetime\b|\bos\.(?:times|fork\w*|utime|kill|wait\w*|getpid)\b"
    r"|\bst_[amc]time\w*|\bresource\.\w+|\bfaulthandler\.\w+|\bmark\.timeout\b|\bsettimeout\b"
    r"|\bsleep\b|\bmonotonic\b|\bperf_counter\b|\bwait\s*\(|\bas_completed\b|\banyio\b|\btrio\b"
    r"|\bfreezegun\b|\bqueue\.\w+|\bBarrier\b|\bCondition\b|\bSemaphore\b",
    CPP: r"\bchrono\b|\w*_clock\b|\bj?thread\b|\bthis_thread::\w+|\basync\b|\bfuture\b"
    r"|\bpromise\b|\bpackaged_task\b|\bcondition_variable\w*|\bclock\s*\(|\bfork\s*\("
    r"|\bposix_spawn\w*|\bpopen\s*\(|\bsystem\s*\(|\blatch\b|\bbarrier\b|\bsemaphore\b"
    r"|\batomic\w*|\bpoll\s*\(|\bselect\s*\(|\bepoll\w*|\bpthread_\w+|\bwait\w*\s*\("
    r"|\bstop_token\b|\bstop_source\b",
    RUST: r"\bstd::time\b|\bDuration\b|\bInstant\b|\bSystemTime\b|\bUNIX_EPOCH\b|\bthread\b"
    r"|\bspawn\w*\b|\btokio\w*|\basync_std\b|\bsmol\b|\brayon\b|\bcrossbeam\b|\bblock_on\b"
    r"|\bmpsc\b|\bCondvar\b|\bBarrier\b|\bpark\w*\b|\bCommand\b|\bchrono\b|\bjoin!|\bselect!"
    r"|\bsleep\b|\belapsed\b|\bMutex\b|\bAtomic\w+",
}
# Each dismissed spelling, per binding, with why it is neither physical time
# nor a thread, task or process running beside the test.
DISMISSED = {
    GO: {
        "runtime.Caller": "the caller's source position, no scheduling",
        "time.Second": "a duration compared as a value, no clock read",
    },
    PYTHON: {
        "asyncio.CancelledError": "an exception type",
        "asyncio.Task": "a type annotation",
        "asyncio.current_task": "the running task, on the test's one thread",
        "asyncio.run": "the event loop on the test's own thread",
        "asyncio.sleep": "the zero sleep, one turn of the loop, which the catalogue exempts",
        "asyncio.testing": "the turn executor's module",
        "asyncio.timeout": "the zero timeout, the next turn, which the catalogue exempts",
        "os.getpid": "the test's own process id",
        "os.kill": "a signal to a child the test drives through a handshake",
        "os.utime": "file times set to fixed instants",
        "os.waitpid": "a wait for a child's exit, with no duration",
        "queue.Empty": "an exception type",
        "resource.RUSAGE_SELF": "a memory reading's selector",
        "resource.getrusage": "the peak resident memory, not a time",
        "signal.SIGINT": "a signal number",
        "signal.SIGKILL": "a signal number",
        "signal.SIGTERM": "a signal number",
        "sleep": "a local name, not the function",
        "st_mtime": "a file time moved by a fixed offset, the result never compared with a clock",
        "st_mtime_ns": "a file's own time compared before and after a run, never with a clock",
        "subprocess.CompletedProcess": "a type annotation",
        "subprocess.DEVNULL": "a stream redirection",
        "subprocess.PIPE": "a stream redirection",
        "wait(": "a wait for a child's exit, with no duration",
    },
    CPP: {
        "atomic": "an atomic read or write on the test's one thread",
        "chrono": "durations as values and the timestamp type, no clock read",
        "steady_clock": "a clock type naming the stepping clock's unit, never read",
        "stop_source": "a cancellation requested on the test's own thread",
        "stop_token": "a cancellation token, read on the test's own thread",
        "wait(": "a blocking lock wait with no duration",
        "wait_until_free(": "a blocking lock wait with no duration",
        "waitpid(": "a wait for a child's exit, with no duration",
    },
    RUST: {
        "Mutex": "a lock no second thread contends",
        "block_on": "the turn executor's driver, on the test's own thread",
    },
}
# A process a test starts is one its claim needs, judged file by file: a word
# that starts one in any file not named here is a new site to judge.
FRESH_RUNTIME = "the claim holds only where the GHC runtime starts fresh, which it does once per process"
CAP_ENDS_PROCESS = "a tight heap cap ends its process, and the runtime starts once per process"
LOCALE = "the runtime reads the locale once, when it starts, so another locale needs another process"
FENCES = "each fence of the documents is built and run as the program a reader would run"
TRACKED = "the claim is over git's tracked files, which only git answers"
DISMISSED_IN = {
    GO: {
        "exec.Command": {
            "go/aletheia/doc_examples_test.go": FENCES,
            "go/aletheia/doc_files_test.go": TRACKED,
            "go/aletheia/loader_failures_test.go": "a library is opened once per process",
            "go/aletheia/locale_test.go": LOCALE,
            "go/aletheia/main_test.go": FRESH_RUNTIME,
            "go/aletheia/rts_heap_cap_test.go": CAP_ENDS_PROCESS,
        },
    },
    PYTHON: dict.fromkeys(
        ("subprocess.run", "subprocess.Popen"),
        {
            "python/tests/_cli_check_helpers.py": "the four CLIs are compared as the programs they are,"
            " and a claim about a runtime not yet started runs the command as its own process",
            "python/tests/test_check_build_incremental.py": "a record lock belongs to a process, and"
            " F_GETLK reports only another process's",
            "python/tests/test_check_precise_hints.py": TRACKED,
            "python/tests/test_cli_parity.py": "the Go CLI the parity runs is built from its sources",
            "python/tests/test_demo_scripts.py": "an example is run as the program it is",
            "python/tests/test_ffi_abi_version.py": "a library is loaded once per process",
            "python/tests/test_ffi_strings.py": LOCALE,
            "python/tests/test_git_toplevel.py": TRACKED,
            "python/tests/test_install_hooks.py": "a hook is run as git runs it, over a repository git built",
            "python/tests/test_mutation_run_scope.py": "the modules a fresh interpreter imports are what is claimed",
            "python/tests/test_rts_heap_cap.py": CAP_ENDS_PROCESS,
            "python/tests/test_run_guarded.py": "process groups, a guard's own group and a caller's input are"
            " attributes of processes",
            "python/tests/test_scheduler.py": "an interrupt is a signal to a process group",
            "python/tests/test_streaming_residency.py": "resident memory is measured per process",
            "python/tests/test_tools_library_path.py": "a bare interpreter's import path is what is claimed",
            "python/tests/test_unified_client.py": FRESH_RUNTIME + ", here with two capabilities",
        },
    ),
    CPP: {
        "fork(": {
            "cpp/tests/fresh_process_tests.cpp": "each suite it starts claims what holds only in"
            " a process of its own: the renderer refusing where no runtime was ever started, its"
            " library search kept once per process, the heap cap ending its process; the"
            " mutation binary folds them in, so they run as its children",
            "cpp/tests/test_rts_heap_cap.cpp": CAP_ENDS_PROCESS,
        },
        "popen(": {"cpp/tests/doc_example_tests.cpp": FENCES},
    },
    RUST: {
        "Command": {
            "rust/tests/doc_examples.rs": FENCES + "; " + TRACKED,
            "rust/tests/locale.rs": LOCALE,
            "rust/tests/rts_heap_cap.rs": CAP_ENDS_PROCESS,
        },
    },
}
repo = Path.cwd()
undismissed = set()
for rel in git_ls_files(repo):
    for binding in BINDINGS:
        if binding.is_test(rel) and (repo / rel).is_file():
            code = binding.code(rel, SourceText((repo / rel).read_text(encoding="utf-8")))
            counted = [
                site.span()
                for primitive in binding.primitives
                for site in re.finditer(primitive.pattern, code, re.MULTILINE)
            ]
            for match in re.finditer(NETS[binding], code, re.MULTILINE):
                start, end = match.span()
                if any(start < last and first < end for first, last in counted):
                    continue
                word = re.sub(r"\s+", "", match.group(0))
                if word not in DISMISSED[binding] and rel not in DISMISSED_IN.get(binding, {}).get(
                    word, {}
                ):
                    undismissed.add((rel, word))
for rel, word in sorted(undismissed):
    print(f"{rel}: {word!r} is neither counted by the catalogue nor dismissed")
if undismissed:
    sys.exit(1)
print("PASS: every time or thread word in a test is counted by the catalogue or dismissed with its reason")
PY
