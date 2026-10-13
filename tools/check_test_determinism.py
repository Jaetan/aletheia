# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Refuse a test that reads physical time or starts a thread, unless the record names it.

AGENTS.md § Universal Rules, "a test is deterministic": a test reads no clock
and waits on no duration, and starts no thread, goroutine or concurrent task
beside itself.  Where the code under test needs time, the clock is injected and
the test drives a mock that advances only when told; where it needs
concurrency, the scheduler or the competing party is injected and the test
drives the interleaving step by step.  A test that waits on a duration passes or
fails by how fast the machine was, and one that races a thread passes or fails
by how it was scheduled: a larger timeout or a retry makes the wrong outcome
rarer, never impossible.

It is a ratchet, as the index-loop and precise-hint gates are: the record holds
every time and thread primitive the test files use today, so that a new one
fails, and a row leaves the record by the change that rewrites its sites to a
mocked clock or a driven interleaving.  Both directions are enforced, because a
row naming more sites than the file holds is standing permission to bring one
back:

* a primitive the record does not name, or more of it than recorded, fails the
  gate, which prints the row that would allow it.  Adding a row needs user
  approval, on the same footing as a suppression;
* a row naming more sites than the file holds fails the gate, which prints the
  row to lower or delete.

A second net, each binding's own and wider than its catalogue, reads the same
code for words that name a clock, a timer, a wait, a thread, a task or a
process; a word it finds that no catalogue site covers is not counted, whether
the catalogue does not know it or exempts it.  ``tools/_determinism_dismissals.py``
holds those words, each with the reason recorded for it, for one file or, with no
file, for every test of its binding; a word no row dismisses fails, and in the
tree's run so does a row no site needs.  Adding a row needs user approval.  A
word that starts a process in a Python test under ``python/tests/``, the fuzz
harnesses apart, is left to the runtime guard (``tools/_determinism_guard.py``,
by the test's ``@pytest.mark.process`` reason) rather than to a row; the guard
sees only the suite's own process, not a script there that a test runs as a child.

What is a test file, per binding: ``*_test.go`` under ``go/``; every Python file
under ``python/tests/`` and the repository's ``conftest.py``; every C++ source
under ``cpp/tests/``; every Rust file under a crate's ``tests/`` or holding a
module declared under ``#[cfg(test)]``, or one below such a module, and the
``#[cfg(test)] mod`` blocks of the crates' other sources.  Comments and string
literals are blanked before the scan, so a primitive named in prose is not a
site, and a name bound by an import, a ``use`` or a using-declaration is read
as the qualified name it stands for, so no spelling of an import hides one.  A
Python test's string literal that is a script, one that parses and calls or
imports something, is read as the child source it is: a test hands a child
interpreter its script that way.  The gate's test of its catalogue and the
runtime guard's test are the exception, their strings being the fixtures they
feed what they test.

An example is not a test: a documentation fence and a file under
``examples/`` show production use, and keep the threads and timers that use
needs.  The harness that runs one is a test file like any other.

Rows are keyed by file and by the primitive's label, the kind first (``time:``,
``thread:``, or ``random:`` for a property test whose sample no seed fixes),
with how many sites the file holds.

One setting is held beside the record: ``rust/.cargo/config.toml`` forces
``RUST_TEST_THREADS`` to 1, since the Rust test harness otherwise runs a
binary's tests side by side on threads of one process.  The tree's run fails
when it does not.

Run: ``python -m tools.check_test_determinism`` compares the tree with the
record; ``--file PATH --as REL`` compares one file's text, as it stands after
an edit, with the record's rows for REL, which is what the write-time hook runs;
``--is-test REL...`` prints each REL that is a test file, or a directory holding
a tracked one, and exits 0 when it printed one and 1 when it did not, so the
hook asks this module what a test is rather than spelling it again.  Exit 0 is
clean, 1 a site, a word or a row out of step, 2 a file or the record that cannot be read.
"""

from __future__ import annotations

import argparse
import ast
import io
import re
import sys
import textwrap
import tomllib
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

from tools._common import RelPath, emit, git_ls_files, git_toplevel
from tools._determinism_dismissals import DISMISSED, Dismissal
from tools._determinism_reading import (
    BlankedCode,
    blank_cpp,
    blank_go,
    blank_python,
    blank_rust,
    python_tree,
    spell_cpp_aliases,
    spell_go_aliases,
    spell_python_aliases,
    spell_rust_aliases,
)
from tools._determinism_syntax import (
    ASYNC_CLIENT_ON_A_THREAD,
    CPP,
    GO,
    PYTHON,
    REPLAYING_PROFILE,
    RUST,
    UNSEEDED_PROPERTY,
    BindingName,
    NetWord,
    SiteCount,
    SourceText,
    async_clients_on_a_thread,
    replaying_profiles,
    unseeded_properties,
)
from tools._ratchet import CanonicalText, RatchetRows, RowKey, as_row, read_ratchet_rows

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

RECORD = Path("docs/TEST_DETERMINISM.yaml")
# Cargo's configuration for every Rust crate, whose environment runs each test
# binary's tests one at a time; the harness otherwise runs them side by side.
RUST_CARGO_CONFIG = Path("rust/.cargo/config.toml")
# The table of the net's words dismissed in tests, each with its reason.
_DISMISSALS = Path("tools/_determinism_dismissals.py")
CLEAN, OUT_OF_STEP, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)

# A regular expression's source, compiled where it is matched.
RegexSource = NewType("RegexSource", str)


class Primitive(NamedTuple):
    """One thing a test must not do: its label in the record, and what spells it."""

    label: CanonicalText
    pattern: RegexSource


_GO = (
    Primitive(
        CanonicalText("time: a clock or timer from package time"),
        RegexSource(
            r"\btime\.(?:Sleep|After|AfterFunc|NewTimer|NewTicker|Tick|Now|Since|Until)\s*\("
        ),
    ),
    Primitive(
        CanonicalText("time: a context with a deadline"),
        RegexSource(r"\bcontext\.With(?:Timeout|Deadline)(?:Cause)?\s*\("),
    ),
    Primitive(
        CanonicalText("thread: a go statement"),
        RegexSource(r"(?:^|[;{}\s])go\s+(?:func\b|[A-Za-z_][\w.]*\s*\()"),
    ),
    Primitive(
        CanonicalText("thread: a yield to the scheduler"), RegexSource(r"\bruntime\.Gosched\s*\(")
    ),
    Primitive(
        CanonicalText("thread: a parallel test"),
        RegexSource(r"\.(?:Parallel|RunParallel)\s*\("),
    ),
    Primitive(
        CanonicalText("thread: a goroutine started through a group"), RegexSource(r"\.Go\s*\(")
    ),
    Primitive(
        UNSEEDED_PROPERTY,
        RegexSource(
            r"\bquick\.Config\s*\{(?![^{}]*\bRand\s*:)"
            + r"|\bquick\.Check(?:Equal)?\s*\((?:[^()]|\([^()]*\))*,\s*nil\s*\)"
        ),
    ),
)

_PYTHON = (
    Primitive(
        CanonicalText("time: a clock or sleep from module time"),
        RegexSource(
            r"\btime\.(?:sleep|monotonic|perf_counter|time|process_time|thread_time"
            + r"|clock_gettime)(?:_ns)?\s*\("
        ),
    ),
    Primitive(
        CanonicalText("time: an asyncio sleep of a duration"),
        RegexSource(r"\basyncio\.sleep\s*\(\s*(?!0\s*\))"),
    ),
    Primitive(
        CanonicalText("time: an asyncio timeout"),
        RegexSource(r"\basyncio\.(?:timeout|timeout_at|wait_for)\s*\(\s*(?!0\s*\))"),
    ),
    Primitive(
        CanonicalText("time: a timeout argument"), RegexSource(r"\btimeout\s*=\s*(?!None\b)")
    ),
    Primitive(
        CanonicalText("time: a positional timeout"),
        RegexSource(r"\.(?:wait|join|result)\s*\(\s*(?:(?!0\s*\))\d|[A-Z][A-Z0-9_]*\s*\))"),
    ),
    Primitive(
        CanonicalText("time: a loop callback after a delay"),
        RegexSource(r"\b(?:call_later|call_at)\s*\("),
    ),
    Primitive(
        CanonicalText("time: a wall-clock date"),
        RegexSource(r"\b(?:datetime\.)?(?:datetime|date)\.(?:now|utcnow|today)\s*\("),
    ),
    Primitive(
        CanonicalText("time: a signal timer"),
        RegexSource(
            r"\bsignal\.(?:alarm|setitimer)\s*\(" + r"|\bfaulthandler\.dump_traceback_later\s*\("
        ),
    ),
    Primitive(
        CanonicalText("thread: a yield to the scheduler"), RegexSource(r"\bos\.sched_yield\s*\(")
    ),
    Primitive(
        CanonicalText("thread: a thread or timer from module threading"),
        RegexSource(r"\bthreading\.(?:Thread|Timer)\b"),
    ),
    Primitive(
        CanonicalText("thread: a thread from module _thread"),
        RegexSource(r"\b_thread\.start_new_thread\s*\("),
    ),
    Primitive(
        CanonicalText("thread: an executor"),
        RegexSource(r"\b(?:ThreadPoolExecutor|ProcessPoolExecutor)\b|\brun_in_executor\s*\("),
    ),
    Primitive(
        CanonicalText("thread: a coroutine run on a thread"),
        RegexSource(r"\basyncio\.to_thread\s*\("),
    ),
    Primitive(
        CanonicalText("thread: a concurrent asyncio task"),
        RegexSource(r"\basyncio\.(?:create_task|gather|ensure_future|TaskGroup)\b"),
    ),
    Primitive(
        CanonicalText("thread: a process pool or fork"),
        RegexSource(r"\bmultiprocessing\b|\bos\.fork\s*\("),
    ),
)

_CPP = (
    Primitive(
        CanonicalText("time: a sleep"),
        RegexSource(
            r"\bsleep_(?:for|until)\s*\(|\b(?:usleep|nanosleep|clock_nanosleep)\s*\("
            + r"|(?<![\w.>:])(?:::)?sleep\s*\("
        ),
    ),
    Primitive(
        CanonicalText("time: a wait of a duration"),
        RegexSource(r"\b(?:wait|try_lock|try_acquire)_(?:for|until)\s*\("),
    ),
    Primitive(
        CanonicalText("time: a clock read"),
        RegexSource(
            r"\b(?:steady_clock|system_clock|high_resolution_clock)::now\s*\("
            + r"|\b(?:clock_gettime|gettimeofday|timespec_get)\s*\(|\bstd::(?:time|clock)\s*\("
            + r"|(?<![\w.>:])(?:::)?time\s*\(\s*(?:nullptr|NULL|0)?\s*\)"
        ),
    ),
    Primitive(
        CanonicalText("time: a timer"),
        RegexSource(r"\b(?:alarm|setitimer|timer_create|timerfd_create)\s*\("),
    ),
    Primitive(
        CanonicalText("time: a Catch2 benchmark"), RegexSource(r"\bBENCHMARK(?:_ADVANCED)?\s*\(")
    ),
    Primitive(
        CanonicalText("thread: a std::thread or std::jthread"), RegexSource(r"\bstd::j?thread\b")
    ),
    Primitive(CanonicalText("thread: std::async"), RegexSource(r"\bstd::async\s*\(")),
    Primitive(CanonicalText("thread: a POSIX thread"), RegexSource(r"\bpthread_create\s*\(")),
    Primitive(
        CanonicalText("thread: a yield to the scheduler"),
        RegexSource(r"\bthis_thread::yield\s*\(|\bsched_yield\s*\("),
    ),
)

_RUST = (
    Primitive(CanonicalText("time: a sleep"), RegexSource(r"\bthread::sleep\s*\(")),
    Primitive(
        CanonicalText("time: a clock read"), RegexSource(r"\b(?:Instant|SystemTime)::now\s*\(")
    ),
    Primitive(
        CanonicalText("time: a wait of a duration"),
        RegexSource(r"\b(?:recv_timeout|wait_timeout|wait_timeout_while|park_timeout)\s*\("),
    ),
    Primitive(CanonicalText("time: a tokio timer"), RegexSource(r"\btokio::time::")),
    Primitive(
        CanonicalText("thread: a spawned or scoped thread"),
        RegexSource(r"\bthread::(?:spawn|scope|Builder)\b"),
    ),
    Primitive(
        CanonicalText("thread: a yield to the scheduler"), RegexSource(r"\bthread::yield_now\s*\(")
    ),
    Primitive(
        CanonicalText("thread: a spawned async task"),
        RegexSource(r"\b(?:tokio::spawn|tokio::task::spawn\w*)\b"),
    ),
    Primitive(
        ASYNC_CLIENT_ON_A_THREAD,
        RegexSource(r"\bAsyncClient::new\s*\(|(?:\.|::)build_async(?:_with_backend)?\s*\("),
    ),
)

# Each binding's wide net: words that name a clock, a timer, a wait, a thread, a
# task or a process, past the catalogue's spellings.  A word it finds that no
# catalogue site covers fails the gate until a row of
# tools/_determinism_dismissals.py dismisses it, with its reason.
_GO_NET = RegexSource(
    r"\btime\.\w+|\bsync\.\w+|\berrgroup\b|\bselect\s*\{|\bchan\b|\bruntime\.\w+"
    + r"|\bexec\.Command\w*|\bsignal\.\w+|\bb\.(?:Elapsed|ResetTimer|StartTimer|StopTimer|Loop)\b"
    + r"|\bos\.StartProcess\b|\bSetDeadline\b|\bsynctest\b"
    + r"|\bsyscall\.(?:ForkExec|StartProcess)\b"
)
_PYTHON_NET = RegexSource(
    r"\btime\b|\bthreading\.\w+|\bThread\b|\bTimer\b|\basyncio\.\w+|\bloop\.\w+|\bconcurrent\b"
    + r"|\bsubprocess\.\w+|\bPopen\b|\bsignal\.\w+|\bselect\.\w+|\bselectors\b|\bsched\b"
    + r"|\btimeit\b|\b(?:datetime\.)?(?:datetime|date)\.(?:now|utcnow|today)\b"
    + r"|\bos\.(?:times|fork\w*|utime|kill|wait\w*|getpid)\b"
    + r"|\bos\.(?:system|posix_spawnp?|spawn\w*|popen)\b"
    + r"|\bst_[amc]time\w*|\bresource\.(?!RLIMIT_AS\b|setrlimit\b)\w+|\bfaulthandler\.\w+"
    + r"|\bmark\.timeout\b|\bsettimeout\b"
    + r"|\bsleep\b|\bmonotonic\b|\bperf_counter\b|\bwait\s*\(|\bas_completed\b|\banyio\b|\btrio\b"
    + r"|\bfreezegun\b|\bqueue\.\w+|\bBarrier\b|\bCondition\b|\bSemaphore\b"
)
_CPP_NET = RegexSource(
    r"\bchrono\b|\b\w*_clock\b|\bj?thread\b|\bthis_thread::\w+|\basync\b|\bfuture\b|\bpromise\b"
    + r"|\bpackaged_task\b|\bcondition_variable\w*|\bclock\s*\(|\bfork\s*\(|\bposix_spawn\w*"
    + r"|\bpopen\s*\(|\bsystem\s*\(|\blatch\b|\bbarrier\b|\bsemaphore\b|\batomic\w*|\bpoll\s*\("
    + r"|\bselect\s*\(|\bepoll\w*|\bpthread_\w+|\bwait\w*\s*\(|\bstop_token\b|\bstop_source\b"
    + r"|\bvfork\s*\(|\btime\s*\("
)
_RUST_NET = RegexSource(
    r"\bstd::time\b|\bDuration\b|\bInstant\b|\bSystemTime\b|\bUNIX_EPOCH\b|\bthread\b"
    + r"|\bspawn\w*\b|\btokio\w*|\basync_std\b|\bsmol\b|\brayon\b|\bcrossbeam\b|\bblock_on\b"
    + r"|\bmpsc\b|\bCondvar\b|\bBarrier\b|\bpark\w*\b|\bCommand\b|\bchrono\b|\bjoin!|\bselect!"
    + r"|\bsleep\b|\belapsed\b|\bMutex\b|\bAtomic\w+"
    + r"|\blibc::(?:v?fork|posix_spawn\w*|system|popen)\b"
)


# A module declared under ``#[cfg(test)]``, by its name, whatever attributes
# follow: in line, or held in a file of its own.
_CFG_TEST_MOD_HEAD = (
    r"#\[cfg\(test\)\]\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*"
)
_CFG_TEST_MOD = re.compile(_CFG_TEST_MOD_HEAD + r"\{")
_CFG_TEST_MOD_NAMED = re.compile(_CFG_TEST_MOD_HEAD + r"[;{]")


def rust_test_modules(code: BlankedCode) -> BlankedCode:
    """Keep only the ``#[cfg(test)] mod`` blocks of blanked Rust source.

    A block runs from its opening brace to the brace that closes it, counted on
    the blanked text, so a brace in a string or a comment cannot end it early.
    Everything outside the blocks is blanked, the offsets kept.
    """
    kept = [ch if ch == "\n" else " " for ch in code]
    for match in _CFG_TEST_MOD.finditer(code):
        depth = 0
        for index in range(match.end() - 1, len(code)):
            if code[index] == "{":
                depth += 1
            elif code[index] == "}":
                depth -= 1
            kept[index] = code[index]
            if depth == 0:
                break
    return BlankedCode("".join(kept))


def rust_test_file(repo: Path, rel: RelPath) -> bool:
    """Say whether a Rust source file is test code whole.

    It is when its module, or a module above it, is declared under
    ``#[cfg(test)]``: ``src/a/b.rs`` holds module ``b``, which ``src/a.rs`` or
    ``src/a/mod.rs`` declares, and ``a`` is declared by ``src/lib.rs`` or
    ``src/main.rs``.
    """
    crate, _, inner = rel.partition("/src/")
    names = inner.removesuffix(".rs").split("/")
    for depth, name in enumerate(names):
        above = "/".join([crate, "src", *names[:depth]])
        declaring = (
            (f"{above}/lib.rs", f"{above}/main.rs")
            if depth == 0
            else (f"{above}.rs", f"{above}/mod.rs")
        )
        for path in declaring:
            try:
                text = SourceText((repo / path).read_text(encoding="utf-8"))
            except OSError, UnicodeDecodeError:
                continue
            if name in _CFG_TEST_MOD_NAMED.findall(blank_rust(text)):
                return True
    return False


def _rust_code(repo: Path, rel: RelPath, text: SourceText) -> BlankedCode:
    code = spell_rust_aliases(blank_rust(text))
    whole = "/tests/" in rel or rust_test_file(repo, rel)
    return code if whole else rust_test_modules(code)


class Binding(NamedTuple):
    """How one binding's test files are recognised, read and scanned.

    ``code`` is what the scan reads of a file in the tree at ``repo``: its
    comments and literals blanked, and every name an import or a
    using-declaration binds spelled out as the catalogue spells it.
    ``primitives`` is the catalogue, and ``net`` the wider net over the same code.
    """

    name: BindingName
    is_test: Callable[[RelPath], bool]
    code: Callable[[Path, RelPath, SourceText], BlankedCode]
    primitives: tuple[Primitive, ...]
    net: RegexSource


def _is_go_test(rel: RelPath) -> bool:
    return rel.startswith("go/") and rel.endswith("_test.go")


def _is_python_test(rel: RelPath) -> bool:
    return rel.endswith(".py") and (rel.startswith("python/tests/") or rel == "conftest.py")


def _is_cpp_test(rel: RelPath) -> bool:
    return rel.startswith("cpp/tests/") and rel.endswith((".cpp", ".hpp"))


def _is_rust_test(rel: RelPath) -> bool:
    return rel.startswith("rust/") and rel.endswith(".rs") and ("/tests/" in rel or "/src/" in rel)


def _go_code(_repo: Path, _rel: RelPath, text: SourceText) -> BlankedCode:
    return spell_go_aliases(text, blank_go(text))


# A Python test hands a child interpreter its script as a string, which the
# blanking empties; each string literal that parses as Python is read as the
# source it is, but in the gate's and the guard's tests, whose strings are fixtures.
_STRING_FIXTURES = frozenset(
    RelPath(f"python/tests/test_{n}.py") for n in ("check_test_determinism", "determinism_guard")
)
# The stand-in for an interpolated value when an f-string or a t-string is
# read as source.
_INTERPOLATED = "_"


def _is_script(tree: ast.Module | None) -> bool:
    """Say whether parsed source calls or imports anything, as a script does."""
    return tree is not None and any(
        isinstance(node, (ast.Call, ast.Import, ast.ImportFrom)) for node in ast.walk(tree)
    )


def python_child_sources(text: SourceText) -> list[SourceText]:
    """Every string literal in Python source that is a script, dedented with its rows ending at LF.

    A script parses as Python and calls or imports something, which a phrase
    that happens to parse (``"non-monotonic"``) does not.  A docstring is prose
    and is skipped; an f-string or a t-string is read with each value it
    interpolates standing as one name.  A file the parser refuses yields none.
    """
    tree = python_tree(text)
    if tree is None:
        return []
    nodes = list(ast.walk(tree))
    skipped = {
        id(node.value)
        for node in nodes
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
    }
    skipped |= {
        id(part)
        for node in nodes
        if isinstance(node, (ast.JoinedStr, ast.TemplateStr))
        for part in node.values
    }
    literals = [
        node.value
        for node in nodes
        if isinstance(node, ast.Constant)
        and isinstance(node.value, str)
        and id(node) not in skipped
    ] + [
        "".join(
            part.value
            if isinstance(part, ast.Constant) and isinstance(part.value, str)
            else _INTERPOLATED
            for part in node.values
        )
        for node in nodes
        if isinstance(node, (ast.JoinedStr, ast.TemplateStr))
    ]
    sources = [
        SourceText(textwrap.dedent(io.StringIO(literal, newline=None).read()))
        for literal in literals
    ]
    return [source for source in sources if _is_script(python_tree(source))]


def _python_code(_repo: Path, rel: RelPath, text: SourceText) -> BlankedCode:
    code = spell_python_aliases(text, blank_python(text))
    if rel in _STRING_FIXTURES:
        return code
    children = (
        spell_python_aliases(child, blank_python(child)) for child in python_child_sources(text)
    )
    return BlankedCode("\n".join([code, *children]))


def _cpp_code(_repo: Path, _rel: RelPath, text: SourceText) -> BlankedCode:
    return spell_cpp_aliases(blank_cpp(text))


BINDINGS = (
    Binding(GO, _is_go_test, _go_code, _GO, _GO_NET),
    Binding(PYTHON, _is_python_test, _python_code, _PYTHON, _PYTHON_NET),
    Binding(CPP, _is_cpp_test, _cpp_code, _CPP, _CPP_NET),
    Binding(RUST, _is_rust_test, _rust_code, _RUST, _RUST_NET),
)


def sites_in(
    code: BlankedCode, primitives: tuple[Primitive, ...]
) -> dict[CanonicalText, SiteCount]:
    """Count each primitive's sites in blanked code, omitting the ones absent."""
    counts: dict[CanonicalText, SiteCount] = {}
    for primitive in primitives:
        found = len(re.findall(primitive.pattern, code, re.MULTILINE))
        if found:
            counts[primitive.label] = SiteCount(found)
    return counts


class NetSite(NamedTuple):
    """A word the net finds in one file, and the binding whose net found it."""

    file: RelPath
    binding: BindingName
    word: NetWord


# A Python test under python/tests/, the fuzz harnesses apart, runs under the
# suite's runtime guard (tools/_determinism_guard.py), which fails a test that
# starts a process without a ``@pytest.mark.process`` reason, so a word that
# starts one there is left to the guard rather than to a row.  The guard sees only
# the suite's own process: a script there that a test runs as a child escapes both.
_GUARDED = re.compile(r"python/tests/(?!fuzz/)")
_GUARDED_START = re.compile(
    r"Popen|subprocess\.(?:Popen|call|check_call|check_output|getoutput|getstatusoutput|run)"
    + r"|os\.(?:fork|forkpty|system|popen|posix_spawnp?|spawn\w+)"
    + r"|asyncio\.create_subprocess_(?:exec|shell)|loop\.subprocess_(?:exec|shell)"
)


def net_words(binding: Binding, code: BlankedCode) -> set[NetWord]:
    """Name each word of the binding's net in blanked code that no catalogue site covers."""
    counted = [
        site.span()
        for primitive in binding.primitives
        for site in re.finditer(primitive.pattern, code, re.MULTILINE)
    ]
    return {
        NetWord(re.sub(r"\s+", "", match.group(0)))
        for match in re.finditer(binding.net, code, re.MULTILINE)
        if not any(match.start() < last and first < match.end() for first, last in counted)
    }


def judged(
    sites: list[NetSite], dismissals: Mapping[Dismissal, Prose]
) -> tuple[list[NetSite], list[Dismissal]]:
    """Split the net's sites into those no row dismisses, and name the rows no site needs.

    A row naming a file covers the word there, a row naming none covers it in
    every file of its binding, the file's row taken first; a word left to the
    runtime guard needs neither.
    """
    used: set[Dismissal] = set()
    undismissed: list[NetSite] = []
    for site in sites:
        if _GUARDED_START.fullmatch(site.word) and _GUARDED.match(site.file):
            continue
        rows = (
            Dismissal(site.binding, site.word, site.file),
            Dismissal(site.binding, site.word, None),
        )
        row = next((row for row in rows if row in dismissals), None)
        if row is None:
            undismissed.append(site)
        else:
            used.add(row)
    unused = [row for row in dismissals if row not in used]
    return undismissed, sorted(unused, key=lambda row: (row.binding, row.word, row.file or ""))


def as_dismissal(site: NetSite) -> Prose:
    """Render the row that would dismiss a site in its file, so a diagnostic can be pasted."""
    return Prose(
        f"    Dismissal({site.binding.upper()}, NetWord({site.word!r}), RelPath({site.file!r})):"
        + ' Prose("<why it reads no physical time and starts nothing, or why the claim'
        + ' needs the process it starts>"),'
    )


def is_test(rel: RelPath) -> bool:
    """Say whether a repository path is a test file of any binding."""
    return any(binding.is_test(rel) for binding in BINDINGS)


def which_are_tests(repo: Path, rels: list[RelPath]) -> list[RelPath]:
    """Name the paths that are a test file, or a directory holding a tracked one."""
    tracked: list[RelPath] | None = None
    named: list[RelPath] = []
    for rel in rels:
        if is_test(rel):
            named.append(rel)
        elif (repo / rel).is_dir() and rel not in {"", "."}:
            tracked = git_ls_files(repo) if tracked is None else tracked
            if any(is_test(path) for path in tracked if path.startswith(f"{rel}/")):
                named.append(rel)
    return named


class Scan(NamedTuple):
    """What the gate reads of test files: the catalogue's rows and the net's sites."""

    rows: RatchetRows
    sites: list[NetSite]
    unreadable: tuple[Prose, ...] = ()


def scan_of(repo: Path, rel: RelPath, text: SourceText) -> Scan:
    """Read one file's text, as the path it stands for, for its rows and its net sites."""
    rows: RatchetRows = {}
    sites: list[NetSite] = []
    for binding in BINDINGS:
        if binding.is_test(rel):
            code = binding.code(repo, rel, text)
            for label, count in sites_in(code, binding.primitives).items():
                rows[RowKey(rel, label)] = count
            sites += [NetSite(rel, binding.name, word) for word in sorted(net_words(binding, code))]
    if _is_python_test(rel):
        for label, count in (
            (ASYNC_CLIENT_ON_A_THREAD, async_clients_on_a_thread(text)),
            (UNSEEDED_PROPERTY, unseeded_properties(text)),
            (REPLAYING_PROFILE, replaying_profiles(text)),
        ):
            if count:
                rows[RowKey(rel, label)] = count
    return Scan(rows, sites)


def rows_of(repo: Path, rel: RelPath, text: SourceText) -> RatchetRows:
    """Count the time and thread primitives one file's text uses, read as the path it stands for."""
    return scan_of(repo, rel, text).rows


def scan_tree(repo: Path) -> Scan:
    """Read every test file of the tree for its rows and its net sites, naming each unread."""
    rows: RatchetRows = {}
    sites: list[NetSite] = []
    unreadable: list[Prose] = []
    for rel in git_ls_files(repo):
        path = repo / rel
        if is_test(rel) and path.is_file():
            try:
                text = SourceText(path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError) as exc:
                unreadable.append(Prose(f"{rel}: cannot be read: {exc}"))
                continue
            scan = scan_of(repo, rel, text)
            rows |= scan.rows
            sites += scan.sites
    return Scan(rows, sites, tuple(unreadable))


def report(
    observed: RatchetRows, recorded: RatchetRows, *, file: RelPath | None = None
) -> ExitStatus:
    """Print every unrecorded site and every stale row; return the process exit code.

    ``file`` narrows the comparison to that file, and to sites the record does
    not allow: a row the file under edit holds fewer of is the change the record
    follows, and the tree's run holds it to the record.
    """
    unrecorded = sorted(key for key, n in observed.items() if n > recorded.get(key, 0))
    stale = (
        []
        if file is not None
        else sorted(key for key, n in recorded.items() if n > observed.get(key, 0))
    )
    if file is not None:
        unrecorded = [key for key in unrecorded if key.file == file]
    for path, label in unrecorded:
        emit(f"{path}: a test uses time, a thread or an unseeded sample the record does not allow")
        emit(f"    {label}")
        emit("  Inject the clock or the scheduler and drive it, or seed the sample")
        emit("  (AGENTS.md § Universal Rules),")
        emit(f"  or, with user approval, add this row to {RECORD}:")
        emit(as_row(path, label, observed[RowKey(path, label)]))
    for path, label in stale:
        emit(f"{path}: a recorded row names more sites than the file holds")
        emit(f"    {label}")
        emit(f"  Its sites were rewritten: drop the row from {RECORD}, or lower its count to")
        emit(f"  {observed.get(RowKey(path, label), 0)}, in the change that rewrote them.")
    if unrecorded or stale:
        emit(f"{len(unrecorded)} unrecorded, {len(stale)} stale")
        return OUT_OF_STEP
    emit(
        f"time, thread and sample primitives in tests: {sum(observed.values())}, every one recorded"
    )
    return CLEAN


def net_report(
    sites: list[NetSite], dismissals: Mapping[Dismissal, Prose], *, whole: bool
) -> ExitStatus:
    """Print every net site no row dismisses and, over the ``whole`` tree, every row no site needs.

    A row no site needs is standing permission past what the tests spell, so the
    tree's run refuses it; one file under edit is held only to the words it spells.
    """
    undismissed, unused = judged(sites, dismissals)
    if not whole:
        unused = []
    for site in undismissed:
        emit(f"{site.file}: a test names {site.word!r}, which the catalogue does not count")
        emit("  and no row dismisses.  Inject the clock or the scheduler and drive it, or drop")
        emit("  the process (AGENTS.md § Universal Rules); or, with user approval, dismiss it")
        emit(f"  in {_DISMISSALS} with the reason it reads no physical time and starts")
        emit("  nothing, or the reason the test's claim needs the process it starts:")
        emit(as_dismissal(site))
    for row in unused:
        where = f" in {row.file}" if row.file is not None else ""
        emit(f"{_DISMISSALS}: a dismissed row no site needs: {row.binding} {row.word!r}{where}")
        emit("  Drop it: no test spells the word where another row or the runtime guard")
        emit("  does not already cover it.")
    if undismissed or unused:
        emit(f"{len(undismissed)} undismissed, {len(unused)} unused dismissals")
        return OUT_OF_STEP
    words = {site.word for site in sites}
    emit(f"net sites the catalogue does not count: {len(sites)} of {len(words)} words, all held")
    return CLEAN


class _Arguments(NamedTuple):
    """The command line: one file and the path it stands for, or a path to classify."""

    file: Path | None
    rel: RelPath | None
    classify: list[RelPath]


def _parsed() -> _Arguments:
    """Read the command line."""
    parser = argparse.ArgumentParser(description="Hold the tests' time and threads to the record.")
    _ = parser.add_argument("--file", type=Path, help="read this file in place of the tree")
    _ = parser.add_argument("--as", dest="rel", help="the repository path --file stands for")
    _ = parser.add_argument(
        "--is-test",
        dest="classify",
        nargs="+",
        type=PurePosixPath,
        default=[],
        help="print the paths that are tests",
    )
    arguments = parser.parse_args()
    # argparse hands the values over untyped; each is narrowed where it is read.
    rel = arguments.rel
    return _Arguments(
        cast("Path | None", arguments.file),
        RelPath(PurePosixPath(rel).as_posix()) if isinstance(rel, str) else None,
        [RelPath(each.as_posix()) for each in cast("list[PurePosixPath]", arguments.classify)],
    )


# A value cargo's ``[env]`` table sets, and the parts of its configuration read here.
CargoEnvValue = NewType("CargoEnvValue", str)


class _ForcedCargoEnv(TypedDict, total=False):
    value: CargoEnvValue
    force: bool


class _CargoEnv(TypedDict, total=False):
    RUST_TEST_THREADS: CargoEnvValue | _ForcedCargoEnv


class _CargoConfig(TypedDict, total=False):
    env: _CargoEnv


def rust_tests_run_alone(repo: Path) -> bool:
    """Say whether cargo's configuration forces one test thread on every Rust test binary."""
    try:
        text = (repo / RUST_CARGO_CONFIG).read_text(encoding="utf-8")
        config = cast("_CargoConfig", tomllib.loads(text))
    except OSError, tomllib.TOMLDecodeError:
        return False
    return config.get("env", {}).get("RUST_TEST_THREADS") == {"value": "1", "force": True}


def rust_harness_report(repo: Path) -> ExitStatus:
    """Print why the Rust harness may run tests side by side, if it may; return the exit code."""
    if rust_tests_run_alone(repo):
        return CLEAN
    emit(f"{RUST_CARGO_CONFIG}: the Rust test binaries may run their tests side by side")
    emit('  Set [env] RUST_TEST_THREADS = { value = "1", force = true } there,')
    emit("  so each runs its tests one at a time.")
    return OUT_OF_STEP


def main() -> ExitStatus:
    """Compare the tests' time and thread primitives, or one file's, against the record."""
    arguments = _parsed()
    repo = git_toplevel()
    if arguments.classify:
        named = which_are_tests(repo, arguments.classify)
        for rel in named:
            emit(rel)
        return CLEAN if named else OUT_OF_STEP
    if (arguments.file is None) != (arguments.rel is None):
        emit("--file and --as go together: a file, and the repository path it stands for")
        return UNREADABLE
    recorded = read_ratchet_rows(repo, RECORD, "sites")
    if isinstance(recorded, str):
        emit(recorded)
        return UNREADABLE
    if arguments.file is not None and arguments.rel is not None:
        try:
            text = SourceText(arguments.file.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError) as exc:
            emit(f"{arguments.file}: cannot be read: {exc}")
            return UNREADABLE
        scan = scan_of(repo, arguments.rel, text)
        return max(
            report(scan.rows, recorded, file=arguments.rel),
            net_report(scan.sites, DISMISSED, whole=False),
        )
    return tree_report(repo, recorded)


def tree_report(repo: Path, recorded: RatchetRows) -> ExitStatus:
    """Hold the tree's tests to the record and the dismissals, unless a test could not be read."""
    scan = scan_tree(repo)
    for line in scan.unreadable:
        emit(line)
    if scan.unreadable:
        return UNREADABLE
    return max(
        report(scan.rows, recorded),
        net_report(scan.sites, DISMISSED, whole=True),
        rust_harness_report(repo),
    )


if __name__ == "__main__":
    sys.exit(main())
