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

What is a test file, per binding: ``*_test.go`` under ``go/``; every Python file
under ``python/tests/`` and the repository's ``conftest.py``; every C++ source
under ``cpp/tests/``; every Rust file under a crate's ``tests/``, and the
``#[cfg(test)] mod`` blocks of the crates' sources.  Comments and string
literals are blanked before the scan, so a primitive named in prose is not a
site, and a name bound by an import, a ``use`` or a using-declaration is read
as the qualified name it stands for, so no spelling of an import hides one.  A
Python test's string literal that is a script, one that parses and calls or
imports something, is read as the child source it is: a test hands a child
interpreter its script that way.  The gate's own test is the exception, its
strings being the fixtures it feeds the gate.

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
clean, 1 a site or a row out of step, 2 a file or the record that cannot be read.
"""

from __future__ import annotations

import argparse
import ast
import io
import re
import sys
import textwrap
import tokenize
import tomllib
import warnings
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

from tools._common import RelPath, emit, git_ls_files, git_toplevel
from tools._determinism_syntax import (
    ASYNC_CLIENT_ON_A_THREAD,
    REPLAYING_PROFILE,
    UNSEEDED_PROPERTY,
    BoundName,
    DottedName,
    SiteCount,
    SourceText,
    async_clients_on_a_thread,
    replaying_profiles,
    unseeded_properties,
)
from tools._ratchet import CanonicalText, RatchetRows, RowKey, as_row, read_ratchet_rows
from tools.check_cpp_index_loops import blank_noncode

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Callable

RECORD = Path("docs/TEST_DETERMINISM.yaml")
# Cargo's configuration for every Rust crate, whose environment runs each test
# binary's tests one at a time; the harness otherwise runs them side by side.
RUST_CARGO_CONFIG = Path("rust/.cargo/config.toml")
CLEAN, OUT_OF_STEP, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)

# A test file's text with its comments and literals blanked to spaces, every
# offset and newline kept: only it is scanned.
BlankedCode = NewType("BlankedCode", str)
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


# Comments, string literals and rune or character literals, blanked with their
# newlines kept, so a scan never reads a primitive named in prose.
_GO_NONCODE = re.compile(
    r"//[^\n]*|/\*.*?\*/|`[^`]*`|\"(?:\\.|[^\"\\\n])*\"|'(?:\\.|[^'\\\n])+'",
    re.DOTALL,
)
_RUST_NONCODE = re.compile(
    r"//[^\n]*|/\*.*?\*/|r(#*)\".*?\"\1|b?\"(?:\\.|[^\"\\])*\"|b?'(?:\\.|[^'\\\n])'",
    re.DOTALL,
)
_CFG_TEST_MOD = re.compile(r"#\[cfg\(test\)\]\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+\w+\s*\{")


def blank_go(text: SourceText) -> BlankedCode:
    """Return Go source with its comments and literals blanked, offsets preserved."""
    return BlankedCode(_GO_NONCODE.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text))


def blank_rust(text: SourceText) -> BlankedCode:
    """Return Rust source with its comments and literals blanked, offsets preserved."""
    return BlankedCode(_RUST_NONCODE.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text))


def blank_cpp(text: SourceText) -> BlankedCode:
    """Return C++ source blanked as the index-loop gate blanks it."""
    return BlankedCode(blank_noncode(text))


def blank_python(text: SourceText) -> BlankedCode:
    """Return Python source with its comments and string literals blanked.

    Read by the tokenizer, which knows every string prefix and nesting the
    language allows; a file the tokenizer refuses is returned unblanked, so its
    sites are counted rather than hidden.
    """
    out = [list(line) for line in text.splitlines(keepends=True)]
    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(text).readline))
    except tokenize.TokenError, SyntaxError:
        return BlankedCode(text)
    blanked = {tokenize.COMMENT, tokenize.STRING, tokenize.FSTRING_MIDDLE}
    for token in tokens:
        if token.type not in blanked:
            continue
        (start_row, start_col), (end_row, end_col) = token.start, token.end
        for row in range(start_row, end_row + 1):
            line = out[row - 1]
            first = start_col if row == start_row else 0
            last = end_col if row == end_row else len(line)
            for col in range(first, last):
                if line[col] != "\n":
                    line[col] = " "
    return BlankedCode("".join("".join(line) for line in out))


# The catalogue spells a primitive qualified, as ``time.sleep`` or
# ``std::thread::spawn``; a test that names one through an import alias, a
# from-import or a using-declaration is read with that name spelled out again,
# so no spelling of an import hides a site.  The functions below rewrite the
# blanked code to the qualified spelling; the result is only counted, never
# reported, so the offsets it moves do not matter.

# A Rust path ``::``-joined, one of its segments, the text of a Rust use tree,
# and a Go package's import path.
RustPath = NewType("RustPath", str)
PathSegment = NewType("PathSegment", str)
UseTree = NewType("UseTree", str)
GoPackage = NewType("GoPackage", str)
# A character offset into a file's text, and the parser's 1-based row and
# UTF-8 byte column of a node.
CharOffset = NewType("CharOffset", int)
Row = NewType("Row", int)
ByteColumn = NewType("ByteColumn", int)

# The Python modules whose names the catalogue reads, with the names a star
# import of each brings in.
_PY_MODULES: dict[DottedName, tuple[BoundName, ...]] = {
    DottedName("time"): (
        BoundName("sleep"),
        BoundName("monotonic"),
        BoundName("perf_counter"),
        BoundName("time"),
        BoundName("process_time"),
        BoundName("thread_time"),
        BoundName("clock_gettime"),
    ),
    DottedName("datetime"): (BoundName("datetime"), BoundName("date")),
    DottedName("threading"): (BoundName("Thread"), BoundName("Timer")),
    DottedName("_thread"): (BoundName("start_new_thread"),),
    DottedName("asyncio"): (
        BoundName("sleep"),
        BoundName("timeout"),
        BoundName("timeout_at"),
        BoundName("wait_for"),
        BoundName("to_thread"),
        BoundName("create_task"),
        BoundName("gather"),
        BoundName("ensure_future"),
        BoundName("TaskGroup"),
    ),
    DottedName("concurrent.futures"): (
        BoundName("ThreadPoolExecutor"),
        BoundName("ProcessPoolExecutor"),
    ),
    DottedName("multiprocessing"): (),
    DottedName("os"): (BoundName("fork"), BoundName("sched_yield")),
    DottedName("signal"): (BoundName("alarm"), BoundName("setitimer")),
    DottedName("faulthandler"): (BoundName("dump_traceback_later"),),
}


def _watched_python(dotted: DottedName) -> bool:
    """Say whether a dotted module path is one of the modules above, inside one or above one."""
    return any(
        dotted == module or dotted.startswith(f"{module}.") or module.startswith(f"{dotted}.")
        for module in _PY_MODULES
    )


def _python_aliases(tree: ast.Module) -> dict[BoundName, DottedName]:
    """Map each name a Python file binds to a watched module or one of its members."""
    aliases: dict[BoundName, DottedName] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for name in node.names:
                if name.asname and _watched_python(DottedName(name.name)):
                    aliases[BoundName(name.asname)] = DottedName(name.name)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            module = DottedName(node.module)
            for name in node.names:
                member = DottedName(f"{module}.{name.name}")
                if name.name == "*":
                    for star in _PY_MODULES.get(module, ()):
                        aliases[star] = DottedName(f"{module}.{star}")
                elif _watched_python(module) or _watched_python(member):
                    aliases[BoundName(name.asname or name.name)] = member
    return aliases


def _python_tree(source: SourceText) -> ast.Module | None:
    """Parse Python source quietly, or None when it is not Python the parser takes."""
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", SyntaxWarning)
        try:
            return ast.parse(source)
        except SyntaxError, ValueError:
            return None


def spell_python_aliases(text: SourceText, code: BlankedCode) -> BlankedCode:
    """Spell every read of a Python import alias as the qualified name it stands for.

    The names are found by the parser, which sees only code; a file the parser
    refuses is returned as it came.
    """
    tree = _python_tree(text)
    if tree is None:
        return code
    aliases = _python_aliases(tree)
    if not aliases:
        return code
    lines = text.splitlines(keepends=True)
    starts = [CharOffset(0)]
    for line in lines:
        starts.append(CharOffset(starts[-1] + len(line)))

    def offset(row: Row, column: ByteColumn) -> CharOffset:
        """Turn the parser's row and UTF-8 column into a character offset."""
        return CharOffset(starts[row - 1] + len(lines[row - 1].encode()[:column].decode()))

    reads = sorted(
        (
            (
                offset(Row(node.lineno), ByteColumn(node.col_offset)),
                offset(Row(node.lineno), ByteColumn(node.col_offset + len(node.id.encode()))),
                aliases[BoundName(node.id)],
            )
            for node in ast.walk(tree)
            if isinstance(node, ast.Name)
            and isinstance(node.ctx, ast.Load)
            and BoundName(node.id) in aliases
        ),
        reverse=True,
    )
    spelled = str(code)
    for start, end, qualified in reads:
        spelled = spelled[:start] + qualified + spelled[end:]
    return BlankedCode(spelled)


# A Rust ``use`` declaration, whose tree never holds a semicolon, and the paths
# whose names the catalogue reads, with the names a glob import of each brings in.
_RUST_USE = re.compile(r"\buse\s+([^;]+);")
_RUST_PATHS: dict[RustPath, tuple[BoundName, ...]] = {
    RustPath("std::thread"): (
        BoundName("sleep"),
        BoundName("spawn"),
        BoundName("scope"),
        BoundName("Builder"),
        BoundName("yield_now"),
        BoundName("park_timeout"),
    ),
    RustPath("std::time"): (BoundName("Instant"), BoundName("SystemTime")),
    RustPath("core::time"): (),
    RustPath("aletheia::AsyncClient"): (),
    RustPath("crate::AsyncClient"): (),
    RustPath("tokio"): (BoundName("spawn"), BoundName("time"), BoundName("task")),
    RustPath("tokio::time"): (BoundName("sleep"), BoundName("timeout"), BoundName("interval")),
    RustPath("tokio::task"): (
        BoundName("spawn"),
        BoundName("spawn_blocking"),
        BoundName("spawn_local"),
    ),
}


def _top_level_parts(tree: UseTree) -> list[UseTree]:
    """Split a use list on the commas outside its nested braces."""
    parts: list[UseTree] = []
    depth, start = 0, CharOffset(0)
    for index, char in enumerate(tree):
        depth += {"{": 1, "}": -1}.get(char, 0)
        if char == "," and depth == 0:
            parts.append(UseTree(tree[start:index]))
            start = CharOffset(index + 1)
    parts.append(UseTree(tree[start:]))
    return [part for part in parts if part.strip()]


def _rust_use_tree(
    prefix: list[PathSegment], tree: UseTree, into: dict[BoundName, RustPath]
) -> None:
    """Bind each name a use tree brings in under a watched path to the path it names."""
    text = str(tree).strip().removeprefix("::")
    if (brace := text.find("{")) >= 0:
        head = [PathSegment(part.strip()) for part in text[:brace].split("::") if part.strip()]
        for part in _top_level_parts(UseTree(text[brace + 1 : text.rindex("}")])):
            _rust_use_tree(prefix + head, part, into)
        return
    path, alias = text, None
    if renamed := re.fullmatch(r"(.+?)\s+as\s+(\w+)", text, re.DOTALL):
        path, alias = renamed.group(1), BoundName(renamed.group(2))
    segments = prefix + [PathSegment(part.strip()) for part in path.split("::") if part.strip()]
    if segments and segments[-1] == "*":
        module = "::".join(segments[:-1])
        for member in _RUST_PATHS.get(RustPath(module), ()):
            into[member] = RustPath(f"{module}::{member}")
        return
    if segments and segments[-1] == "self":
        segments = segments[:-1]
    full = "::".join(segments)
    if segments and any(full == root or full.startswith(f"{root}::") for root in _RUST_PATHS):
        into[alias or BoundName(segments[-1])] = RustPath(full)


def spell_rust_aliases(code: BlankedCode) -> BlankedCode:
    """Spell every name a Rust ``use`` brings in from a watched path as that path."""
    names: dict[BoundName, RustPath] = {}
    for match in _RUST_USE.finditer(code):
        _rust_use_tree([], UseTree(match.group(1)), names)
    if not names:
        return code
    spelled = _RUST_USE.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), code)
    for name, path in names.items():
        spelled = re.sub(rf"(?<![\w:.]){re.escape(name)}\b", path, spelled)
    return BlankedCode(spelled)


# A Go import spec that names its package, read from the source at an offset
# the blanked code shows is code, since the blanking empties the path string.
_GO_NAMED_IMPORT = re.compile(
    r'^[ \t]*(?:import[ \t]+)?([A-Za-z_]\w*|\.)[ \t]+"(time|context|runtime)"', re.MULTILINE
)
_GO_PACKAGES: dict[GoPackage, tuple[BoundName, ...]] = {
    GoPackage("time"): tuple(
        BoundName(name)
        for name in (
            "Sleep",
            "After",
            "AfterFunc",
            "NewTimer",
            "NewTicker",
            "Tick",
            "Now",
            "Since",
            "Until",
        )
    ),
    GoPackage("context"): tuple(
        BoundName(name)
        for name in ("WithTimeout", "WithDeadline", "WithTimeoutCause", "WithDeadlineCause")
    ),
    GoPackage("runtime"): (BoundName("Gosched"),),
}


def spell_go_aliases(text: SourceText, code: BlankedCode) -> BlankedCode:
    """Spell every read through a renamed or dot import of a watched package as the package."""
    spelled = str(code)
    for match in _GO_NAMED_IMPORT.finditer(text):
        name, package = match.group(1), GoPackage(match.group(2))
        if name == "_" or code[match.start(1)] != text[match.start(1)]:
            continue
        if name == ".":
            members = "|".join(_GO_PACKAGES[package])
            spelled = re.sub(rf"(?<![\w.])({members})\s*\(", rf"{package}.\1(", spelled)
        else:
            spelled = re.sub(rf"(?<![\w.]){re.escape(name)}\.", f"{package}.", spelled)
    return BlankedCode(spelled)


# C++ names a clock, the standard namespace or a thread through an alias, a
# using-declaration or a using-directive; the lookbehind keeps a member, a
# qualified name and an ``#include <thread>`` out.
_CPP_CLOCK_ALIAS = re.compile(
    r"\busing\s+(\w+)\s*=\s*(?:::)?(?:std::)?(?:chrono::)?(\w+_clock)\s*;"
    + r"|\btypedef\s+(?:::)?(?:std::)?(?:chrono::)?(\w+_clock)\s+(\w+)\s*;"
)
_CPP_STD_ALIAS = re.compile(r"\bnamespace\s+(\w+)\s*=\s*(?:::)?std\s*;")
_CPP_USING_STD = re.compile(
    r"\busing\s+namespace\s+std\s*;|\busing\s+(?:::)?std::(j?thread|async)\s*;"
)
_CPP_UNQUALIFIED = r"(?<![\w.>:<])"


def spell_cpp_aliases(code: BlankedCode) -> BlankedCode:
    """Spell a clock alias, a standard-namespace alias and a used ``std`` name qualified."""
    spelled = str(code)
    for match in _CPP_CLOCK_ALIAS.finditer(code):
        alias, clock = match.group(1) or match.group(4), match.group(2) or match.group(3)
        spelled = re.sub(rf"{_CPP_UNQUALIFIED}{alias}::now\b", f"{clock}::now", spelled)
    for match in _CPP_STD_ALIAS.finditer(code):
        spelled = re.sub(rf"{_CPP_UNQUALIFIED}{match.group(1)}::", "std::", spelled)
    used = {match.group(1) or "*" for match in _CPP_USING_STD.finditer(code)}
    if used & {"*", "thread", "jthread"}:
        spelled = re.sub(rf"{_CPP_UNQUALIFIED}(j?thread)\b", r"std::\1", spelled)
    if used & {"*", "async"}:
        spelled = re.sub(rf"{_CPP_UNQUALIFIED}async\s*\(", "std::async(", spelled)
    return BlankedCode(spelled)


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


def _rust_code(rel: RelPath, text: SourceText) -> BlankedCode:
    code = spell_rust_aliases(blank_rust(text))
    return code if "/tests/" in rel else rust_test_modules(code)


class Binding(NamedTuple):
    """How one binding's test files are recognised, read and scanned.

    ``code`` is what the scan reads of a file: its comments and literals
    blanked, and every name an import or a using-declaration binds spelled
    out as the catalogue spells it.
    """

    is_test: Callable[[RelPath], bool]
    code: Callable[[RelPath, SourceText], BlankedCode]
    primitives: tuple[Primitive, ...]


def _is_go_test(rel: RelPath) -> bool:
    return rel.startswith("go/") and rel.endswith("_test.go")


def _is_python_test(rel: RelPath) -> bool:
    return rel.endswith(".py") and (rel.startswith("python/tests/") or rel == "conftest.py")


def _is_cpp_test(rel: RelPath) -> bool:
    return rel.startswith("cpp/tests/") and rel.endswith((".cpp", ".hpp"))


def _is_rust_test(rel: RelPath) -> bool:
    return rel.startswith("rust/") and rel.endswith(".rs") and ("/tests/" in rel or "/src/" in rel)


def _go_code(_rel: RelPath, text: SourceText) -> BlankedCode:
    return spell_go_aliases(text, blank_go(text))


# A Python test hands a child interpreter its script as a string, which the
# blanking empties; each string literal that parses as Python is read as the
# source it is.  The gate's own test is exempt: its strings are the fixtures
# it feeds the gate, and its code is read like any other test's.
_STRING_FIXTURES = RelPath("python/tests/test_check_test_determinism.py")
# The stand-in for an interpolated value when an f-string is read as source.
_INTERPOLATED = "_"


def _is_script(tree: ast.Module | None) -> bool:
    """Say whether parsed source calls or imports anything, as a script does."""
    return tree is not None and any(
        isinstance(node, (ast.Call, ast.Import, ast.ImportFrom)) for node in ast.walk(tree)
    )


def python_child_sources(text: SourceText) -> list[SourceText]:
    """Every string literal in Python source that is a script, dedented.

    A script parses as Python and calls or imports something, which a phrase
    that happens to parse (``"non-monotonic"``) does not.  A docstring is prose
    and is skipped; an f-string is read with each value it interpolates
    standing as one name.  A file the parser refuses yields none.
    """
    tree = _python_tree(text)
    if tree is None:
        return []
    nodes = list(ast.walk(tree))
    skipped = {
        id(node.value)
        for node in nodes
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
    }
    skipped |= {
        id(part) for node in nodes if isinstance(node, ast.JoinedStr) for part in node.values
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
        if isinstance(node, ast.JoinedStr)
    ]
    sources = [SourceText(textwrap.dedent(literal)) for literal in literals]
    return [source for source in sources if _is_script(_python_tree(source))]


def _python_code(rel: RelPath, text: SourceText) -> BlankedCode:
    code = spell_python_aliases(text, blank_python(text))
    if rel == _STRING_FIXTURES:
        return code
    children = (
        spell_python_aliases(child, blank_python(child)) for child in python_child_sources(text)
    )
    return BlankedCode("\n".join([code, *children]))


def _cpp_code(_rel: RelPath, text: SourceText) -> BlankedCode:
    return spell_cpp_aliases(blank_cpp(text))


BINDINGS = (
    Binding(_is_go_test, _go_code, _GO),
    Binding(_is_python_test, _python_code, _PYTHON),
    Binding(_is_cpp_test, _cpp_code, _CPP),
    Binding(_is_rust_test, _rust_code, _RUST),
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


def rows_of(rel: RelPath, text: SourceText) -> RatchetRows:
    """Count the time and thread primitives one file's text uses, read as the path it stands for."""
    rows: RatchetRows = {}
    for binding in BINDINGS:
        if binding.is_test(rel):
            for label, count in sites_in(binding.code(rel, text), binding.primitives).items():
                rows[RowKey(rel, label)] = count
    if _is_python_test(rel):
        for label, count in (
            (ASYNC_CLIENT_ON_A_THREAD, async_clients_on_a_thread(text)),
            (UNSEEDED_PROPERTY, unseeded_properties(text)),
            (REPLAYING_PROFILE, replaying_profiles(text)),
        ):
            if count:
                rows[RowKey(rel, label)] = count
    return rows


def observed_rows(repo: Path) -> RatchetRows:
    """Count every time and thread primitive the tree's test files use."""
    rows: RatchetRows = {}
    for rel in git_ls_files(repo):
        path = repo / rel
        if is_test(rel) and path.is_file():
            rows |= rows_of(rel, SourceText(path.read_text(encoding="utf-8")))
    return rows


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
        return report(rows_of(arguments.rel, text), recorded, file=arguments.rel)
    return max(report(observed_rows(repo), recorded), rust_harness_report(repo))


if __name__ == "__main__":
    sys.exit(main())
