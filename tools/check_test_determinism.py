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
site.

Rows are keyed by file and by the primitive's label, the kind first (``time:``
or ``thread:``), with how many sites the file holds.

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
import io
import re
import sys
import tokenize
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, NamedTuple, NewType, cast

from tools._common import RelPath, emit, git_ls_files, git_toplevel
from tools._ratchet import CanonicalText, RatchetRows, RowKey, as_row, read_ratchet_rows
from tools.check_cpp_index_loops import blank_noncode

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Callable

RECORD = Path("docs/TEST_DETERMINISM.yaml")
CLEAN, OUT_OF_STEP, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)

# A test file's text as read, and the same text with its comments and literals
# blanked to spaces, every offset and newline kept: only the second is scanned.
SourceText = NewType("SourceText", str)
BlankedCode = NewType("BlankedCode", str)
# A regular expression's source, compiled where it is matched.
RegexSource = NewType("RegexSource", str)
# How many sites of one primitive a file holds.
SiteCount = NewType("SiteCount", int)


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
)

_PYTHON = (
    Primitive(
        CanonicalText("time: a clock or sleep from module time"),
        RegexSource(r"\btime\.(?:sleep|monotonic|perf_counter|time)(?:_ns)?\s*\("),
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
        RegexSource(r"\bdatetime\.(?:datetime\.)?(?:now|utcnow|today)\s*\("),
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
    Primitive(CanonicalText("time: a sleep"), RegexSource(r"\bsleep_(?:for|until)\s*\(")),
    Primitive(
        CanonicalText("time: a wait of a duration"),
        RegexSource(r"\b(?:wait|try_lock|try_acquire)_(?:for|until)\s*\("),
    ),
    Primitive(
        CanonicalText("time: a clock read"),
        RegexSource(r"\b(?:steady_clock|system_clock|high_resolution_clock)::now\s*\("),
    ),
    Primitive(
        CanonicalText("thread: a std::thread or std::jthread"), RegexSource(r"\bstd::j?thread\b")
    ),
    Primitive(CanonicalText("thread: std::async"), RegexSource(r"\bstd::async\s*\(")),
    Primitive(CanonicalText("thread: a POSIX thread"), RegexSource(r"\bpthread_create\s*\(")),
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


def _blank_rust_file(rel: RelPath, text: SourceText) -> BlankedCode:
    code = blank_rust(text)
    return code if "/tests/" in rel else rust_test_modules(code)


class Binding(NamedTuple):
    """How one binding's test files are recognised, blanked and scanned."""

    is_test: Callable[[RelPath], bool]
    blank: Callable[[RelPath, SourceText], BlankedCode]
    primitives: tuple[Primitive, ...]


def _is_go_test(rel: RelPath) -> bool:
    return rel.startswith("go/") and rel.endswith("_test.go")


def _is_python_test(rel: RelPath) -> bool:
    return rel.endswith(".py") and (rel.startswith("python/tests/") or rel == "conftest.py")


def _is_cpp_test(rel: RelPath) -> bool:
    return rel.startswith("cpp/tests/") and rel.endswith((".cpp", ".hpp"))


def _is_rust_test(rel: RelPath) -> bool:
    return rel.startswith("rust/") and rel.endswith(".rs") and ("/tests/" in rel or "/src/" in rel)


def _blank_go_file(_rel: RelPath, text: SourceText) -> BlankedCode:
    return blank_go(text)


def _blank_python_file(_rel: RelPath, text: SourceText) -> BlankedCode:
    return blank_python(text)


def _blank_cpp_file(_rel: RelPath, text: SourceText) -> BlankedCode:
    return blank_cpp(text)


BINDINGS = (
    Binding(_is_go_test, _blank_go_file, _GO),
    Binding(_is_python_test, _blank_python_file, _PYTHON),
    Binding(_is_cpp_test, _blank_cpp_file, _CPP),
    Binding(_is_rust_test, _blank_rust_file, _RUST),
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
            for label, count in sites_in(binding.blank(rel, text), binding.primitives).items():
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
        emit(f"{path}: a test uses physical time or a thread the record does not allow")
        emit(f"    {label}")
        emit("  Inject the clock or the scheduler and drive it (AGENTS.md § Universal Rules),")
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
    emit(f"time and thread primitives in tests: {sum(observed.values())}, every one recorded")
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
    return report(observed_rows(repo), recorded)


if __name__ == "__main__":
    sys.exit(main())
