# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What the determinism gate reads of a test file: its code, blanked and spelled out.

``tools/check_test_determinism.py`` scans each test file's code, never its
prose: comments and literals are blanked to spaces with every offset and
newline kept, and every name an import, a ``use`` or a using-declaration binds
is spelled out as the qualified name the gate's catalogue spells, so no
spelling of an import hides a site.  This module is that reading, per binding.
"""

from __future__ import annotations

import ast
import io
import re
import tokenize
import warnings
from typing import NewType

from tools._determinism_syntax import BoundName, DottedName, SourceText
from tools.check_cpp_index_loops import blank_noncode

# A test file's text with its comments and literals blanked to spaces, every
# offset and newline kept: only it is scanned.
BlankedCode = NewType("BlankedCode", str)


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
    sites are counted rather than hidden.  The rows end where the parser's do,
    at a line feed, a carriage return or the two together, so a line separator
    inside a string ends none.
    """
    out = [list(line) for line in io.StringIO(text, newline="").readlines()]
    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(text, newline="").readline))
    except tokenize.TokenError, SyntaxError:
        return BlankedCode(text)
    blanked = {tokenize.COMMENT, tokenize.STRING, tokenize.FSTRING_MIDDLE, tokenize.TSTRING_MIDDLE}
    for token in tokens:
        if token.type not in blanked:
            continue
        (start_row, start_col), (end_row, end_col) = token.start, token.end
        for row in range(start_row, end_row + 1):
            line = out[row - 1]
            first = start_col if row == start_row else 0
            last = end_col if row == end_row else len(line)
            for col in range(first, last):
                if line[col] not in "\r\n":
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


def python_tree(source: SourceText) -> ast.Module | None:
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
    refuses is returned as it came.  Its rows end where the parser's do, at a
    line feed, a carriage return or the two together.
    """
    tree = python_tree(text)
    if tree is None:
        return code
    aliases = _python_aliases(tree)
    if not aliases:
        return code
    lines = io.StringIO(text, newline="").readlines()
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
