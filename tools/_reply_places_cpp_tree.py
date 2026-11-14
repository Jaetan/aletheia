# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The syntax tree the reply-place gate reads the C++ binding's reader code through.

libclang, the C interface of the Clang 23 toolchain the C++ binding is built
with, parses a file as clang-23 compiles it.  The gate loads it from the path
the toolchain's ``libclang1-23`` package installs it at, and where nothing loads
from there it exits 2 naming that path, since a gate passing over the C++
binding would hold nothing of it.  The flags a file is compiled with are in
the compile database the configure of ``cpp/build`` writes, and
``compile_commands`` exits 2 naming its path where that tree has none; a file
the database names no command for, a header, is parsed with
``cpp/src/client.cpp``'s.

``parse_unit`` parses a file once and copies the cursors of its own text into
``CppNode`` values, so that no libclang object passes this module: a node's
kind, name, extent, the declaration it references and its parts.  The module
holds what the C++ reader asks of them: a function found by name, a node's
lines and code, the node an implicit conversion wraps, a C++ string literal
read through its escapes, and each line the compiler refuses, which the reader
reports rather than reads past.
"""

from __future__ import annotations

import io
import json
import re
import shlex
import sys
import unicodedata
from bisect import bisect_left
from ctypes import CDLL
from dataclasses import dataclass
from functools import cache, lru_cache
from pathlib import Path
from typing import TYPE_CHECKING, NewType, Protocol, TypedDict, cast

from tools._reply_places import (
    REPO_ROOT,
    CodePoint,
    CppLine,
    CppSymbol,
    CppText,
    LiteralText,
    read_text,
    scalar,
)
from tools._vendor.clang.cindex import (
    Config,
    Cursor,
    CursorKind,
    Diagnostic,
    Index,
    SourceLocation,
    SourceRange,
    TokenKind,
    TranslationUnit,
)

if TYPE_CHECKING:
    from collections.abc import Iterator

    from aletheia.common_types import Prose

# The libclang of the Clang 23 toolchain, at the path its libclang1-23 package installs.
LIBCLANG = Path("/usr/lib/llvm-23/lib/libclang-23.so.23")
# The compile database the configure of the C++ test tree writes.
COMPILE_COMMANDS = Path(__file__).resolve().parents[1] / "cpp" / "build" / "compile_commands.json"
# The file whose command a file the database names none for is parsed with.
_LIBRARY_UNIT = REPO_ROOT / "cpp" / "src" / "client.cpp"

# A file's source as libclang reads it: its UTF-8 bytes.
SourceBytes = NewType("SourceBytes", bytes)
# The index of a byte of a file's source, from 0.
SourceOffset = NewType("SourceOffset", int)
# The index of a character of a literal's text, from 0.
TextIndex = NewType("TextIndex", int)
# A file's path as libclang and the compile database spell it.
SourceName = NewType("SourceName", str)
# An argument clang is run with, and a command line of them.
ClangArgument = NewType("ClangArgument", str)
CommandLine = NewType("CommandLine", str)
# How grave a diagnostic is, as libclang ranks it.
Severity = NewType("Severity", int)
# Where a declaration stands: its file and the offset of its name.
type DeclKey = tuple[SourceName, SourceOffset]


class _CompileCommand(TypedDict, total=False):
    """An entry of the compile database: a file and the command compiling it."""

    file: SourceName
    command: CommandLine
    arguments: list[ClangArgument]


class _Token(Protocol):
    """A libclang token, as this module reads it."""

    @property
    def kind(self) -> TokenKind:
        """Whether the token is a comment, a literal, a name, a keyword or punctuation."""
        ...

    @property
    def spelling(self) -> CppText:
        """The token's text."""
        ...

    @property
    def extent(self) -> SourceRange:
        """The bytes the token spans."""
        ...


class _Diagnostic(Protocol):
    """A libclang diagnostic, as this module reads it."""

    @property
    def severity(self) -> Severity:
        """How grave the diagnostic is."""
        ...

    @property
    def location(self) -> SourceLocation:
        """Where the diagnostic stands."""
        ...

    @property
    def spelling(self) -> Prose:
        """The compiler's message."""
        ...


def libclang() -> Path:
    """Return the path libclang loads from, exiting with code 2 where it does not load."""
    try:
        _ = CDLL(LIBCLANG)
    except OSError as refused:
        _ = sys.stderr.write(
            f"check-limits-parity: libclang does not load from {LIBCLANG}: {refused}"
            + "; the Clang 23 toolchain's libclang1-23 package installs it\n"
        )
        sys.exit(2)
    return LIBCLANG


def compile_commands() -> Path:
    """Return the path of the C++ test tree's compile database, exiting with code 2 where absent."""
    if not COMPILE_COMMANDS.is_file():
        _ = sys.stderr.write(
            f"check-limits-parity: {COMPILE_COMMANDS} is missing;"
            + " configure cpp/build, which writes it\n"
        )
        sys.exit(2)
    return COMPILE_COMMANDS


def _command_arguments(entry: _CompileCommand) -> list[ClangArgument]:
    """Return the arguments an entry compiles its file with, its compiler, output and file aside."""
    written = entry.get("arguments") or [
        ClangArgument(word) for word in shlex.split(entry.get("command", ""))
    ]
    kept: list[ClangArgument] = []
    output = False
    for word in written[1:]:
        if output:
            output = False
        elif word == "-o":
            output = True
        elif word not in {"-c", entry.get("file")}:
            kept.append(word)
    return kept


def compile_arguments(path: Path) -> tuple[ClangArgument, ...]:
    """Return the arguments the compile database compiles ``path`` with.

    A file it names no command for, a header, is parsed with
    ``cpp/src/client.cpp``'s, libclang reading a ``.hpp`` file as a header by
    its name; where the database names neither, the gate exits 2.
    """
    database = compile_commands()
    entries = cast("list[_CompileCommand]", json.loads(database.read_text(encoding="utf-8")))
    commands = {Path(entry.get("file", "")): entry for entry in entries}
    command = commands.get(path) or commands.get(_LIBRARY_UNIT)
    if command is None:
        _ = sys.stderr.write(
            f"check-limits-parity: {database} names no command for {_LIBRARY_UNIT},"
            + f" whose flags {path} is parsed with\n"
        )
        sys.exit(2)
    return tuple(_command_arguments(command))


@cache
def _index(library: Path) -> Index:
    """Return the index every file is parsed into, libclang loaded from ``library``."""
    if not Config.loaded:
        Config.set_library_file(library)
    return Index.create()


@dataclass(frozen=True)
class CppDecl:
    """A declaration a node references: its kind, its name, where it stands, its scope's name."""

    kind: CursorKind
    name: CppSymbol
    key: DeclKey
    scope: CppSymbol


@dataclass(frozen=True)
class CppSpan:
    """The bytes a node spans, from ``start`` up to ``end``, and its first and last lines."""

    start: SourceOffset
    end: SourceOffset
    first: CppLine
    last: CppLine


@dataclass(frozen=True)
class CppSite:
    """Where libclang locates a node, a declaration's name: the key a reference names, its line."""

    key: DeclKey
    line: CppLine


@dataclass(frozen=True, eq=False)
class CppNode:
    """A cursor of a file's own text: its kind, its name, where it stands, its parts.

    ``referenced`` is the declaration a reference names, or a declaration's
    definition; ``arguments`` are the parts a call passes, in source order.
    """

    kind: CursorKind
    name: CppSymbol
    span: CppSpan
    site: CppSite
    referenced: CppDecl | None
    parts: tuple[CppNode, ...]
    arguments: tuple[CppNode, ...]

    @property
    def start(self) -> SourceOffset:
        """The offset of the node's first byte."""
        return self.span.start

    @property
    def end(self) -> SourceOffset:
        """The offset past the node's last byte."""
        return self.span.end

    @property
    def first(self) -> CppLine:
        """The line the node starts on."""
        return self.span.first

    @property
    def last(self) -> CppLine:
        """The line the node ends on."""
        return self.span.last

    @property
    def key(self) -> DeclKey:
        """Where the node stands, which a reference to it names."""
        return self.site.key

    @property
    def line(self) -> CppLine:
        """The line libclang locates the node on."""
        return self.site.line

    @property
    def definition(self) -> bool:
        """Whether the node is a declaration that defines what it declares."""
        return self.referenced is not None and self.referenced.key == self.key


@dataclass(frozen=True)
class CppToken:
    """A token of a file's own text, not a comment: its kind, its text, its bytes and its line."""

    kind: TokenKind
    text: CppText
    start: SourceOffset
    end: SourceOffset
    line: CppLine


@dataclass(frozen=True)
class CppBreak:
    """A line the compiler refuses: its file, its number, its code and the compiler's message."""

    path: Path
    line: CppLine
    shown: CppText
    message: Prose


@dataclass(frozen=True, eq=False)
class CppUnit:
    """A file parsed once: its source, each line with its comments blanked, its nodes and tokens.

    ``nodes`` lists every node of the file's own text in source order,
    ``broken`` each error the compiler reports parsing it, wherever it stands.
    """

    path: Path
    source: SourceBytes
    shown: tuple[CppText, ...]
    nodes: tuple[CppNode, ...]
    tokens: tuple[CppToken, ...]
    broken: tuple[CppBreak, ...]

    def text(self, node: CppNode) -> CppText:
        """Return a node's text as the file writes it."""
        return CppText(self.source[node.start : node.end].decode("utf-8"))

    def line_code(self, line: CppLine) -> CppText:
        """Return a line of the file, each comment blanked, as a refusal shows it."""
        return CppText(self.shown[line - 1].strip())

    def code(self, start: SourceOffset, end: SourceOffset) -> CppText:
        """Return the code between two offsets, each comment blanked."""
        return CppText("".join(self.shown).encode("utf-8")[start:end].decode("utf-8"))

    def tokens_of(self, node: CppNode) -> list[CppToken]:
        """Return the tokens a node spans, in source order."""
        first = bisect_left(self.tokens, node.start, key=lambda token: token.start)
        last = bisect_left(self.tokens, node.end, key=lambda token: token.start)
        return list(self.tokens[first:last])

    def tokens_on(self, line: CppLine) -> list[CppToken]:
        """Return the tokens on a line, in source order."""
        first = bisect_left(self.tokens, line, key=lambda token: token.line)
        last = bisect_left(self.tokens, line + 1, key=lambda token: token.line)
        return list(self.tokens[first:last])

    def of_kind(self, kind: CursorKind) -> list[CppNode]:
        """Return the file's nodes of ``kind``, in source order."""
        return [node for node in self.nodes if node.kind == kind]


def walk(node: CppNode) -> Iterator[CppNode]:
    """Yield ``node`` and every node under it, in source order."""
    stack = [node]
    while stack:
        current = stack.pop()
        yield current
        stack.extend(reversed(current.parts))


def node_lines(node: CppNode) -> range:
    """Return the lines a node spans."""
    return range(node.first, node.last + 1)


def _file_name(location: SourceLocation) -> SourceName | None:
    """Return the path of the file a location stands in, None where it stands in none."""
    file = location.file
    return None if file is None else SourceName(str(file))


def _decl(cursor: Cursor | None) -> CppDecl | None:
    """Return the declaration a cursor names, None for none."""
    if cursor is None:
        return None
    scope = cursor.semantic_parent
    return CppDecl(
        cursor.kind,
        CppSymbol(cursor.spelling),
        (_file_name(cursor.location) or SourceName(""), SourceOffset(cursor.location.offset)),
        CppSymbol("" if scope is None else scope.spelling),
    )


def _node(cursor: Cursor, own: SourceName) -> CppNode:
    """Return a cursor of a file's own text as a node, its parts in that text with it."""
    parts = tuple(
        _node(part, own) for part in cursor.get_children() if _file_name(part.extent.start) == own
    )
    passed = {
        (argument.extent.start.offset, argument.extent.end.offset)
        for argument in cursor.get_arguments()
        if argument is not None
    }
    extent, location = cursor.extent, cursor.location
    return CppNode(
        cursor.kind,
        CppSymbol(cursor.spelling),
        CppSpan(
            SourceOffset(extent.start.offset),
            SourceOffset(extent.end.offset),
            CppLine(extent.start.line),
            CppLine(extent.end.line),
        ),
        CppSite((own, SourceOffset(location.offset)), CppLine(location.line)),
        _decl(cursor.get_definition() if cursor.kind.is_declaration() else cursor.referenced),
        parts,
        tuple(
            sorted(
                (part for part in parts if (part.start, part.end) in passed),
                key=lambda part: part.start,
            )
        ),
    )


def _file_tokens(tu: TranslationUnit, name: SourceName, size: SourceOffset) -> list[_Token]:
    """Return every token of one file of a translation unit, its comments among them."""
    file = tu.get_file(name)
    whole = SourceRange.from_locations(
        SourceLocation.from_offset(tu, file, 0), SourceLocation.from_offset(tu, file, size)
    )
    return [cast("_Token", token) for token in tu.get_tokens(extent=whole)]


def _shown(source: SourceBytes, tokens: list[_Token]) -> tuple[CppText, ...]:
    """Return a file's lines, each with its end, every comment blanked to its line ends.

    A line ends where libclang ends one, at a line feed, a carriage return or the
    two together, and the end of the file closes one more after a last line end,
    so every line libclang names has its own text.
    """
    shown = bytearray(source)
    for token in tokens:
        if token.kind == TokenKind.COMMENT:
            for at in range(token.extent.start.offset, token.extent.end.offset):
                if shown[at] not in b"\r\n":
                    shown[at] = ord(" ")
    lines = io.StringIO(bytes(shown).decode("utf-8"), newline="").readlines()
    if not lines or lines[-1].endswith(("\r", "\n")):
        lines.append("")
    return tuple(map(CppText, lines))


def _broken(
    tu: TranslationUnit, texts: dict[Path, CppText], own: Path, shown: tuple[CppText, ...]
) -> tuple[CppBreak, ...]:
    """Return each error the compiler reports, at the line of the file it stands in."""
    broken: list[CppBreak] = []
    for each in tu.diagnostics:
        diagnostic = cast("_Diagnostic", each)
        if diagnostic.severity < Diagnostic.Error:
            continue
        name = _file_name(diagnostic.location)
        path = own if name is None else Path(name)
        line = CppLine(max(diagnostic.location.line, 1))
        lines = shown
        if path != own:
            text = texts.get(path) or CppText(path.read_text(encoding="utf-8", newline=""))
            source = SourceBytes(text.encode("utf-8"))
            tokens = _file_tokens(tu, SourceName(str(path)), SourceOffset(len(source)))
            lines = _shown(source, tokens)
        code = CppText(lines[line - 1].strip())
        broken.append(CppBreak(path, line, code, diagnostic.spelling))
    return tuple(broken)


@lru_cache(maxsize=32)
def parse_unit(
    library: Path,
    path: Path,
    arguments: tuple[ClangArgument, ...],
    texts: tuple[tuple[Path, CppText], ...],
) -> CppUnit:
    """Return ``path`` parsed once by ``library`` with ``arguments``, ``texts`` read as given."""
    given = dict(texts)
    own = SourceName(str(path))
    source = SourceBytes(given[path].encode("utf-8"))
    tu = TranslationUnit.from_source(
        own,
        args=list(arguments),
        unsaved_files=[(str(each), text) for each, text in texts],
        index=_index(library),
    )
    root = tu.cursor
    top: list[CppNode] = []
    if root is not None:
        top = [
            _node(cursor, own)
            for cursor in root.get_children()
            if _file_name(cursor.extent.start) == own
        ]
    every = _file_tokens(tu, own, SourceOffset(len(source)))
    shown = _shown(source, every)
    return CppUnit(
        path,
        source,
        shown,
        tuple(node for each in top for node in walk(each)),
        tuple(
            CppToken(
                token.kind,
                token.spelling,
                SourceOffset(token.extent.start.offset),
                SourceOffset(token.extent.end.offset),
                CppLine(token.extent.start.line),
            )
            for token in every
            if token.kind != TokenKind.COMMENT
        ),
        _broken(tu, given, path, shown),
    )


def defined(unit: CppUnit | None, kind: CursorKind, name: CppSymbol) -> list[CppNode]:
    """Return each definition of ``kind`` a file's own text gives ``name``, in source order."""
    if unit is None:
        return []
    return [node for node in unit.of_kind(kind) if node.name == name and node.definition]


def cpp_function(unit: CppUnit | None, name: CppSymbol) -> CppNode | None:
    """Return a file's first definition of a function, or None when it defines none."""
    return next(iter(defined(unit, CursorKind.FUNCTION_DECL, name)), None)


def cpp_function_lines(unit: CppUnit | None, name: CppSymbol) -> frozenset[CppLine]:
    """Return the lines a function's definition spans, none when the file does not define it."""
    function = cpp_function(unit, name)
    return frozenset() if function is None else frozenset(map(CppLine, node_lines(function)))


def bare(node: CppNode) -> CppNode:
    """Return the node an implicit conversion wraps: its one part spanning the same code."""
    while len(node.parts) == 1 and (node.parts[0].start, node.parts[0].end) == (
        node.start,
        node.end,
    ):
        node = node.parts[0]
    return node


# What each simple escape reads as, the digits each numeric escape takes, and
# the greatest code a narrow escape names a character with.
_SIMPLE = dict(zip("'\"?\\abfnrtv", "'\"?\\\a\b\f\n\r\t\v", strict=True))
_OCTAL = re.compile(r"(?P<digits>[0-7]{1,3})|o\{(?P<braced>[0-7]+)\}")
_HEX = re.compile(r"x(?:\{(?P<braced>[0-9A-Fa-f]+)\}|(?P<digits>[0-9A-Fa-f]+))")
_UNIVERSAL = re.compile(
    r"u(?:\{(?P<braced>[0-9A-Fa-f]+)\}|(?P<four>[0-9A-Fa-f]{4}))|U(?P<eight>[0-9A-Fa-f]{8})"
)
_NAMED = re.compile(r"N\{(?P<name>[^}]+)\}")
_MAX_ASCII = 0x7F
# A string literal's token: its encoding prefix, then its raw delimiter and
# text or its escaped text, then its suffix.
_RAW = re.compile(
    r'(?:u8|[uUL])?R"(?P<delimiter>[^()\\\s"]{0,16})\((?P<text>.*)\)(?P=delimiter)"\w*', re.DOTALL
)
_COOKED = re.compile(r'(?:u8|[uUL])?"(?P<text>(?:[^"\\\n]|\\.)*)"\w*', re.DOTALL)


def _narrow(code: CodePoint) -> LiteralText | None:
    """Return the character a numeric escape names, None for a code past ASCII."""
    return LiteralText(chr(code)) if code <= _MAX_ASCII else None


def _character(name: CppText) -> LiteralText | None:
    """Return the character a named escape names, None for a name Unicode does not give one."""
    try:
        return LiteralText(unicodedata.lookup(name))
    except KeyError:
        return None


def _escape(text: CppText) -> tuple[LiteralText | None, TextIndex]:
    """Return what the escape ``text`` opens with reads as, None for none, and its length.

    ``text`` starts past the backslash.
    """
    read: LiteralText | None = None
    length = 1
    if text[:1] in _SIMPLE:
        read = LiteralText(_SIMPLE[text[0]])
    elif octal := _OCTAL.match(text):
        read = _narrow(CodePoint(int(octal["digits"] or octal["braced"], 8)))
        length = octal.end()
    elif hexadecimal := _HEX.match(text):
        read = _narrow(CodePoint(int(hexadecimal["braced"] or hexadecimal["digits"], 16)))
        length = hexadecimal.end()
    elif universal := _UNIVERSAL.match(text):
        digits = universal["braced"] or universal["four"] or universal["eight"]
        read = scalar(CodePoint(int(digits, 16)))
        length = universal.end()
    elif named := _NAMED.match(text):
        read = _character(CppText(named["name"]))
        length = named.end()
    return read, TextIndex(length)


def _cooked(text: CppText) -> LiteralText | None:
    """Return the text a literal's escaped text reads as, None when an escape reads as none."""
    read: list[LiteralText | None] = []
    at = 0
    while at < len(text):
        if text[at] != "\\":
            read.append(LiteralText(text[at]))
            at += 1
            continue
        char, length = _escape(CppText(text[at + 1 :]))
        read.append(char)
        at += 1 + length
    return read_text(read)


def string_text(written: CppText) -> LiteralText | None:
    """Return the text one string literal token holds, as the compiler reads it, or None."""
    if raw := _RAW.fullmatch(written):
        return LiteralText(raw.group("text"))
    if cooked := _COOKED.fullmatch(written):
        return _cooked(CppText(cooked.group("text")))
    return None


def literal(unit: CppUnit, node: CppNode) -> LiteralText | None:
    """Return the text a string literal holds, its tokens joined; None for no literal."""
    found = bare(node)
    if found.kind != CursorKind.STRING_LITERAL:
        return None
    return read_text(string_text(token.text) for token in unit.tokens_of(found))
