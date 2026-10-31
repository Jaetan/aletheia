# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ reader of the reply-tags arm, ``tools/_reply_places.py``.

It reads the set the C++ binding's reply readers take at each string place of
``replyText`` from their own code: a ``std::to_array`` table of ``{word,
enumerator}`` pairs, the literals a dispatch compares a word with, the words
its ``field_word`` calls await, the words one function gives an enum's
enumerators, or the ``bound_kind_*`` codes.  A table's last entry, or the word
no comparison of a dispatch names, is the reader's last arm, which reads every
word its other arms do not name, and the arm holds it to the row's last word.
A line of a reader file that could read a tag word outside these sets, a word
compared outside the dispatches or a table no reader file declares looked up,
is reported with each set the module cannot read.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import TYPE_CHECKING

from tools._reply_places import (
    REPO_ROOT,
    AnyNonEmpty,
    Arms,
    CppLine,
    CppSymbol,
    CppText,
    ReaderSets,
    ReplyPlace,
    ReplyWord,
    UnnamedLast,
    fragment_lines,
    read_sets,
    word_literals,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterator
    from pathlib import Path

    from tools._reply_places import BindingReader

CPP_SOURCE = REPO_ROOT / "cpp" / "src"
CPP_INCLUDE = REPO_ROOT / "cpp" / "include"
CPP_PARSE = CPP_SOURCE / "json_parse.cpp"
CPP_PARSE_DBC = CPP_SOURCE / "json_parse_dbc.cpp"
CPP_REPLY_SHAPE = CPP_SOURCE / "reply_shape.cpp"
CPP_REPLY_SHAPE_HEADER = CPP_SOURCE / "detail" / "reply_shape.hpp"


@dataclass(frozen=True)
class _CppTable:
    """A ``constexpr std::to_array`` table of ``{word, enumerator}`` pairs, one per line.

    Its last entry is the reader's last arm: the table is declared once, in a
    reader file, and every other reference to it is a ``lookup`` that defaults
    to the last entry's enumerator.
    """

    module: Path
    name: CppSymbol


@dataclass(frozen=True)
class _CppDispatch:
    """The literals a function compares the word at a key with, its last arm naming none.

    The function reads the key once with ``field_string``, into a variable or
    compared where it is read, and compares the word with ``==`` to literals
    only; what it does after the comparisons reads every other word.
    """

    module: Path
    function: CppSymbol
    key: ReplyWord


@dataclass(frozen=True)
class _CppWordCall:
    """The literals a function's ``field_word`` calls at a key await."""

    module: Path
    function: CppSymbol
    key: ReplyWord


@dataclass(frozen=True)
class _CppEnumWords:
    """The words one function gives the enumerators of an enum declared in a header.

    A second word for an enumerator, or its word reached outside ``reader``,
    could stand for a word the function does not give, so the gate refuses,
    where it stands, a ``case`` of the enum outside ``words``, a reference to
    ``words`` outside its declaration, its definition and ``reader``, and a
    second declaration of the enum.
    """

    header: Path
    enum: CppSymbol
    module: Path
    words: CppSymbol
    reader: CppSymbol


@dataclass(frozen=True)
class _CppBoundKinds:
    """The ``bound_kind_*`` codes of ``cpp/include/aletheia/limits.hpp``."""


type _CppSet = _CppTable | _CppDispatch | _CppWordCall | _CppEnumWords | _CppBoundKinds

# Every row of `replyText`, with the set the C++ reader takes at its place, read
# from the reader's own code, under the rules PYTHON_REPLY_TEXT is held to; a
# table's last entry, or the word no comparison of a dispatch names, is the
# row's last word.
CPP_REPLY_TEXT: dict[ReplyPlace, _CppSet | AnyNonEmpty] = {
    ReplyPlace(place): spec
    for place, spec in {
        "status": _CppEnumWords(
            CPP_REPLY_SHAPE_HEADER,
            CppSymbol("ReplyStatus"),
            CPP_REPLY_SHAPE,
            CppSymbol("status_word"),
            CppSymbol("field_status"),
        ),
        "type": _CppWordCall(CPP_PARSE, CppSymbol("parse_frame_response"), ReplyWord("type")),
        "results/type": _CppDispatch(
            CPP_PARSE, CppSymbol("read_property_event"), ReplyWord("type")
        ),
        "results/status <property>": _CppTable(CPP_PARSE, CppSymbol("verdict_table")),
        "warnings/kind": _CppDispatch(
            CPP_PARSE, CppSymbol("read_stream_warning"), ReplyWord("kind")
        ),
        "issues/severity": _CppTable(CPP_PARSE, CppSymbol("severity_table")),
        "warnings/severity": _CppTable(CPP_PARSE, CppSymbol("severity_table")),
        "bound_kind": _CppBoundKinds(),
        "dbc/messages/signals/byteOrder": _CppTable(CPP_PARSE_DBC, CppSymbol("byte_order_table")),
        "dbc/messages/signals/presence": _CppDispatch(
            CPP_PARSE_DBC, CppSymbol("read_presence"), ReplyWord("presence")
        ),
        "dbc/messages/signals/multiplexor": AnyNonEmpty(),
        "dbc/comments/target/kind": _CppDispatch(
            CPP_PARSE_DBC, CppSymbol("read_comment_target"), ReplyWord("kind")
        ),
        "dbc/attributes/kind": _CppDispatch(
            CPP_PARSE_DBC, CppSymbol("read_attribute"), ReplyWord("kind")
        ),
        "dbc/attributes/scope <definition>": _CppTable(
            CPP_PARSE_DBC, CppSymbol("attr_scope_table")
        ),
        "dbc/attributes/attrType/kind": _CppDispatch(
            CPP_PARSE_DBC, CppSymbol("read_attr_type"), ReplyWord("kind")
        ),
        "dbc/attributes/value/kind": _CppDispatch(
            CPP_PARSE_DBC, CppSymbol("read_attr_value"), ReplyWord("kind")
        ),
        "dbc/attributes/target/kind": _CppDispatch(
            CPP_PARSE_DBC, CppSymbol("read_attr_target"), ReplyWord("kind")
        ),
    }.items()
}


# A C++ raw string, string or character literal, or a comment, matched from the
# left so that a `//` inside a literal is not taken for a comment; a quote after
# a hex digit is a digit separator, not a character literal.
_CPP_TOKEN = re.compile(
    r'R"(?P<delimiter>[^()\\\s"]{0,16})\(.*?\)(?P=delimiter)"|"(?:[^"\\\n]|\\.)*"|'
    + r"(?<![0-9A-Fa-f])'(?:[^'\\\n]|\\.)*'|//[^\n]*|/\*.*?\*/",
    flags=re.DOTALL,
)
# A comparison that could read a word, in source whose literals' text is
# blanked: `==` or `!=` beside a string literal, or a `compare`, `starts_with`
# or `ends_with` call.
_CPP_WORD_COMPARISON = re.compile(
    r'[!=]=\s*(?:(?:std::)?string(?:_view)?\s*[({]\s*)?(?:u8|[LuU])?R?"|"(?:sv|s)?\s*[!=]='
    + r"|\.compare\s*\(|\b(?:starts_with|ends_with)\s*\("
)
# A `field_word` call whose arguments hold no call of their own, and those
# arguments: the object and the path, the literal key and the braced words.
_CPP_WORD_CALL = re.compile(r"\bfield_word\((?P<args>[^()]*)\)")
_CPP_WORD_CALL_ARGS = re.compile(
    r'^.*?,\s*"(?P<key>[^"\\]*)"\s*,\s*\{(?P<words>[^{}]*)\}\s*$', flags=re.DOTALL
)
# An entry of a word table, `{"word", Enum::Member},`.
_CPP_TABLE_ENTRY = re.compile(r'^\{"(?P<word>[^"\\]*)",\s*(?P<value>\w+(?:::\w+)*)\},?$')


@dataclass(frozen=True)
class _CppFile:
    """A file of the C++ library, its comments blanked, then its literals' text blanked too."""

    code: CppText
    hollow: CppText


# A line of a file of the C++ library.
type _CppSite = tuple[Path, CppLine]


def _blank(text: CppText) -> CppText:
    """Return text with every character but a line break blanked."""
    return CppText(re.sub(r"[^\n]", " ", text))


def _cpp_code(text: CppText) -> CppText:
    """Return C++ source with each comment blanked to its line breaks and its literals kept."""
    return CppText(
        _CPP_TOKEN.sub(
            lambda token: (
                _blank(CppText(token.group())) if token.group().startswith("/") else token.group()
            ),
            text,
        )
    )


def _cpp_hollow_literal(literal: CppText) -> CppText:
    """Return a literal with its text blanked: a string's inside its quotes, a character's whole."""
    if not literal.endswith('"'):
        return _blank(literal)
    opening = literal.index('"') + 1
    return CppText(literal[:opening] + _blank(CppText(literal[opening:-1])) + '"')


def _cpp_hollow(code: CppText) -> CppText:
    """Return C++ source with each literal's text blanked."""
    return CppText(_CPP_TOKEN.sub(lambda token: _cpp_hollow_literal(CppText(token.group())), code))


def _cpp_file(path: Path) -> _CppFile:
    """Return a file of the C++ library, its comments blanked."""
    code = _cpp_code(CppText(path.read_text(encoding="utf-8")))
    return _CppFile(code, _cpp_hollow(code))


def _cpp_package() -> dict[Path, _CppFile]:
    """Return every source and header of the C++ library."""
    return {
        path: _cpp_file(path)
        for root in (CPP_SOURCE, CPP_INCLUDE)
        for path in sorted(root.rglob("*"))
        if path.suffix in {".cpp", ".hpp"}
    }


def _is_cpp_reader(path: Path) -> bool:
    """Whether a file of the C++ library is a reply reader, a json_parse*.cpp or a reply_shape."""
    return path.stem == "reply_shape" or (
        path.parent == CPP_SOURCE and path.match("json_parse*.cpp")
    )


def _cpp_function(code: CppText, name: CppSymbol) -> CppText | None:
    """Return a function's definition up to the brace clang-format closes it with, or None."""
    head = rf"^(?:\[\[nodiscard\]\]\s+)?(?:static\s+)?auto\s+{re.escape(name)}\("
    for start in re.finditer(head, code, flags=re.MULTILINE):
        opening = re.compile(r"[{;]").search(code, start.end())
        if opening is not None and opening.group() == "{":
            end = code.find("\n}", opening.end())
            return CppText(code[start.start() : None if end < 0 else end])
    return None


def _cpp_function_lines(code: CppText, name: CppSymbol) -> frozenset[CppLine]:
    """Return the lines a function's definition spans, none when the file does not define it."""
    body = _cpp_function(code, name)
    return frozenset() if body is None else frozenset(map(CppLine, fragment_lines(code, body)))


def _cpp_lines(file: _CppFile) -> Iterator[tuple[CppLine, CppText, CppText]]:
    """Yield each line of a file: its number, its hollow text and its text as shown."""
    for number, (line, shown) in enumerate(
        zip(file.hollow.split("\n"), file.code.split("\n"), strict=True), start=1
    ):
        yield CppLine(number), CppText(line), CppText(shown.strip())


def _dispatch_arms(spec: _CppDispatch, body: CppText) -> Arms | Prose:
    """Return the words a function compares the word at its key with, its last arm naming none."""
    read = rf'field_string\(\s*\w+\s*,\s*\w+\s*,\s*"{re.escape(spec.key)}"\s*\)'
    reads = list(re.finditer(read, body))
    if len(reads) != 1:
        return Prose(f"reads {spec.key!r} with field_string {len(reads)} times, not once")
    held = re.search(r"\bauto\s+const\s+(?P<name>\w+)\s*=\s*\Z", body[: reads[0].start()])
    if held is None and re.match(r'\s*==\s*"', body[reads[0].end() :]) is None:
        return Prose(f"neither holds the word at {spec.key!r} nor compares it where it reads it")
    operand = read if held is None else rf"(?<![.>])\b{held.group('name')}\b"
    words = [
        ReplyWord(m.group("word"))
        for m in re.finditer(rf'{operand}\s*==\s*"(?P<word>[^"\\]*)"', body)
    ]
    hollow = _cpp_hollow(body)
    if len(_CPP_WORD_COMPARISON.findall(hollow)) != len(words):
        return Prose(f"compares a word other than the one at {spec.key!r} with == to a literal")
    if held is not None and len(re.findall(operand, hollow)) != 1 + len(words):
        return Prose(f"uses {held.group('name')} other than to compare it with a literal")
    if len(set(words)) != len(words):
        return Prose("compares the word with one literal twice")
    return Arms(frozenset(words), UnnamedLast())


def _cpp_word_call_words(body: CppText, key: ReplyWord) -> frozenset[ReplyWord] | Prose:
    """Return the words a function's ``field_word`` calls at ``key`` await."""
    calls = list(_CPP_WORD_CALL.finditer(body))
    if len(calls) != len(re.findall(r"\bfield_word\(", body)):
        return Prose("a field_word call holds a call of its own")
    words: set[ReplyWord] = set()
    for call in calls:
        args = _CPP_WORD_CALL_ARGS.match(call.group("args"))
        if args is None:
            return Prose(f"field_word({call.group('args')}) names no literal key or no words")
        if args.group("key") != key:
            continue
        found = word_literals(CppText(args.group("words")))
        if found is None:
            return Prose(f"field_word({call.group('args')}) awaits a word that is not a literal")
        words |= found
    return frozenset(words) if words else Prose(f"no field_word call at {key!r}")


def _table_reads(
    spec: _CppTable, package: dict[Path, _CppFile], declared: _CppSite, last: CppSymbol
) -> Iterator[Prose]:
    """Yield each reference to a table, its declaration aside, but a lookup defaulting to ``last``.

    A table no lookup reads is yielded too, since the reader then reads another.
    """
    name = re.escape(spec.name)
    lookup = re.compile(
        rf"\blookup\(\s*(?P<table>{name})\b(?:[^()]|\((?:[^()]|\([^()]*\))*\))*\)"
        + r"(?:\s*\.value_or\(\s*(?P<default>\w+(?:::\w+)*)\s*\))?"
    )
    read = False
    for path, file in package.items():
        defaults = {
            call.start("table"): call.group("default") for call in lookup.finditer(file.hollow)
        }
        shown = file.code.split("\n")
        for mention in re.finditer(rf"\b{name}\b", file.hollow):
            number = CppLine(file.hollow.count("\n", 0, mention.start()) + 1)
            where = f"{path.relative_to(REPO_ROOT)}:{number}: {shown[number - 1].strip()!r}"
            if (path, number) == declared:
                continue
            if mention.start() not in defaults:
                yield Prose(f"{where} reaches {spec.name} outside a lookup")
                continue
            read = True
            if defaults[mention.start()] != last:
                yield Prose(f"{where} reads a word outside {spec.name} as other than {last}")
    if not read:
        yield Prose(f"{spec.module.relative_to(REPO_ROOT)}:{spec.name}: no lookup reads it")


def _table_arms(spec: _CppTable, package: dict[Path, _CppFile]) -> Arms | Prose:
    """Return a table's words and its last entry's, or each line that hides them."""
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.name}"
    name = re.escape(spec.name)
    declared = [
        (path, number)
        for path, file in package.items()
        for number, line, _ in _cpp_lines(file)
        if re.search(rf"\b{name}\s*=(?!=)", line)
    ]
    if [path for path, _ in declared] != [spec.module]:
        return Prose(f"{where}: given a value {len(declared)} times in the library, not once")
    lines = package[spec.module].code.split("\n")
    at = declared[0][1]
    head = rf"^(?:(?:static|inline)\s+)*constexpr\s+auto\s+{name}\s*=\s*std::to_array<.+>\(\{{$"
    if re.match(head, lines[at - 1].strip()) is None:
        return Prose(f"{where}: {lines[at - 1].strip()!r} opens no constexpr std::to_array table")
    words: list[ReplyWord] = []
    values: list[CppSymbol] = []
    for number, line in enumerate(lines[at:], start=at + 1):
        if line.strip() == "});":
            break
        entry = _CPP_TABLE_ENTRY.match(line.strip())
        if line.strip() and entry is None:
            return Prose(f"{where}:{number}: {line.strip()!r} is not one {{word, enumerator}}")
        if entry is not None:
            words.append(ReplyWord(entry.group("word")))
            values.append(CppSymbol(entry.group("value")))
    if not words or len(set(words)) != len(words):
        return Prose(f"{where}: the table is empty or names a word twice")
    breaches = list(_table_reads(spec, package, declared[0], values[-1]))
    return Prose("; ".join(breaches)) if breaches else Arms(frozenset(words), words[-1])


def _enum_word_breaches(spec: _CppEnumWords, package: dict[Path, _CppFile]) -> Iterator[Prose]:
    """Yield each line that could give an enumerator a second word or reach its word elsewhere."""
    module = package[spec.module].code
    giver = frozenset((spec.module, n) for n in _cpp_function_lines(module, spec.words))
    reader = frozenset((spec.module, n) for n in _cpp_function_lines(module, spec.reader))
    declaration = frozenset(
        (spec.header, number)
        for number, line, _ in _cpp_lines(package[spec.header])
        if re.match(rf"^\s*(?:\[\[nodiscard\]\]\s+)?auto\s+{re.escape(spec.words)}\(", line)
    )
    breaches = (
        (
            rf"\b{re.escape(spec.words)}\b",
            f"reaches {spec.words} outside {spec.reader}",
            giver | reader | declaration,
        ),
        (
            rf"\bcase\s+{re.escape(spec.enum)}::",
            f"switches on a {spec.enum} outside {spec.words}, which could give it a second word",
            giver,
        ),
    )
    for path, file in package.items():
        for number, line, shown in _cpp_lines(file):
            for regex, what, exempt in breaches:
                if re.search(regex, line) and (path, number) not in exempt:
                    yield Prose(f"{path.relative_to(REPO_ROOT)}:{number}: {shown!r} {what}")


def _cpp_enum_words(
    spec: _CppEnumWords, package: dict[Path, _CppFile]
) -> frozenset[ReplyWord] | Prose:
    """Return the word a function gives each enumerator of an enum, or each line that hides them."""
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.words}"
    enum = re.escape(spec.enum)
    declaration = re.compile(
        rf"\benum\s+(?:class|struct)\s+{enum}\b[^{{;]*\{{(?P<members>[^}}]*)\}}"
    )
    declared = [
        (path, found) for path, file in package.items() for found in declaration.finditer(file.code)
    ]
    if [path for path, _ in declared] != [spec.header]:
        return Prose(f"{spec.enum} is not defined once, in {spec.header.relative_to(REPO_ROOT)}")
    members = [m.strip() for m in declared[0][1].group("members").split(",") if m.strip()]
    module = package.get(spec.module)
    body = None if module is None else _cpp_function(module.code, spec.words)
    if body is None:
        return Prose(f"{where} is not defined")
    cases = list(
        re.finditer(rf'\bcase\s+{enum}::(?P<member>\w+):\s*return\s+"(?P<word>[^"\\]*)";', body)
    )
    hollow = _cpp_hollow(body)
    exits = {len(re.findall(r"\bcase\b", hollow)), len(re.findall(r"\breturn\b", hollow))}
    if exits != {len(cases)}:
        return Prose(f"{where}: a case or a return is not one enumerator returning one literal")
    words = [ReplyWord(case.group("word")) for case in cases]
    named = sorted(case.group("member") for case in cases)
    if named != sorted(members) or len(set(words)) != len(words):
        return Prose(f"{where}: its cases do not give each enumerator of {spec.enum} its own word")
    breaches = list(_enum_word_breaches(spec, package))
    return Prose("; ".join(breaches)) if breaches else frozenset(words)


def _cpp_words(
    spec: _CppSet, cpp_codes: frozenset[ReplyWord], package: dict[Path, _CppFile]
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return a C++ reader set's words and last arm, or why the gate cannot read them."""
    if isinstance(spec, _CppBoundKinds):
        return cpp_codes
    if isinstance(spec, _CppEnumWords):
        return _cpp_enum_words(spec, package)
    if isinstance(spec, _CppTable):
        return _table_arms(spec, package)
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.function}"
    file = package.get(spec.module)
    body = None if file is None else _cpp_function(file.code, spec.function)
    if body is None:
        return Prose(f"{where} is not defined")
    found = (
        _dispatch_arms(spec, body)
        if isinstance(spec, _CppDispatch)
        else _cpp_word_call_words(body, spec.key)
    )
    return Prose(f"{where}: {found}") if isinstance(found, str) else found


def _cpp_reader_breaches(package: dict[Path, _CppFile]) -> Iterator[Prose]:
    """Yield each line of a reader file that could read a tag word outside the readers' sets.

    That is a comparison of a word outside the dispatches ``CPP_REPLY_TEXT``
    names, which the gate reads, and a lookup of a table no reader file declares.
    """
    dispatched = frozenset(
        (spec.module, number)
        for spec in CPP_REPLY_TEXT.values()
        if isinstance(spec, _CppDispatch) and spec.module in package
        for number in _cpp_function_lines(package[spec.module].code, spec.function)
    )
    readers = {path: file for path, file in package.items() if _is_cpp_reader(path)}
    tables = {
        table.group("name")
        for file in readers.values()
        for table in re.finditer(r"\b(?P<name>\w+)\s*=\s*std::to_array\b", file.hollow)
    }
    for path, file in readers.items():
        for number, line, shown in _cpp_lines(file):
            where = f"{path.relative_to(REPO_ROOT)}:{number}: {shown!r}"
            if _CPP_WORD_COMPARISON.search(line) and (path, number) not in dispatched:
                yield Prose(f"{where} compares a word outside the dispatches CPP_REPLY_TEXT names")
        for call in re.finditer(r"\blookup\(\s*(?P<table>\w+)", file.hollow):
            if call.group("table") not in tables:
                number = file.hollow.count("\n", 0, call.start()) + 1
                yield Prose(
                    f"{path.relative_to(REPO_ROOT)}:{number}: looks up {call.group('table')}, "
                    + "a table no reader file declares"
                )


def cpp_reader(cpp_codes: frozenset[ReplyWord]) -> BindingReader:
    """Return the C++ reader, whose bound kinds are ``cpp_codes``.

    It adds each line of a reader file that could read a tag word outside its
    sets to the places none reads.
    """

    def read(unread: list[Prose]) -> ReaderSets:
        package = _cpp_package()
        sets = read_sets(
            Prose("the C++ reader"),
            Prose("CPP_REPLY_TEXT"),
            CPP_REPLY_TEXT,
            lambda spec: _cpp_words(spec, cpp_codes, package),
            unread,
        )
        unread.extend(_cpp_reader_breaches(package))
        return sets

    return read
