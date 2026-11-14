# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ reader of the reply-tags arm, ``tools/_reply_places.py``.

It reads the set the C++ binding's reply readers take at each string place of
``replyText`` from their own code, as libclang parses it
(``tools/_reply_places_cpp_tree.py``): a ``std::to_array`` table of ``{word,
enumerator}`` pairs read by ``field_member``, the words a function's
``field_word`` calls await, alone or with the dispatch mapping the word one such
call reads, the words one function gives an enum's enumerators, or the
``bound_kind_*`` codes.
A table's last entry, or the code after a dispatch's tests, is the reader's last
arm: as ``field_member`` and ``field_word`` refuse every other word, it reads the
awaited words its other arms do not name and the words of the arms giving its
value, must read one word or none, and is held to the row's last word.
A line of a reader file that could read a tag word outside these sets, a word
compared outside the dispatches or a table no reader file declares looked up,
is reported with each set the module cannot read, and so is each line the
compiler refuses.  The library the gate reads is the files the rows name and
the reader files, each parsed once with the compile database's flags.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from tools._reply_places import (
    REPO_ROOT,
    AnyNonEmpty,
    Arms,
    CppLine,
    CppSymbol,
    CppText,
    MappingNames,
    ReaderSets,
    ReplyPlace,
    ReplyWord,
    mapped_last,
    read_sets,
)
from tools._reply_places_cpp_tree import (
    CppNode,
    CppUnit,
    DeclKey,
    bare,
    compile_arguments,
    cpp_function,
    cpp_function_lines,
    defined,
    libclang,
    literal,
    parse_unit,
    walk,
)
from tools._reply_places_tree import holds_word
from tools._vendor.clang.cindex import CursorKind, TokenKind

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator
    from pathlib import Path

    from tools._reply_places import BindingReader

CPP_SOURCE = REPO_ROOT / "cpp" / "src"
CPP_INCLUDE = REPO_ROOT / "cpp" / "include"
CPP_PARSE = CPP_SOURCE / "json_parse.cpp"
CPP_PARSE_DBC = CPP_SOURCE / "json_parse_dbc.cpp"
CPP_REPLY_SHAPE = CPP_SOURCE / "reply_shape.cpp"
CPP_REPLY_SHAPE_HEADER = CPP_SOURCE / "detail" / "reply_shape.hpp"


@dataclass(frozen=True)
class _CppMemberTable:
    """A ``constexpr std::to_array`` table of ``{word, enumerator}`` pairs, one per line.

    The table is declared once, in a reader file, and every other reference to
    it is the table argument of a ``field_member`` call, which refuses each word
    the table does not name.  Its last entry is its last arm, which reads the
    words of the entries giving its enumerator too.
    """

    module: Path
    name: CppSymbol


@dataclass(frozen=True)
class _CppWordCall:
    """The literals a function's ``field_word`` calls at a key await."""

    module: Path
    function: CppSymbol
    key: ReplyWord


@dataclass(frozen=True)
class _CppMappedWordCall:
    """The literals a function's one ``field_word`` call at a key awaits, and its tests.

    The function reads the word once with ``field_word``, holding it ``auto
    const`` or comparing it where it reads it, and compares it only with ``==``
    to literals, each the condition of an ``if`` returning one value built as
    ``NAME{...}``; its last statement, returning one value so built, is its last
    arm, and every other return is an arm's.  The type a value builds stands for
    it.  The last arm reads the awaited words no comparison names and the words
    of the arms building its type, and must read one word or none.
    """

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


type _CppSet = _CppMemberTable | _CppWordCall | _CppMappedWordCall | _CppEnumWords | _CppBoundKinds

# Every row of `replyText`, with the set the C++ reader takes at its place, read
# from the reader's own code, under the rules PYTHON_REPLY_TEXT is held to; a
# table's last entry, or the code after a dispatch's tests, reads the row's
# last word.
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
        "results/type": _CppWordCall(CPP_PARSE, CppSymbol("read_verdict"), ReplyWord("type")),
        "results/status <property>": _CppMemberTable(CPP_PARSE, CppSymbol("verdict_table")),
        "warnings/kind": _CppWordCall(
            CPP_PARSE, CppSymbol("read_stream_warning"), ReplyWord("kind")
        ),
        "issues/severity": _CppMemberTable(CPP_PARSE, CppSymbol("severity_table")),
        "warnings/severity": _CppMemberTable(CPP_PARSE, CppSymbol("severity_table")),
        "bound_kind": _CppBoundKinds(),
        "dbc/messages/signals/byteOrder": _CppMemberTable(
            CPP_PARSE_DBC, CppSymbol("byte_order_table")
        ),
        "dbc/messages/signals/presence": _CppMappedWordCall(
            CPP_PARSE_DBC, CppSymbol("read_presence"), ReplyWord("presence")
        ),
        "dbc/messages/signals/multiplexor": AnyNonEmpty(),
        "dbc/comments/target/kind": _CppMappedWordCall(
            CPP_PARSE_DBC, CppSymbol("read_comment_target"), ReplyWord("kind")
        ),
        "dbc/attributes/kind": _CppMappedWordCall(
            CPP_PARSE_DBC, CppSymbol("read_attribute"), ReplyWord("kind")
        ),
        "dbc/attributes/scope <definition>": _CppMemberTable(
            CPP_PARSE_DBC, CppSymbol("attr_scope_table")
        ),
        "dbc/attributes/attrType/kind": _CppMappedWordCall(
            CPP_PARSE_DBC, CppSymbol("read_attr_type"), ReplyWord("kind")
        ),
        "dbc/attributes/value/kind": _CppMappedWordCall(
            CPP_PARSE_DBC, CppSymbol("read_attr_value"), ReplyWord("kind")
        ),
        "dbc/attributes/target/kind": _CppMappedWordCall(
            CPP_PARSE_DBC, CppSymbol("read_attr_target"), ReplyWord("kind")
        ),
    }.items()
}

# Each file of the C++ library the gate parses, by its path.
type _Package = dict[Path, CppUnit]

# The operators a comparison is written with; the calls that search a text,
# and those that search one only as members of std::string or std::string_view,
# whose classes libclang names basic_string and basic_string_view, since a
# Json's contains and find look a key up.  find_first_of, find_last_of and
# their _not_of siblings take a set of characters, so they compare no word.
_COMPARED = frozenset({CppText("=="), CppText("!=")})
_SEARCHES = frozenset({CppSymbol("starts_with"), CppSymbol("ends_with")})
_TEXT_SEARCHES = frozenset({CppSymbol("find"), CppSymbol("contains")})
_TEXTS = frozenset({CppSymbol("basic_string"), CppSymbol("basic_string_view")})
# The tokens a table's line holds past its specifiers, before and after its
# element type, and the tokens closing it.
_SPECIFIERS = frozenset({CppText("static"), CppText("inline")})
_TABLE_HEAD = (CppText("constexpr"), CppText("auto"))
_TABLE_CALL = tuple(map(CppText, ("=", "std", "::", "to_array", "<")))
_TABLE_OPEN = [CppText("("), CppText("{")]
_TABLE_CLOSE = [CppText("}"), CppText(")"), CppText(";")]
# The token after ``enum`` that scopes an enum's enumerators.
_SCOPED = ([CppText("class")], [CppText("struct")])


def _cpp_source(path: Path) -> CppText:
    """Return the source of a file of the C++ library."""
    return CppText(path.read_text(encoding="utf-8"))


def _shown(path: Path) -> Prose:
    """Return a path as a refusal names it, from the repository's root where it stands in it."""
    return Prose(str(path.relative_to(REPO_ROOT) if path.is_relative_to(REPO_ROOT) else path))


def _is_cpp_reader(path: Path) -> bool:
    """Whether a file of the C++ library is a reply reader, a json_parse*.cpp or a reply_shape."""
    return path.stem == "reply_shape" or (
        path.parent == CPP_SOURCE and path.match("json_parse*.cpp")
    )


def _named(spec: _CppSet | AnyNonEmpty) -> frozenset[Path]:
    """Return the files a row reads."""
    if isinstance(spec, _CppEnumWords):
        return frozenset({spec.header, spec.module})
    if isinstance(spec, _CppBoundKinds | AnyNonEmpty):
        return frozenset()
    return frozenset({spec.module})


def _cpp_package() -> _Package:
    """Return each file a row reads and each reader file, parsed once.

    Each is parsed with every header of the library as ``_cpp_source`` gives it.
    """
    library = libclang()
    files = [
        path
        for root in (CPP_SOURCE, CPP_INCLUDE)
        for path in sorted(root.rglob("*"))
        if path.suffix in {".cpp", ".hpp"}
    ]
    named = frozenset(path for spec in CPP_REPLY_TEXT.values() for path in _named(spec))
    headers = tuple((path, _cpp_source(path)) for path in files if path.suffix == ".hpp")
    package: _Package = {}
    for path in files:
        if path in named or _is_cpp_reader(path):
            own = () if path.suffix == ".hpp" else ((path, _cpp_source(path)),)
            package[path] = parse_unit(library, path, compile_arguments(path), (*own, *headers))
    return package


def _site(unit: CppUnit, line: CppLine) -> Prose:
    """Return a line of a file as a refusal names it: its path, its number and its code."""
    return Prose(f"{_shown(unit.path)}:{line}: {unit.line_code(line)!r}")


@dataclass(frozen=True)
class _Comparison:
    """An equality or an inequality: its operator, the line it stands on and its operands."""

    operator: CppText
    line: CppLine
    operands: tuple[CppNode, ...]


def _comparison(unit: CppUnit, node: CppNode) -> _Comparison | None:
    """Return what a node compares with ``==`` or ``!=``, its operands in source order, or None.

    The operator is the first ``==`` or ``!=`` standing in neither operand:
    between them written infix, after ``operator`` called by its name.
    """
    if node.kind == CursorKind.CALL_EXPR and node.name.startswith("operator"):
        operands = node.arguments
    elif node.kind == CursorKind.BINARY_OPERATOR:
        operands = node.parts
    else:
        return None
    if len(operands) != len(("left", "right")):
        return None
    inside = {token for operand in operands for token in unit.tokens_of(operand)}
    for token in unit.tokens_of(node):
        if token.text in _COMPARED and token not in inside:
            return _Comparison(token.text, token.line, operands)
    return None


def _holds_literal(unit: CppUnit, node: CppNode, *, word: bool) -> bool:
    """Say whether an operand is a string literal: bare, given a suffix, or made a string of.

    When ``word``, the literal's text, as the compiler reads its escapes, is a
    word as ``holds_word`` says.
    """
    found = bare(node)
    if found.kind == CursorKind.STRING_LITERAL:
        return not word or holds_word(literal(unit, found))
    constructed = found.referenced is not None and found.referenced.kind == CursorKind.CONSTRUCTOR
    made = found.kind == CursorKind.CXX_FUNCTIONAL_CAST_EXPR or (
        found.kind == CursorKind.CALL_EXPR and (constructed or found.name.startswith('operator""'))
    )
    return made and any(_holds_literal(unit, part, word=word) for part in found.parts)


def _holds_no_word(unit: CppUnit, node: CppNode) -> bool:
    """Say whether an argument is a string literal, as ``_holds_literal`` reads one, of no word."""
    return _holds_literal(unit, node, word=False) and not _holds_literal(unit, node, word=True)


def _searches(node: CppNode) -> bool:
    """Say whether a call, what it calls its first part, compares a text with its arguments.

    That is a ``compare`` member, a ``starts_with`` or ``ends_with`` call, and
    a ``find`` or ``contains`` member of a std::string or a std::string_view.
    """
    if node.name == "compare":
        return node.parts[0].kind == CursorKind.MEMBER_REF_EXPR
    if node.name in _TEXT_SEARCHES:
        named = node.referenced
        return named is not None and named.scope in _TEXTS
    return node.name in _SEARCHES


def _word_comparisons(unit: CppUnit, nodes: list[CppNode], *, word: bool) -> list[CppLine]:
    """Return the line of each comparison among ``nodes`` that could read a word.

    That is ``==`` or ``!=``, written infix or called by its name, beside a
    string literal, holding a word when ``word``, at its operator; and a call
    ``_searches`` names, at its name, unless ``word`` and every argument it is
    given is a string literal of no word.
    """
    lines: list[CppLine] = []
    for node in nodes:
        compared = _comparison(unit, node)
        if compared is not None and any(
            _holds_literal(unit, operand, word=word) for operand in compared.operands
        ):
            lines.append(compared.line)
        if node.kind != CursorKind.CALL_EXPR or not node.parts:
            continue
        if _searches(node) and not (
            word and all(_holds_no_word(unit, argument) for argument in node.arguments)
        ):
            lines.append(node.parts[0].line)
    return lines


def _arm(
    unit: CppUnit, compared: _Comparison, operand: Callable[[CppNode], bool]
) -> ReplyWord | None:
    """Return the word an equality compares an operand with, None when it compares none."""
    if compared.operator != "==":
        return None
    left, right = compared.operands
    for one, other in ((left, right), (right, left)):
        if operand(bare(one)):
            text = literal(unit, other)
            return None if text is None else ReplyWord(text)
    return None


def _holder(unit: CppUnit, function: CppNode, read: CppNode) -> CppNode | None:
    """Return the variable written ``auto const NAME =`` the read initializes, or None."""
    for variable in walk(function):
        if variable.kind == CursorKind.VAR_DECL and any(
            bare(part) is read for part in variable.parts
        ):
            head = [token.text for token in unit.tokens_of(variable) if token.end <= read.start]
            return variable if head == ["auto", "const", variable.name, "="] else None
    return None


def _word_at(read: CppNode, held: CppNode | None) -> Callable[[CppNode], bool]:
    """Return what says a node is the word at the key: the read, or a use of what holds it."""
    if held is None:
        return lambda node: node is read
    return lambda node: (
        node.kind == CursorKind.DECL_REF_EXPR
        and node.referenced is not None
        and node.referenced.key == held.key
    )


def _compared_words(
    unit: CppUnit, function: CppNode, key: ReplyWord
) -> tuple[list[ReplyWord], Callable[[CppNode], bool]] | Prose:
    """Return the words a function compares the word ``field_word`` reads at ``key`` with.

    Beside them comes what says a node is that word.
    """
    nodes = list(walk(function))
    reads = [
        node
        for node in nodes
        if node.kind == CursorKind.CALL_EXPR
        and node.name == "field_word"
        and len(node.arguments) == len(("obj", "path", "key", "words"))
        and literal(unit, node.arguments[2]) == key
    ]
    if len(reads) != 1:
        return Prose(f"reads {key!r} with field_word {len(reads)} times, not once")
    held = _holder(unit, function, reads[0])
    word_at = _word_at(reads[0], held)
    compared = [found for node in nodes if (found := _comparison(unit, node)) is not None]
    where_read = any(
        each.operator == "=="
        and any(word_at(bare(one)) for one in each.operands)
        and any(_holds_literal(unit, operand, word=False) for operand in each.operands)
        for each in compared
    )
    if held is None and not where_read:
        return Prose(f"neither holds the word at {key!r} nor compares it where it reads it")
    words = [word for each in compared if (word := _arm(unit, each, word_at)) is not None]
    if len(_word_comparisons(unit, nodes, word=False)) != len(words):
        return Prose(f"compares a word other than the one at {key!r} with == to a literal")
    if held is not None and sum(map(word_at, nodes)) != len(words):
        return Prose(f"uses {held.name} other than to compare it with a literal")
    if len(set(words)) != len(words):
        return Prose("compares the word with one literal twice")
    return words, word_at


def _built(statement: CppNode) -> DeclKey | None:
    """Return the type a ``return NAME{...};`` builds, braced alone or not, or None."""
    if statement.kind == CursorKind.COMPOUND_STMT and len(statement.parts) == 1:
        statement = statement.parts[0]
    if statement.kind != CursorKind.RETURN_STMT or len(statement.parts) != 1:
        return None
    value = bare(statement.parts[0])
    if value.kind != CursorKind.CXX_FUNCTIONAL_CAST_EXPR or not value.parts:
        return None
    named = value.parts[0]
    if named.kind != CursorKind.TYPE_REF or named.referenced is None:
        return None
    return named.referenced.key


@dataclass(frozen=True)
class _Test:
    """A test of a dispatch's word: the literal it is compared with, the type its if returns."""

    word: ReplyWord
    built: DeclKey


@dataclass(frozen=True)
class _Tests:
    """A dispatch's tests in order, and the type its last statement returns."""

    tests: list[_Test]
    last: DeclKey


def _arm_values(
    unit: CppUnit, function: CppNode, word_at: Callable[[CppNode], bool]
) -> _Tests | Prose:
    """Return each test's word and the type its ``if`` returns, and the last statement's type.

    Every return of the function is a test's or its last statement.
    """
    arms: list[_Test] = []
    for node in walk(function):
        if node.kind != CursorKind.IF_STMT or not node.parts:
            continue
        compared = _comparison(unit, bare(node.parts[0]))
        word = None if compared is None else _arm(unit, compared, word_at)
        if word is None:
            continue
        built = _built(node.parts[1]) if len(node.parts) == len(("condition", "then")) else None
        if built is None:
            return Prose(f"the test of {word!r} returns no one value built as NAME{{...}}")
        arms.append(_Test(word, built))
    body = next(
        (part for part in reversed(function.parts) if part.kind == CursorKind.COMPOUND_STMT), None
    )
    last = None if body is None or not body.parts else _built(body.parts[-1])
    if last is None:
        return Prose("its last statement returns no one value built as NAME{...}")
    if sum(node.kind == CursorKind.RETURN_STMT for node in walk(function)) != len(arms) + 1:
        return Prose("returns other than in its tests and its last statement")
    return _Tests(arms, last)


def _mapped_arms(
    unit: CppUnit, spec: _CppMappedWordCall, function: CppNode
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return the words a function's ``field_word`` call awaits and the word its last arm reads."""
    awaited = _word_call_words(unit, function, spec.key)
    if isinstance(awaited, str):
        return awaited
    compared = _compared_words(unit, function, spec.key)
    if isinstance(compared, str):
        return compared
    words, word_at = compared
    values = _arm_values(unit, function, word_at)
    if isinstance(values, str):
        return values
    if len(values.tests) != len(words):
        return Prose("compares the word other than as the condition of an if")
    mapping = Prose(f"the tests of the word at {spec.key!r}")
    names = MappingNames(
        mapping, Prose(f"field_word call at {spec.key!r}"), Prose(f"the code after {mapping}")
    )
    shared = frozenset(test.word for test in values.tests if test.built == values.last)
    return mapped_last(awaited, frozenset(words), shared, names)


def _word_call_words(
    unit: CppUnit, function: CppNode, key: ReplyWord
) -> frozenset[ReplyWord] | Prose:
    """Return the words a function's ``field_word`` calls at ``key`` await."""
    calls = [
        node
        for node in walk(function)
        if node.kind == CursorKind.CALL_EXPR and node.name == "field_word"
    ]
    inside: list[CppText] = []
    for call in calls:
        tokens = unit.tokens_of(call)
        opened = next(at for at, token in enumerate(tokens) if token.text == "(")
        if any(token.text == "(" for token in tokens[opened + 1 : -1]):
            return Prose("a field_word call holds a call of its own")
        inside.append(unit.code(tokens[opened].end, tokens[-1].start))
    words: set[ReplyWord] = set()
    for call, written in zip(calls, inside, strict=True):
        named = literal(unit, call.arguments[-2]) if call.arguments[2:] else None
        listed = bare(call.arguments[-1]) if call.arguments else None
        if named is None or listed is None or listed.kind != CursorKind.INIT_LIST_EXPR:
            return Prose(f"field_word({written}) names no literal key or no words")
        if named != key:
            continue
        found = [literal(unit, part) for part in listed.parts]
        if None in found:
            return Prose(f"field_word({written}) awaits a word that is not a literal")
        words |= {ReplyWord(word) for word in found if word is not None}
    return frozenset(words) if words else Prose(f"no field_word call at {key!r}")


@dataclass(frozen=True)
class _TableEntries:
    """A table's words in its order, those sharing its last entry's enumerator, and its key.

    ``shared`` holds the words of the entries before the last naming the
    enumerator it names; ``key`` is the table's own, which a reference names.
    """

    words: list[ReplyWord]
    shared: frozenset[ReplyWord]
    key: DeclKey


def _table_list(table: CppNode) -> CppNode | None:
    """Return the braced list a variable's ``std::to_array`` call is given, or None."""
    for part in table.parts:
        call = bare(part)
        if (
            call.kind == CursorKind.CALL_EXPR
            and call.name == "to_array"
            and call.referenced is not None
            and call.referenced.scope == "std"
            and len(call.arguments) == 1
        ):
            listed = bare(call.arguments[0])
            return listed if listed.kind == CursorKind.INIT_LIST_EXPR else None
    return None


def _opens_table(unit: CppUnit, table: CppNode) -> bool:
    """Say whether a table's line is ``constexpr auto NAME = std::to_array<...>({`` alone."""
    texts = [token.text for token in unit.tokens_on(table.line)]
    head = texts[next((at for at, text in enumerate(texts) if text not in _SPECIFIERS), 0) :]
    shape = (*_TABLE_HEAD, table.name, *_TABLE_CALL)
    return tuple(head[: len(shape)]) == shape and head[-len(_TABLE_OPEN) :] == _TABLE_OPEN


def _entry(unit: CppUnit, listed: CppNode, line: CppLine) -> tuple[ReplyWord, CppNode] | None:
    """Return the word and the enumerator of the one ``{word, enumerator}`` on a line, or None.

    The line holds the entry alone, a comma after it aside.
    """
    entry = next((part for part in listed.parts if part.first == line), None)
    if entry is None or len(entry.parts) != len(("word", "enumerator")):
        return None
    texts = [token.text for token in unit.tokens_on(line)]
    written = [token.text for token in unit.tokens_of(entry)]
    word, value = literal(unit, entry.parts[0]), bare(entry.parts[1])
    if texts not in (written, [*written, ","]) or word is None:
        return None
    return (ReplyWord(word), value) if value.kind == CursorKind.DECL_REF_EXPR else None


def _table_entries(spec: _CppMemberTable, package: _Package) -> _TableEntries | Prose:
    """Return a table's entries, or why the gate cannot read them."""
    where = f"{_shown(spec.module)}:{spec.name}"
    declared = [
        (path, node)
        for path, unit in package.items()
        for node in defined(unit, CursorKind.VAR_DECL, spec.name)
    ]
    if [path for path, _ in declared] != [spec.module]:
        return Prose(f"{where}: given a value {len(declared)} times in the library, not once")
    unit, table = package[spec.module], declared[0][1]
    listed = _table_list(table)
    if listed is None or not _opens_table(unit, table):
        return Prose(
            f"{where}: {unit.line_code(table.line)!r} opens no constexpr std::to_array table"
        )
    entries: list[tuple[ReplyWord, CppNode]] = []
    for number in map(CppLine, range(table.line + 1, listed.last + 1)):
        texts = [token.text for token in unit.tokens_on(number)]
        if not texts or (number == listed.last and texts == _TABLE_CLOSE):
            continue
        entry = _entry(unit, listed, number)
        if entry is None:
            shown = unit.line_code(number)
            return Prose(f"{where}:{number}: {shown!r} is not one {{word, enumerator}}")
        entries.append(entry)
    words = [word for word, _ in entries]
    last = entries[-1][1] if entries else None
    if last is None or last.referenced is None or len(set(words)) != len(words):
        return Prose(f"{where}: the table is empty or names a word twice")
    return _TableEntries(words, _sharing(entries), table.key)


def _sharing(entries: list[tuple[ReplyWord, CppNode]]) -> frozenset[ReplyWord]:
    """Return the words of the entries before a table's last naming the enumerator it names."""
    *before, (_, last) = entries
    named = last.referenced
    return frozenset(
        word
        for word, value in before
        if named is not None and value.referenced is not None and value.referenced.key == named.key
    )


def _references(package: _Package, entries: _TableEntries) -> Iterator[tuple[CppUnit, CppNode]]:
    """Yield each reference to a table, in the library's order."""
    for unit in package.values():
        for node in unit.of_kind(CursorKind.DECL_REF_EXPR):
            if node.referenced is not None and node.referenced.key == entries.key:
                yield unit, node


def _calls(unit: CppUnit, name: CppSymbol) -> list[CppNode]:
    """Return a file's calls of ``name``, in source order."""
    return [node for node in unit.of_kind(CursorKind.CALL_EXPR) if node.name == name]


def _member_reads(
    spec: _CppMemberTable, package: _Package, entries: _TableEntries
) -> Iterator[Prose]:
    """Yield each reference to a table, its declaration aside, but a ``field_member`` read of it.

    A table no ``field_member`` call reads is yielded too, since the reader then
    reads another.
    """
    read = False
    for unit, reference in _references(package, entries):
        if not any(
            bare(argument) is reference
            for call in _calls(unit, CppSymbol("field_member"))
            for argument in call.arguments[1:]
        ):
            where = _site(unit, reference.line)
            yield Prose(f"{where} reaches {spec.name} outside a field_member call")
            continue
        read = True
    if not read:
        yield Prose(f"{_shown(spec.module)}:{spec.name}: no field_member call reads it")


def _member_table_arms(
    spec: _CppMemberTable, package: _Package
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return a table's words, each other refused, and its last entry's, or what hides them."""
    entries = _table_entries(spec, package)
    if isinstance(entries, str):
        return entries
    breaches = list(_member_reads(spec, package, entries))
    if breaches:
        return Prose("; ".join(breaches))
    names = MappingNames(
        Prose(spec.name), Prose(f"field_member call reading {spec.name}"), Prose("its last entry")
    )
    awaited = frozenset(entries.words)
    found = mapped_last(awaited, frozenset(entries.words[:-1]), entries.shared, names)
    return Prose(f"{_shown(spec.module)}:{spec.name}: {found}") if isinstance(found, str) else found


def _names_member_of(node: CppNode, enum: CppSymbol) -> bool:
    """Say whether a node names an enumerator of ``enum``."""
    named = bare(node).referenced
    return named is not None and named.kind == CursorKind.ENUM_CONSTANT_DECL and named.scope == enum


def _enum_word_breaches(spec: _CppEnumWords, package: _Package) -> Iterator[Prose]:
    """Yield each line that could give an enumerator a second word or reach its word elsewhere."""
    module = package.get(spec.module)
    giver = frozenset((spec.module, line) for line in cpp_function_lines(module, spec.words))
    reader = frozenset((spec.module, line) for line in cpp_function_lines(module, spec.reader))
    header = package.get(spec.header)
    declaration = frozenset(
        (spec.header, node.line)
        for node in ([] if header is None else header.of_kind(CursorKind.FUNCTION_DECL))
        if node.name == spec.words and not node.definition
    )
    for path, unit in package.items():
        reached: set[CppLine] = set()
        switched: set[CppLine] = set()
        for node in unit.nodes:
            named = node.referenced
            names = node.kind == CursorKind.FUNCTION_DECL or (
                named is not None and named.kind == CursorKind.FUNCTION_DECL
            )
            if names and node.name == spec.words:
                reached.add(node.line)
            if node.kind == CursorKind.CASE_STMT and _names_member_of(node.parts[0], spec.enum):
                switched.add(node.line)
        reached -= {line for site, line in giver | reader | declaration if site == path}
        switched -= {line for site, line in giver if site == path}
        for line in sorted(reached | switched):
            if line in reached:
                yield Prose(f"{_site(unit, line)} reaches {spec.words} outside {spec.reader}")
            if line in switched:
                yield Prose(
                    f"{_site(unit, line)} switches on a {spec.enum} outside {spec.words}, "
                    + "which could give it a second word"
                )


def _given(unit: CppUnit, case: CppNode, enum: CppSymbol) -> tuple[CppSymbol, ReplyWord] | None:
    """Return the enumerator a case names and the literal it returns, or None when it is not so."""
    if len(case.parts) != len(("label", "statement")):
        return None
    label, then = case.parts
    if then.kind != CursorKind.RETURN_STMT or len(then.parts) != 1:
        return None
    word = literal(unit, then.parts[0])
    if word is None or not _names_member_of(label, enum):
        return None
    return bare(label).name, ReplyWord(word)


def _cpp_enum_words(spec: _CppEnumWords, package: _Package) -> frozenset[ReplyWord] | Prose:
    """Return the word a function gives each enumerator of an enum, or each line that hides them."""
    where = f"{_shown(spec.module)}:{spec.words}"
    declared = [
        (path, node)
        for path, unit in package.items()
        for node in defined(unit, CursorKind.ENUM_DECL, spec.enum)
        if [token.text for token in unit.tokens_of(node)[1:2]] in _SCOPED
    ]
    if [path for path, _ in declared] != [spec.header]:
        return Prose(f"{spec.enum} is not defined once, in {_shown(spec.header)}")
    members = sorted(
        part.name for part in declared[0][1].parts if part.kind == CursorKind.ENUM_CONSTANT_DECL
    )
    unit = package.get(spec.module)
    body = cpp_function(unit, spec.words)
    if unit is None or body is None:
        return Prose(f"{where} is not defined")
    nodes = list(walk(body))
    cases = [node for node in nodes if node.kind == CursorKind.CASE_STMT]
    returns = [node for node in nodes if node.kind == CursorKind.RETURN_STMT]
    given = [found for case in cases if (found := _given(unit, case, spec.enum)) is not None]
    if {len(cases), len(returns)} != {len(given)}:
        return Prose(f"{where}: a case or a return is not one enumerator returning one literal")
    words = [word for _, word in given]
    if sorted(member for member, _ in given) != members or len(set(words)) != len(words):
        return Prose(f"{where}: its cases do not give each enumerator of {spec.enum} its own word")
    breaches = list(_enum_word_breaches(spec, package))
    return Prose("; ".join(breaches)) if breaches else frozenset(words)


def _cpp_words(
    spec: _CppSet, cpp_codes: frozenset[ReplyWord], package: _Package
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return a C++ reader set's words and last arm, or why the gate cannot read them."""
    if isinstance(spec, _CppBoundKinds):
        return cpp_codes
    if isinstance(spec, _CppEnumWords):
        return _cpp_enum_words(spec, package)
    if isinstance(spec, _CppMemberTable):
        return _member_table_arms(spec, package)
    where = f"{_shown(spec.module)}:{spec.function}"
    unit = package.get(spec.module)
    function = cpp_function(unit, spec.function)
    if unit is None or function is None:
        return Prose(f"{where} is not defined")
    if isinstance(spec, _CppMappedWordCall):
        found = _mapped_arms(unit, spec, function)
    else:
        found = _word_call_words(unit, function, spec.key)
    return Prose(f"{where}: {found}") if isinstance(found, str) else found


def _cpp_unparsed(package: _Package) -> Iterator[Prose]:
    """Yield each line the compiler refuses parsing a file of the library, once."""
    seen: set[Prose] = set()
    for unit in package.values():
        for broken in unit.broken:
            refused = Prose(
                f"{_shown(broken.path)}:{broken.line}: {broken.shown!r} "
                + f"is not C++ libclang-23 parses: {broken.message}"
            )
            if refused not in seen:
                seen.add(refused)
                yield refused


def _cpp_reader_breaches(package: _Package) -> Iterator[Prose]:
    """Yield each line of a reader file that could read a tag word outside the readers' sets.

    That is a comparison of a word outside the dispatches ``CPP_REPLY_TEXT``
    names, which the gate reads, and a lookup of a table no reader file declares.
    """
    dispatched = frozenset(
        (spec.module, line)
        for spec in CPP_REPLY_TEXT.values()
        if isinstance(spec, _CppMappedWordCall)
        for line in cpp_function_lines(package.get(spec.module), spec.function)
    )
    readers = {path: unit for path, unit in package.items() if _is_cpp_reader(path)}
    tables = {
        node.name
        for unit in readers.values()
        for node in unit.of_kind(CursorKind.VAR_DECL)
        if _table_list(node) is not None
    }
    for path, unit in readers.items():
        for line in sorted(set(_word_comparisons(unit, list(unit.nodes), word=True))):
            if (path, line) not in dispatched:
                yield Prose(
                    f"{_site(unit, line)} compares a word outside the dispatches "
                    + "CPP_REPLY_TEXT names"
                )
        for call in _calls(unit, CppSymbol("lookup")):
            looked = next(
                (
                    token.text
                    for token in unit.tokens_of(call.arguments[0])
                    if token.kind == TokenKind.IDENTIFIER
                ),
                CppText(""),
            )
            if looked not in tables:
                yield Prose(
                    f"{_shown(path)}:{call.first}: looks up {looked}, "
                    + "a table no reader file declares"
                )


def cpp_reader(cpp_codes: frozenset[ReplyWord]) -> BindingReader:
    """Return the C++ reader, whose bound kinds are ``cpp_codes``.

    It adds each line the compiler refuses, and each line of a reader file that
    could read a tag word outside its sets, to the places none reads.
    """

    def read(unread: list[Prose]) -> ReaderSets:
        package = _cpp_package()
        unread.extend(_cpp_unparsed(package))
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
