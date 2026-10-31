# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags arm of ``tools/check_limits_parity.py``.

The reply proof in ``src/Aletheia/Protocol/ReplyRange.agda`` lists, in
``replyText``, the words the kernel writes at each string place of a reply and,
in ``replyNonEmpty``, the arrays it writes with at least one element.  It leaves
a place no row names free, so this module holds each row a reader relies on: it
reads both tables, reads the set each Python reader takes at the place from its
type and the set each Go and C++ reader takes from its own code, and reports a
row one side drops, a word one side holds alone and a C++ last arm, which reads
every word its other arms do not name, other than the row's last word.

A clause of either table, or a reader's type or code, that the module cannot
read is reported rather than passed over, every one of them in one run; the
two catch-all clauses, which leave every other place free, and the tables' type
signatures are the only clauses it reads past.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, NewType

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator

REPO_ROOT = Path(__file__).resolve().parent.parent
AGDA_REPLY_RANGE = REPO_ROOT / "src" / "Aletheia" / "Protocol" / "ReplyRange.agda"
PYTHON_TYPES = REPO_ROOT / "python" / "aletheia" / "types.py"
PYTHON_DBC_TYPES = REPO_ROOT / "python" / "aletheia" / "_dbc_types.py"
PYTHON_ISSUE_CODES = REPO_ROOT / "python" / "aletheia" / "codes" / "_issue.py"
GO_PACKAGE = REPO_ROOT / "go" / "aletheia"
GO_DBC = GO_PACKAGE / "json_dbc.go"
GO_RESPONSE = GO_PACKAGE / "json_response.go"
GO_RESULT = GO_PACKAGE / "result.go"

# A reply place: the keys from the reply's root joined by "/", then, when the
# row depends on it, the `kind` or `type` its object carries in angle brackets.
ReplyPlace = NewType("ReplyPlace", str)
# A string the kernel writes at a reply place.
ReplyWord = NewType("ReplyWord", str)
# A top-level name in a Python module: an alias, a class or a field.
PySymbol = NewType("PySymbol", str)
# Agda source: a module, a clause of it or a fragment of a clause.
AgdaText = NewType("AgdaText", str)
# A top-level name in a Go package: a function or a type.
GoSymbol = NewType("GoSymbol", str)
# Go source: a file, a function of it or a fragment of either.
GoText = NewType("GoText", str)
# The number of a line of a Go file, from 1.
GoLine = NewType("GoLine", int)
# A regular expression over a line of Go source.
GoRegex = NewType("GoRegex", str)
# A name in the C++ library: a function, a table, an enum or an enumerator.
CppSymbol = NewType("CppSymbol", str)
# C++ source: a file, a function of it or a fragment of either.
CppText = NewType("CppText", str)
# The number of a line of a C++ file, from 1.
CppLine = NewType("CppLine", int)


@dataclass(frozen=True)
class _OneOf:
    """A place that holds one of a fixed set of words; ``last`` is its list's last, if any."""

    words: frozenset[ReplyWord]
    last: ReplyWord | None


@dataclass(frozen=True)
class AnyNonEmpty:
    """A place that holds any text but the empty one."""


@dataclass(frozen=True)
class _PyAlias:
    """A ``Literal`` alias whose arguments are the reader's words."""

    module: Path
    name: PySymbol


@dataclass(frozen=True)
class _PyField:
    """A field whose ``Literal`` arguments, over a class or a union of classes, are the words."""

    module: Path
    name: PySymbol
    field: PySymbol


@dataclass(frozen=True)
class _PyEnum:
    """A ``StrEnum`` whose member values are the words."""

    module: Path
    name: PySymbol


@dataclass(frozen=True)
class _PyBoundKinds:
    """The ``BOUND_KIND_*`` codes of ``python/aletheia/limits.py``."""


type _PySet = _PyAlias | _PyField | _PyEnum | _PyBoundKinds

# Every row of `replyText`, with the set the Python reader takes at its place.
# A dropped Agda row, a word on one side only and an Agda row this table does
# not name are each a divergence, so a reader that casts a tag instead of
# checking it reads the kernel's set and no other.  The places are literal
# strings, so ruff (F601) refuses one named twice.
PYTHON_REPLY_TEXT: dict[ReplyPlace, _PySet | AnyNonEmpty] = {
    ReplyPlace(place): spec
    for place, spec in {
        "status": _PyField(PYTHON_TYPES, PySymbol("Response"), PySymbol("status")),
        "type": _PyField(PYTHON_TYPES, PySymbol("Response"), PySymbol("type")),
        "results/type": _PyField(PYTHON_TYPES, PySymbol("PropertyResultEntry"), PySymbol("type")),
        "results/status <property>": _PyField(
            PYTHON_TYPES, PySymbol("PropertyResultEntry"), PySymbol("status")
        ),
        "warnings/kind": _PyField(PYTHON_TYPES, PySymbol("CompleteWarning"), PySymbol("kind")),
        "issues/severity": _PyEnum(PYTHON_ISSUE_CODES, PySymbol("IssueSeverity")),
        "warnings/severity": _PyEnum(PYTHON_ISSUE_CODES, PySymbol("IssueSeverity")),
        "bound_kind": _PyBoundKinds(),
        "dbc/messages/signals/byteOrder": _PyAlias(PYTHON_DBC_TYPES, PySymbol("ByteOrder")),
        "dbc/messages/signals/presence": _PyAlias(PYTHON_DBC_TYPES, PySymbol("SignalPresence")),
        "dbc/messages/signals/multiplexor": AnyNonEmpty(),
        "dbc/comments/target/kind": _PyField(
            PYTHON_DBC_TYPES, PySymbol("DBCCommentTarget"), PySymbol("kind")
        ),
        "dbc/attributes/kind": _PyField(
            PYTHON_DBC_TYPES, PySymbol("DBCAttribute"), PySymbol("kind")
        ),
        "dbc/attributes/scope <definition>": _PyAlias(PYTHON_DBC_TYPES, PySymbol("AttrScope")),
        "dbc/attributes/attrType/kind": _PyField(
            PYTHON_DBC_TYPES, PySymbol("DBCAttrType"), PySymbol("kind")
        ),
        "dbc/attributes/value/kind": _PyField(
            PYTHON_DBC_TYPES, PySymbol("DBCAttrValue"), PySymbol("kind")
        ),
        "dbc/attributes/target/kind": _PyField(
            PYTHON_DBC_TYPES, PySymbol("DBCAttrTarget"), PySymbol("kind")
        ),
    }.items()
}


@dataclass(frozen=True)
class _GoSwitch:
    """The ``case`` literals of the one ``switch`` a function holds, the reader's dispatch."""

    module: Path
    function: GoSymbol


@dataclass(frozen=True)
class _GoWordCall:
    """The literals a function's ``fieldWord`` calls at a key await."""

    module: Path
    function: GoSymbol
    key: ReplyWord


@dataclass(frozen=True)
class _GoConsts:
    """The string constants of a named type, declared in any file of its package."""

    module: Path
    name: GoSymbol


@dataclass(frozen=True)
class _GoValues:
    """The values of a struct of one string field, declared in one ``var`` block of a file.

    A value given its word anywhere else could hold a word the block does not,
    so the gate refuses, where it stands, a value of the type built or
    converted to outside the block, an alias of the type, a type parameter it
    constrains, an unnamed struct a value of it is assigned from, and its field
    reached outside ``reader``.
    """

    module: Path
    name: GoSymbol
    field: GoSymbol
    reader: GoSymbol


@dataclass(frozen=True)
class _GoBoundKinds:
    """The ``BoundKind*`` codes of ``go/aletheia/limits.go``."""


type _GoSet = _GoSwitch | _GoWordCall | _GoConsts | _GoValues | _GoBoundKinds

# Every row of `replyText`, with the set the Go reader takes at its place, read
# from the reader's own code, under the rules PYTHON_REPLY_TEXT is held to.
GO_REPLY_TEXT: dict[ReplyPlace, _GoSet | AnyNonEmpty] = {
    ReplyPlace(place): spec
    for place, spec in {
        "status": _GoValues(
            GO_RESPONSE, GoSymbol("replyStatus"), GoSymbol("word"), GoSymbol("fieldStatus")
        ),
        "type": _GoWordCall(GO_RESPONSE, GoSymbol("parseFrameResponse"), ReplyWord("type")),
        "results/type": _GoSwitch(GO_RESPONSE, GoSymbol("parsePropertyEvent")),
        "results/status <property>": _GoSwitch(GO_RESPONSE, GoSymbol("readVerdict")),
        "warnings/kind": _GoConsts(GO_RESULT, GoSymbol("WarningKind")),
        "issues/severity": _GoSwitch(GO_RESPONSE, GoSymbol("readSeverity")),
        "warnings/severity": _GoSwitch(GO_RESPONSE, GoSymbol("readSeverity")),
        "bound_kind": _GoBoundKinds(),
        "dbc/messages/signals/byteOrder": _GoSwitch(GO_DBC, GoSymbol("readByteOrder")),
        "dbc/messages/signals/presence": _GoSwitch(GO_DBC, GoSymbol("parseSignalPresence")),
        "dbc/messages/signals/multiplexor": AnyNonEmpty(),
        "dbc/comments/target/kind": _GoSwitch(GO_DBC, GoSymbol("parseCommentTarget")),
        "dbc/attributes/kind": _GoSwitch(GO_DBC, GoSymbol("parseAttribute")),
        "dbc/attributes/scope <definition>": _GoSwitch(GO_DBC, GoSymbol("readAttrScope")),
        "dbc/attributes/attrType/kind": _GoSwitch(GO_DBC, GoSymbol("parseAttrType")),
        "dbc/attributes/value/kind": _GoSwitch(GO_DBC, GoSymbol("parseAttrValue")),
        "dbc/attributes/target/kind": _GoSwitch(GO_DBC, GoSymbol("parseAttrTarget")),
    }.items()
}


# Every row of `replyNonEmpty`: the arrays a reader takes as holding at least
# one element.
REPLY_NON_EMPTY: frozenset[ReplyPlace] = frozenset(
    {
        ReplyPlace("results <property_batch>"),
        ReplyPlace("dbc/messages/signals/multiplex_values"),
    }
)

# The set a reader takes at a place: its words, or any non-empty text.
type _ReaderSet = frozenset[ReplyWord] | AnyNonEmpty


@dataclass(frozen=True)
class UnnamedLast:
    """A last arm that names no word, reading every word the arms before it do not."""


# A reader's last arm: the word it names, or none.
type _LastArm = ReplyWord | UnnamedLast


@dataclass(frozen=True)
class Arms:
    """The words a reader's arms name, and its last arm, which reads every word outside them."""

    words: frozenset[ReplyWord]
    last: _LastArm


@dataclass(frozen=True)
class ReaderSets:
    """A binding's reader set at each place its table names, and each last arm it reads."""

    reader: Prose
    table: Prose
    text: dict[ReplyPlace, _ReaderSet]
    last_arms: dict[ReplyPlace, _LastArm]


@dataclass(frozen=True)
class ReplyTables:
    """The reply proof's two tables and each binding's reader set at each place."""

    agda_text: dict[ReplyPlace, _OneOf | AnyNonEmpty]
    agda_non_empty: frozenset[ReplyPlace]
    readers: tuple[ReaderSets, ...]


# The two tables, and the clauses of them the gate reads past: the catch-alls,
# which leave every other place free and every other array possibly empty.
_TABLES = frozenset({AgdaText("replyText"), AgdaText("replyNonEmpty")})
_CATCH_ALLS = frozenset(
    {AgdaText("replyText _ _ = nothing"), AgdaText("replyNonEmpty _ _ = false")}
)
# A clause of `replyText` or `replyNonEmpty`: the path's keys, the type it
# depends on (`nothing` or `(just "<type>")`) and the right-hand side.
_REPLY_CLAUSE = re.compile(
    r"^(?P<table>replyText|replyNonEmpty)\s+\((?P<path>[^)]*)\)\s+"
    + r'(?:nothing|\(just\s+"(?P<type>[^"]*)"\))\s*=\s*(?P<rhs>.*)$'
)
# A definition with no arguments, `scopes = "network" ∷ ... ∷ []`.
_DEFINITION = re.compile(r"^(?P<name>[a-z][A-Za-z]*) = (?P<body>.*)$")
_ONE_OF_NAMED = re.compile(r"^just\s+\(oneOf\s+(?P<name>[a-z][A-Za-z]*)\)$")
_ONE_OF_LITERAL = re.compile(r"^just\s+\(oneOf\s+\((?P<body>.*)\)\)$")
_QUOTED_WORD = re.compile(r'^"(?P<word>[^"]*)"$')
# An innermost block comment, `{- ... -}` holding no other.
_BLOCK_COMMENT = re.compile(r"\{-(?:(?!\{-|-\}).)*?-\}", flags=re.DOTALL)


def _without_block_comments(text: AgdaText) -> AgdaText:
    """Return the module with each block comment, nested ones too, blanked to its line breaks."""
    while (comment := _BLOCK_COMMENT.search(text)) is not None:
        blank = re.sub(r"[^\n]", " ", comment.group())
        text = AgdaText(text[: comment.start()] + blank + text[comment.end() :])
    return text


def _clauses(text: AgdaText) -> Iterator[AgdaText]:
    """Yield each clause of the module, its indented continuation lines joined to it."""
    clause: list[AgdaText] = []
    for line in text.splitlines():
        if line.startswith((" ", "\t")) and clause:
            clause.append(AgdaText(line.strip()))
            continue
        if clause:
            yield AgdaText(" ".join(clause))
        clause = [AgdaText(line)]
    if clause:
        yield AgdaText(" ".join(clause))


def _list_words(body: AgdaText) -> list[ReplyWord] | None:
    """Return the words of a `"a" ∷ "b" ∷ []` list, or None when an element is not a quoted word."""
    *elements, end = (element.strip() for element in body.split("∷"))
    quoted = [_QUOTED_WORD.match(element) for element in elements]
    if end != "[]" or None in quoted:
        return None
    return [ReplyWord(word.group("word")) for word in quoted if word is not None]


def _text_form(rhs: AgdaText, named: dict[AgdaText, AgdaText]) -> _OneOf | AnyNonEmpty | None:
    """Return the form a `replyText` row's right-hand side names, or None when none reads it."""
    if rhs == "just anyNonEmpty":
        return AnyNonEmpty()
    if (one_of := _ONE_OF_NAMED.match(rhs)) is not None:
        body = named.get(AgdaText(one_of.group("name")))
        words = None if body is None else _list_words(body)
    elif (one_of := _ONE_OF_LITERAL.match(rhs)) is not None:
        words = _list_words(AgdaText(one_of.group("body")))
    else:
        return None
    return None if words is None else _OneOf(frozenset(words), words[-1] if words else None)


def _table_of(clause: AgdaText) -> AgdaText | None:
    """Return the table a clause defines a row of, or None for every other clause.

    A table's type signature and its catch-all are not rows, so they too give None.
    """
    words = clause.split()
    if not words or words[0] not in _TABLES or words[1:2] == [":"]:
        return None
    return None if " ".join(words) in _CATCH_ALLS else AgdaText(words[0])


def _parse_agda_reply_places(
    text: AgdaText,
) -> tuple[dict[ReplyPlace, _OneOf | AnyNonEmpty], frozenset[ReplyPlace], list[Prose]]:
    """Return the `replyText` rows, the `replyNonEmpty` places and every clause no form reads."""
    clauses = list(_clauses(_without_block_comments(text)))
    named = {
        AgdaText(m.group("name")): AgdaText(m.group("body"))
        for clause in clauses
        if (m := _DEFINITION.match(clause)) is not None
    }
    text_rows: dict[ReplyPlace, _OneOf | AnyNonEmpty] = {}
    non_empty: set[ReplyPlace] = set()
    unread: list[Prose] = []
    for clause in clauses:
        table = _table_of(clause)
        if table is None:
            continue
        m = _REPLY_CLAUSE.match(clause)
        keys = None if m is None else _list_words(AgdaText(m.group("path")))
        if m is None or keys is None:
            unread.append(
                Prose(
                    f"{table} clause {' '.join(clause.split())!r}: "
                    + "not a path of quoted keys, a type and a form"
                )
            )
            continue
        typed = f" <{m.group('type')}>" if m.group("type") is not None else ""
        place = ReplyPlace("/".join(keys) + typed)
        rhs = AgdaText(m.group("rhs").strip())
        form = _text_form(rhs, named) if table == "replyText" else None
        if place in (text_rows if table == "replyText" else non_empty):
            unread.append(Prose(f"{table} has two rows for {place}"))
        elif table == "replyNonEmpty" and rhs == "true":
            non_empty.add(place)
        elif form is not None:
            text_rows[place] = form
        else:
            unread.append(Prose(f"{table} row {place} has a form this gate does not read: {rhs!r}"))
    return text_rows, frozenset(non_empty), unread


def _top_level(module: ast.Module) -> dict[PySymbol, ast.stmt]:
    """Return each name a module binds at its top level: an alias, a constant or a class."""
    bound: dict[PySymbol, ast.stmt] = {}
    for node in module.body:
        if isinstance(node, ast.ClassDef):
            bound[PySymbol(node.name)] = node
        elif isinstance(node, ast.TypeAlias):
            bound[PySymbol(node.name.id)] = node
        elif isinstance(node, ast.Assign) and len(node.targets) == 1:
            target = node.targets[0]
            if isinstance(target, ast.Name):
                bound[PySymbol(target.id)] = node
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            bound[PySymbol(node.target.id)] = node
    return bound


def _alias_value(node: ast.stmt) -> ast.expr | None:
    """Return the expression an alias or a constant binds, or None for a class."""
    if isinstance(node, ast.TypeAlias | ast.Assign | ast.AnnAssign):
        return node.value
    return None


def _literal_words(node: ast.expr, bound: dict[PySymbol, ast.stmt]) -> frozenset[ReplyWord] | None:
    """Return the words of a ``Literal``, through aliases and ``NotRequired``, or None."""
    if isinstance(node, ast.Name) and PySymbol(node.id) in bound:
        value = _alias_value(bound[PySymbol(node.id)])
        return None if value is None else _literal_words(value, bound)
    if not isinstance(node, ast.Subscript) or not isinstance(node.value, ast.Name):
        return None
    if node.value.id in {"NotRequired", "Required"}:
        return _literal_words(node.slice, bound)
    if node.value.id != "Literal":
        return None
    args = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
    words = [
        ReplyWord(arg.value)
        for arg in args
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str)
    ]
    return frozenset(words) if len(words) == len(args) else None


def _union_members(node: ast.expr) -> list[ast.expr]:
    """Return the members of an ``A | B | C`` union, or the expression alone."""
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return _union_members(node.left) + _union_members(node.right)
    return [node]


def _field_words(spec: _PyField, bound: dict[PySymbol, ast.stmt]) -> frozenset[ReplyWord] | Prose:
    """Return the words of a field over a class or a union of classes, some class holding it."""
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.name}.{spec.field}"
    node = bound.get(spec.name)
    if node is None:
        return Prose(f"{where}: {spec.name} is not defined")
    value = _alias_value(node)
    members = (
        [node]
        if value is None
        else [
            bound.get(PySymbol(member.id)) if isinstance(member, ast.Name) else None
            for member in _union_members(value)
        ]
    )
    words: set[ReplyWord] = set()
    seen = False
    for member in members:
        if not isinstance(member, ast.ClassDef):
            return Prose(f"{where}: a member of {spec.name} is not a class of the module")
        if [ast.unparse(base) for base in member.bases] != ["TypedDict"]:
            return Prose(
                f"{where}: {member.name} derives from more than TypedDict, "
                + "and the gate reads a class's own fields only"
            )
        for item in member.body:
            if (
                isinstance(item, ast.AnnAssign)
                and isinstance(item.target, ast.Name)
                and item.target.id == spec.field
            ):
                found = _literal_words(item.annotation, bound)
                if found is None:
                    return Prose(f"{where}: {member.name}.{spec.field} is not a Literal of strings")
                words |= found
                seen = True
    if not seen:
        return Prose(f"{where}: no class of {spec.name} has the field {spec.field}")
    return frozenset(words)


def _enum_words(spec: _PyEnum, node: ast.ClassDef) -> frozenset[ReplyWord] | Prose:
    """Return the values of a ``StrEnum``'s members, each a string constant."""
    words: set[ReplyWord] = set()
    for item in node.body:
        if isinstance(item, ast.Assign):
            member, value = item.targets[0], item.value
        elif isinstance(item, ast.AnnAssign) and item.value is not None:
            member, value = item.target, item.value
        else:
            continue
        if not (isinstance(value, ast.Constant) and isinstance(value.value, str)):
            return Prose(
                f"{spec.module.relative_to(REPO_ROOT)}:{spec.name}.{ast.unparse(member)} "
                + "is not a string constant"
            )
        words.add(ReplyWord(value.value))
    return frozenset(words)


def _named_words(
    spec: _PyAlias | _PyEnum, bound: dict[PySymbol, ast.stmt]
) -> frozenset[ReplyWord] | Prose:
    """Return the words of a ``Literal`` alias or a ``StrEnum``."""
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.name}"
    node = bound.get(spec.name)
    if node is None:
        return Prose(f"{where} is not defined")
    if isinstance(spec, _PyEnum):
        if not isinstance(node, ast.ClassDef):
            return Prose(f"{where} is not a class")
        return _enum_words(spec, node)
    value = _alias_value(node)
    found = None if value is None else _literal_words(value, bound)
    return Prose(f"{where} is not a Literal of strings") if found is None else found


def _python_words(spec: _PySet, py_codes: frozenset[ReplyWord]) -> frozenset[ReplyWord] | Prose:
    """Return the words a Python reader set holds, or why the gate cannot read them."""
    if isinstance(spec, _PyBoundKinds):
        return py_codes
    if not spec.module.is_file():
        return Prose(f"{spec.module.relative_to(REPO_ROOT)} not found")
    bound = _top_level(ast.parse(spec.module.read_text(encoding="utf-8")))
    if isinstance(spec, _PyField):
        return _field_words(spec, bound)
    return _named_words(spec, bound)


# A Go interpreted string, raw string or rune literal, or a comment, matched
# from the left so that a `//` inside a literal is not taken for a comment.
_GO_TOKEN = re.compile(
    r'"(?:[^"\\\n]|\\.)*"|`[^`]*`|' + r"'(?:[^'\\\n]|\\.)*'|//[^\n]*|/\*.*?\*/",
    flags=re.DOTALL,
)
# A Go or C++ string literal holding a reply word, which has no escape.
_WORD_LITERAL = re.compile(r'^"(?P<word>[^"\\]*)"$')
# A statement whose clauses are `case` clauses, and one such clause on a line.
_GO_CASE_HOLDER = re.compile(r"\b(?:switch|select)\b")
_GO_CASE = re.compile(r"^case\s+(?P<exprs>.*):$")
# A `fieldWord` call whose arguments hold no call of their own.
_GO_WORD_CALL = re.compile(r"\bfieldWord\((?P<args>[^()]*)\)")


def _go_code(text: GoText) -> GoText:
    """Return Go source with each comment blanked to its line breaks and its literals kept."""
    return GoText(
        _GO_TOKEN.sub(
            lambda token: (
                re.sub(r"[^\n]", " ", token.group())
                if token.group().startswith("/")
                else token.group()
            ),
            text,
        )
    )


def _go_bare_lines(code: GoText) -> list[GoText]:
    """Return the lines of Go source whose comments are blanked, each literal blanked too."""
    bare = _GO_TOKEN.sub(lambda token: re.sub(r"[^\n]", " ", token.group()), code)
    return [GoText(line) for line in bare.split("\n")]


def _go_package() -> dict[Path, GoText]:
    """Return every non-test file of the Go package, its comments blanked."""
    return {
        path: _go_code(GoText(path.read_text(encoding="utf-8")))
        for path in sorted(GO_PACKAGE.glob("*.go"))
        if not path.name.endswith("_test.go")
    }


def _go_function(code: GoText, name: GoSymbol) -> GoText | None:
    """Return a top-level function up to the brace gofmt closes it with, or None when absent."""
    start = re.search(rf"^func {re.escape(name)}[\[(]", code, flags=re.MULTILINE)
    if start is None:
        return None
    end = code.find("\n}", start.end())
    return GoText(code[start.start() : None if end < 0 else end])


def word_literals(exprs: GoText | CppText) -> frozenset[ReplyWord] | None:
    """Return the words of a comma-separated list of string literals, or None when one is not."""
    found = [_WORD_LITERAL.match(expr.strip()) for expr in exprs.split(",")]
    if None in found:
        return None
    return frozenset(ReplyWord(word.group("word")) for word in found if word is not None)


def _switch_words(body: GoText) -> frozenset[ReplyWord] | Prose:
    """Return the words the ``case`` clauses of a function's one ``switch`` name."""
    holders = len(_GO_CASE_HOLDER.findall(_GO_TOKEN.sub('""', body)))
    if holders != 1:
        return Prose(f"the function holds {holders} switch or select statements, not one")
    words: set[ReplyWord] = set()
    for line in body.splitlines():
        clause = line.strip()
        if re.match(r"case\b", clause) is None:
            continue
        case = _GO_CASE.match(clause)
        found = None if case is None else word_literals(GoText(case.group("exprs")))
        if found is None:
            return Prose(f"{clause!r} is not a case of string literals on one line")
        words |= found
    return frozenset(words) if words else Prose("the function's switch names no case")


def _word_call_words(body: GoText, key: ReplyWord) -> frozenset[ReplyWord] | Prose:
    """Return the words a function's ``fieldWord`` calls at ``key`` await."""
    calls = list(_GO_WORD_CALL.finditer(body))
    if len(calls) != len(re.findall(r"\bfieldWord\(", body)):
        return Prose("a fieldWord call holds a call of its own")
    words: set[ReplyWord] = set()
    for call in calls:
        args = [GoText(arg.strip()) for arg in call.group("args").split(",")]
        at = _WORD_LITERAL.match(args[2]) if args[3:] else None
        if at is None:
            return Prose(f"fieldWord({call.group('args')}) names no literal key or no word")
        if at.group("word") != key:
            continue
        found = word_literals(GoText(",".join(args[3:])))
        if found is None:
            return Prose(f"fieldWord({call.group('args')}) awaits a word that is not a literal")
        words |= found
    return frozenset(words) if words else Prose(f"no fieldWord call at {key!r}")


def _const_specs(code: GoText) -> Iterator[GoText]:
    """Yield each constant spec of a file, a group's lines one by one."""
    group = False
    for line in code.splitlines():
        spec = line.strip()
        if spec == "const (":
            group = True
        elif group and spec == ")":
            group = False
        elif group and spec:
            yield GoText(spec)
        elif spec.startswith("const "):
            yield GoText(spec.removeprefix("const ").strip())


def _const_words(spec: _GoConsts, package: dict[Path, GoText]) -> frozenset[ReplyWord] | Prose:
    """Return the values of every constant of a named string type in the package."""
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.name}"
    name = re.escape(spec.name)
    declared = package.get(spec.module)
    if declared is None or re.search(rf"^type {name} string\s*$", declared, re.MULTILINE) is None:
        return Prose(f"{where} is not declared as a string type")
    typed = re.compile(rf"^\w+\s+{name}\s*=\s*(?P<value>.*)$")
    words: set[ReplyWord] = set()
    for path, code in package.items():
        for const in _const_specs(code):
            if re.search(rf"\b{name}\b", const) is None:
                continue
            m = typed.match(const)
            word = None if m is None else _WORD_LITERAL.match(m.group("value").strip())
            if word is None:
                return Prose(
                    f"{path.relative_to(REPO_ROOT)}: the constant {const!r} of {spec.name} "
                    + "is not one name and one string literal"
                )
            words.add(ReplyWord(word.group("word")))
    return frozenset(words) if words else Prose(f"{where} has no constant")


# A line of a Go file, its number first; and a line of a file of the Go package.
type _GoNumbered = tuple[GoLine, GoText]
type _GoSite = tuple[Path, GoLine]


def _var_blocks(code: GoText) -> Iterator[list[_GoNumbered]]:
    """Yield each ``var ( ... )`` group of a file: its non-blank lines and their numbers."""
    block: list[_GoNumbered] | None = None
    for number, line in enumerate(code.split("\n"), start=1):
        spec = line.strip()
        if spec == "var (":
            block = []
        elif block is not None and spec == ")":
            yield block
            block = None
        elif block is not None and spec:
            block.append((GoLine(number), GoText(spec)))


def fragment_lines(code: GoText | CppText, fragment: GoText | CppText) -> range:
    """Return the numbers of the lines, from 1, a fragment of a file spans."""
    start = code.index(fragment)
    return range(code.count("\n", 0, start) + 1, code.count("\n", 0, start + len(fragment)) + 2)


def _go_function_lines(code: GoText, name: GoSymbol) -> frozenset[GoLine]:
    """Return the lines a top-level function spans, none when the file does not define it."""
    body = _go_function(code, name)
    return frozenset() if body is None else frozenset(map(GoLine, fragment_lines(code, body)))


@dataclass(frozen=True)
class _GoBreach:
    """A line shape that could give a value its word outside its block, and the lines exempt."""

    regex: GoRegex
    what: Prose
    exempt: frozenset[_GoSite]


def _value_breaches(
    spec: _GoValues, block: frozenset[_GoSite], declared: _GoSite, reader: frozenset[_GoSite]
) -> tuple[_GoBreach, ...]:
    """Return the line shapes that could give a value of the type a word outside its block."""
    name, field = re.escape(spec.name), re.escape(spec.field)
    return (
        _GoBreach(
            GoRegex(rf"\b{name}\s*\{{"), Prose(f"builds a {spec.name} outside its block"), block
        ),
        _GoBreach(
            GoRegex(rf"\b{name}\s*\("), Prose(f"converts a value to {spec.name}"), frozenset()
        ),
        _GoBreach(
            GoRegex(rf"=\s*{name}\b(?!\s*[{{(])"), Prose(f"aliases {spec.name}"), frozenset()
        ),
        _GoBreach(
            GoRegex(rf"\[\s*\w+(?:\s*,\s*\w+)*\s+~?(?:interface\s*\{{[^}}]*)?\b{name}\b"),
            Prose(f"constrains a type parameter to {spec.name}"),
            frozenset(),
        ),
        _GoBreach(
            GoRegex(rf"\bstruct\s*\{{\s*{field}\s+string\s*\}}"),
            Prose(f"declares an unnamed struct a {spec.name} is assigned from"),
            frozenset({declared}),
        ),
        _GoBreach(
            GoRegex(rf"\.{field}\b"),
            Prose(f"reaches the {spec.field} of a value outside {spec.reader}"),
            reader,
        ),
    )


def _values_built_elsewhere(
    spec: _GoValues, package: dict[Path, GoText], block: frozenset[_GoSite], declared: _GoSite
) -> Iterator[Prose]:
    """Yield each line of the package that could give a value of the type a word elsewhere."""
    reader = frozenset(
        (path, number)
        for path, code in package.items()
        for number in _go_function_lines(code, spec.reader)
    )
    breaches = _value_breaches(spec, block, declared, reader)
    for path, code in package.items():
        bare = _go_bare_lines(code)
        for number, (line, shown) in enumerate(zip(bare, code.split("\n"), strict=True), start=1):
            for breach in breaches:
                if re.search(breach.regex, line) and (path, GoLine(number)) not in breach.exempt:
                    yield Prose(
                        f"{path.relative_to(REPO_ROOT)}:{number}: {shown.strip()!r} {breach.what}"
                    )


def _value_words(spec: _GoValues, package: dict[Path, GoText]) -> frozenset[ReplyWord] | Prose:
    """Return the words of a type's one block of values, or each line that hides them."""
    where = spec.module.relative_to(REPO_ROOT)
    code = package.get(spec.module, GoText(""))
    declaration = f"type {spec.name} struct{{ {spec.field} string }}"
    at = [
        GoLine(number)
        for number, line in enumerate(code.split("\n"), start=1)
        if line.rstrip() == declaration
    ]
    if len(at) != 1:
        return Prose(f"{where}:{spec.name} is not declared once as {declaration!r}")
    name = re.escape(spec.name)
    blocks = [
        block
        for block in _var_blocks(code)
        if any(re.search(rf"\b{name}\b", line) for _, line in block)
    ]
    if len(blocks) != 1:
        return Prose(f"{where}:{spec.name}: {len(blocks)} var blocks declare its values, not one")
    value = re.compile(rf'^\w+\s*=\s*{name}\{{"(?P<word>[^"\\]*)"\}}$')
    words: set[ReplyWord] = set()
    unread: list[Prose] = []
    for number, line in blocks[0]:
        if (m := value.match(line)) is None:
            unread.append(
                Prose(f"{where}:{number}: {line!r} is not one name and one {spec.name} of a word")
            )
        else:
            words.add(ReplyWord(m.group("word")))
    block = frozenset((spec.module, number) for number, _ in blocks[0])
    unread.extend(_values_built_elsewhere(spec, package, block, (spec.module, at[0])))
    return Prose("; ".join(unread)) if unread else frozenset(words)


def _go_words(
    spec: _GoSet, go_codes: frozenset[ReplyWord], package: dict[Path, GoText]
) -> frozenset[ReplyWord] | Prose:
    """Return the words a Go reader set holds, or why the gate cannot read them."""
    if isinstance(spec, _GoBoundKinds):
        return go_codes
    if isinstance(spec, _GoConsts):
        return _const_words(spec, package)
    if isinstance(spec, _GoValues):
        return _value_words(spec, package)
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.function}"
    code = package.get(spec.module)
    body = None if code is None else _go_function(code, spec.function)
    if body is None:
        return Prose(f"{where} is not defined")
    found = _switch_words(body) if isinstance(spec, _GoSwitch) else _word_call_words(body, spec.key)
    return Prose(f"{where}: {found}") if isinstance(found, str) else found


def read_sets[S](
    reader: Prose,
    name: Prose,
    table: dict[ReplyPlace, S | AnyNonEmpty],
    read: Callable[[S], frozenset[ReplyWord] | Arms | Prose],
    unread: list[Prose],
) -> ReaderSets:
    """Return the set and last arm at each place a binding's table names; unread gets the rest."""
    sets: dict[ReplyPlace, _ReaderSet] = {}
    last_arms: dict[ReplyPlace, _LastArm] = {}
    for place, spec in table.items():
        found = spec if isinstance(spec, AnyNonEmpty) else read(spec)
        if isinstance(found, str):
            unread.append(Prose(f"reply place {place}: {found}"))
        elif isinstance(found, Arms):
            sets[place] = found.words
            last_arms[place] = found.last
        else:
            sets[place] = found
    return ReaderSets(reader, name, sets, last_arms)


# A binding's reader: it returns its sets, adding each place none reads to the
# list it is given.
type BindingReader = Callable[[list[Prose]], ReaderSets]


def python_reader(py_codes: frozenset[ReplyWord]) -> BindingReader:
    """Return the Python reader, whose bound kinds are ``py_codes``."""
    return lambda unread: read_sets(
        Prose("the Python reader"),
        Prose("PYTHON_REPLY_TEXT"),
        PYTHON_REPLY_TEXT,
        lambda spec: _python_words(spec, py_codes),
        unread,
    )


def go_reader(go_codes: frozenset[ReplyWord]) -> BindingReader:
    """Return the Go reader, whose bound kinds are ``go_codes``."""

    def read(unread: list[Prose]) -> ReaderSets:
        package = _go_package()
        return read_sets(
            Prose("the Go reader"),
            Prose("GO_REPLY_TEXT"),
            GO_REPLY_TEXT,
            lambda spec: _go_words(spec, go_codes, package),
            unread,
        )

    return read


def read_reply_tables(
    text: AgdaText, readers: tuple[BindingReader, ...]
) -> ReplyTables | list[Prose]:
    """Return both tables of ``text`` and each binding's sets, or each clause or set none reads."""
    agda_text, agda_non_empty, unread = _parse_agda_reply_places(text)
    if not agda_text or not agda_non_empty:
        unread.append(Prose("no replyText or replyNonEmpty rows parsed"))
    sets = tuple(read(unread) for read in readers)
    return unread or ReplyTables(agda_text, agda_non_empty, sets)


def _one_side(
    place: ReplyPlace,
    left: tuple[Prose, frozenset[ReplyWord]],
    right: tuple[Prose, frozenset[ReplyWord]],
) -> list[Prose]:
    """Return a divergence per word one side of a place holds and the other does not."""
    return [
        Prose(f"reply place {place}: '{word}' is in {side} only")
        for (side, words), (_, other) in ((left, right), (right, left))
        for word in sorted(words - other)
    ]


def _last_arm_diff(
    place: ReplyPlace,
    row: _OneOf,
    words: frozenset[ReplyWord],
    last: _LastArm | None,
    reader: Prose,
) -> Prose | None:
    """Return how a reader's last arm reads other than the row's last word, or None.

    An arm that names no word reads the row's last word, so no other arm may name it.
    """
    if last is None or last == row.last:
        return None
    if row.last is None:
        return Prose(f"reply place {place}: replyText names no word for {reader}'s last arm")
    if not isinstance(last, UnnamedLast):
        return Prose(f"reply place {place}: {reader}'s last arm names '{last}', not '{row.last}'")
    if row.last in words:
        return Prose(f"reply place {place}: {reader} names '{row.last}', which its last arm reads")
    return None


def _check_reader(
    agda_text: dict[ReplyPlace, _OneOf | AnyNonEmpty], reader: ReaderSets
) -> list[Prose]:
    """Return the divergences between ``replyText`` and one binding's reader sets."""
    diffs: list[Prose] = []
    for place, words in reader.text.items():
        row = agda_text.get(place)
        if row is None:
            diffs.append(
                Prose(
                    f"reply place {place}: replyText has no row for this {reader.table} place, "
                    + "so the proof holds nothing there"
                )
            )
        elif isinstance(words, AnyNonEmpty) or isinstance(row, AnyNonEmpty):
            if not (isinstance(words, AnyNonEmpty) and isinstance(row, AnyNonEmpty)):
                diffs.append(
                    Prose(
                        f"reply place {place}: one side reads any non-empty text, "
                        + f"the other a word set ({reader.reader})"
                    )
                )
        else:
            last = reader.last_arms.get(place)
            if (diff := _last_arm_diff(place, row, words, last, reader.reader)) is not None:
                diffs.append(diff)
            unnamed: frozenset[ReplyWord] = frozenset(
                {row.last} if isinstance(last, UnnamedLast) and row.last is not None else ()
            )
            diffs.extend(
                _one_side(place, (Prose("replyText"), row.words), (reader.reader, words | unnamed))
            )
    diffs.extend(
        Prose(f"reply place {place}: replyText has a row {reader.table} does not name")
        for place in sorted(agda_text.keys() - reader.text.keys())
    )
    return diffs


def check_reply_places(tables: ReplyTables, agda_codes: frozenset[ReplyWord]) -> list[Prose]:
    """Return the divergences between the reply proof's tables and every binding's sets."""
    diffs = [diff for reader in tables.readers for diff in _check_reader(tables.agda_text, reader)]
    diffs.extend(
        Prose(f"reply place {place}: replyNonEmpty has no row, so the proof allows an empty array")
        for place in sorted(REPLY_NON_EMPTY - tables.agda_non_empty)
    )
    diffs.extend(
        Prose(f"reply place {place}: replyNonEmpty has a row REPLY_NON_EMPTY does not name")
        for place in sorted(tables.agda_non_empty - REPLY_NON_EMPTY)
    )
    bound_row = tables.agda_text.get(ReplyPlace("bound_kind"))
    if isinstance(bound_row, _OneOf):
        diffs.extend(
            _one_side(
                ReplyPlace("bound_kind"),
                (Prose("replyText"), bound_row.words),
                (Prose("boundKindCode"), agda_codes),
            )
        )
    return diffs
