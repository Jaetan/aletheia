# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags arm of ``tools/check_limits_parity.py``.

The reply proof in ``src/Aletheia/Protocol/ReplyRange.agda`` lists, in
``replyText``, the words the kernel writes at each string place of a reply and,
in ``replyNonEmpty``, the arrays it writes with at least one element.  It leaves
a place no row names free, so this module holds each row a reader relies on: it
reads both tables and the set each Python reader takes at the place from its
type or its ``field_word`` call, runs the readers of ``tools/_reply_places_go.py``,
``tools/_reply_places_cpp.py`` and ``tools/_reply_places_rust.py``, which read
the set each Go, C++ and Rust reader takes from its own code, and reports a row
one side drops, a word one side holds alone and a last arm, which reads every
word its other arms do not name, other than the row's last word.

A clause of either table, or a reader's type or code, that the module cannot
read is reported rather than passed over, every one of them in one run; the
two catch-all clauses, which leave every other place free, and the tables' type
signatures are the only clauses it reads past.  A ``replyText`` word that is
not identifier-shaped is reported too, since that shape is what tells a Go or
Rust reader's word comparison from a comparison of other text.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, replace
from pathlib import Path
from typing import TYPE_CHECKING, NewType

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator

REPO_ROOT = Path(__file__).resolve().parent.parent
AGDA_REPLY_RANGE = REPO_ROOT / "src" / "Aletheia" / "Protocol" / "ReplyRange.agda"
PYTHON_TYPES = REPO_ROOT / "python" / "aletheia" / "types.py"
PYTHON_ISSUE_CODES = REPO_ROOT / "python" / "aletheia" / "codes" / "_issue.py"
PYTHON_DBC_NORMALIZE = (
    REPO_ROOT / "python" / "aletheia" / "client" / "_helpers" / "dbc_normalize.py"
)

# A reply place: the keys from the reply's root joined by "/", then, when the
# row depends on it, the `kind` or `type` its object carries in angle brackets.
ReplyPlace = NewType("ReplyPlace", str)
# A string the kernel writes at a reply place.
ReplyWord = NewType("ReplyWord", str)
# The shape of every reply word, which the gate holds `replyText` to: a reader
# comparing a literal of any other text compares no word.
WORD_SHAPE = r"[A-Za-z_][A-Za-z0-9_]*"
# A top-level name in a Python module: an alias, a class, a field or a function.
PySymbol = NewType("PySymbol", str)
# Python source: a module.
PyText = NewType("PyText", str)
# Agda source: a module, a clause of it or a fragment of a clause.
AgdaText = NewType("AgdaText", str)
# A top-level name in a Go package: a function or a type.
GoSymbol = NewType("GoSymbol", str)
# Go source: a file, a function of it or a fragment of either.
GoText = NewType("GoText", str)
# The number of a line of a Go file, from 1.
GoLine = NewType("GoLine", int)
# A name in the C++ library: a function, a table, an enum or an enumerator.
CppSymbol = NewType("CppSymbol", str)
# C++ source: a file, a function of it or a fragment of either.
CppText = NewType("CppText", str)
# The number of a line of a C++ file, from 1.
CppLine = NewType("CppLine", int)
# The text between a Go, Rust or C++ string literal's quotes, as written or as read.
LiteralText = NewType("LiteralText", str)
# The number a Go, Rust or C++ Unicode escape names.
CodePoint = NewType("CodePoint", int)


@dataclass(frozen=True)
class _OneOf:
    """A place that holds one of a fixed set of words; ``last`` is its list's last, if any."""

    words: frozenset[ReplyWord]
    last: ReplyWord | None


@dataclass(frozen=True)
class AnyNonEmpty:
    """A place that holds any text but the empty one."""


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


@dataclass(frozen=True)
class _PyWordCall:
    """The literals a function's ``field_word`` calls at a key await."""

    module: Path
    function: PySymbol
    key: ReplyWord


@dataclass(frozen=True)
class _PyMappedWordCall:
    """The words a function's one ``field_word`` call at a key awaits, and the tests mapping them.

    The call is compared where it is read, as the whole test ``field_word(...) ==
    "<literal>"`` of an ``if`` of the function's body, or a statement of that body
    assigns it to a name, used nowhere but as the whole left of each test ``<name>
    == "<literal>"`` of a chain of ``if``s there, assignments alone standing between
    them.  Each ``if`` has no ``else`` and ends in ``return``; the code after the
    tests is the last arm.  A row naming a ``helper`` hands it the name there, once,
    as the first argument of a call of it by its bare name: the helper's chain of
    tests of its first parameter, read alike, maps on, and the code after it is the
    last arm.  Python's arms give no value the gate compares, so the last arm reads
    the awaited words the tests do not name, and must read one word or none.
    """

    module: Path
    function: PySymbol
    key: ReplyWord
    helper: PySymbol | None = None


type _PySet = _PyField | _PyEnum | _PyBoundKinds | _PyWordCall | _PyMappedWordCall

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
        "dbc/messages/signals/byteOrder": _PyWordCall(
            PYTHON_DBC_NORMALIZE, PySymbol("normalize_signal"), ReplyWord("byteOrder")
        ),
        "dbc/messages/signals/presence": _PyMappedWordCall(
            PYTHON_DBC_NORMALIZE, PySymbol("_check_presence"), ReplyWord("presence")
        ),
        "dbc/messages/signals/multiplexor": AnyNonEmpty(),
        "dbc/comments/target/kind": _PyMappedWordCall(
            PYTHON_DBC_NORMALIZE, PySymbol("_normalize_comment_target"), ReplyWord("kind")
        ),
        "dbc/attributes/kind": _PyMappedWordCall(
            PYTHON_DBC_NORMALIZE, PySymbol("_normalize_attribute"), ReplyWord("kind")
        ),
        "dbc/attributes/scope <definition>": _PyWordCall(
            PYTHON_DBC_NORMALIZE, PySymbol("_normalize_attribute"), ReplyWord("scope")
        ),
        "dbc/attributes/attrType/kind": _PyMappedWordCall(
            PYTHON_DBC_NORMALIZE, PySymbol("_normalize_attr_type"), ReplyWord("kind")
        ),
        "dbc/attributes/value/kind": _PyMappedWordCall(
            PYTHON_DBC_NORMALIZE, PySymbol("_normalize_attr_value"), ReplyWord("kind")
        ),
        "dbc/attributes/target/kind": _PyMappedWordCall(
            PYTHON_DBC_NORMALIZE,
            PySymbol("_normalize_attr_target"),
            ReplyWord("kind"),
            PySymbol("_normalize_attr_target_at_id"),
        ),
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
class MappingNames:
    """How a refusal names a mapping, the call whose words it maps, and the mapping's last arm."""

    mapping: Prose
    call: Prose
    last_arm: Prose


def mapped_last(
    awaited: frozenset[ReplyWord],
    named: frozenset[ReplyWord],
    shared: frozenset[ReplyWord],
    names: MappingNames,
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return the words a call awaits and the one word its mapping's last arm reads, or them alone.

    Each word the mapping's other arms name is one the call awaits; the last arm
    reads the awaited words they do not name and ``shared``, the words of the
    arms giving its value, and must read one word or none.
    """
    if not named <= awaited:
        outside = ", ".join(repr(word) for word in sorted(named - awaited))
        return Prose(f"{names.mapping} names {outside}, which no {names.call} awaits")
    match sorted(awaited - named | shared):
        case []:
            return awaited
        case [last]:
            return Arms(awaited, last)
        case several:
            return Prose(f"{names.last_arm} reads {', '.join(map(repr, several))} alike")


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


def _unshaped(place: ReplyPlace, form: _OneOf | AnyNonEmpty) -> list[Prose]:
    """Return a refusal for each word of a ``replyText`` row that is not identifier-shaped."""
    words = form.words if isinstance(form, _OneOf) else frozenset[ReplyWord]()
    return [
        Prose(f"replyText row {place}: '{word}' does not match {WORD_SHAPE}, a reply word's shape")
        for word in sorted(words)
        if re.fullmatch(WORD_SHAPE, word) is None
    ]


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
            unread.extend(_unshaped(place, form))
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


def _enum_words(spec: _PyEnum, bound: dict[PySymbol, ast.stmt]) -> frozenset[ReplyWord] | Prose:
    """Return the values of a ``StrEnum``'s members, each a string constant."""
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.name}"
    node = bound.get(spec.name)
    if node is None:
        return Prose(f"{where} is not defined")
    if not isinstance(node, ast.ClassDef):
        return Prose(f"{where} is not a class")
    words: set[ReplyWord] = set()
    for item in node.body:
        if isinstance(item, ast.Assign):
            member, value = item.targets[0], item.value
        elif isinstance(item, ast.AnnAssign) and item.value is not None:
            member, value = item.target, item.value
        else:
            continue
        if not (isinstance(value, ast.Constant) and isinstance(value.value, str)):
            return Prose(f"{where}.{ast.unparse(member)} is not a string constant")
        words.add(ReplyWord(value.value))
    return frozenset(words)


@dataclass(frozen=True)
class _PyCall:
    """A ``field_word`` call at a key, and its words."""

    node: ast.Call
    words: frozenset[ReplyWord]


def _literal(arg: ast.expr) -> ReplyWord | None:
    """Return the text of a string literal, or None for any other expression."""
    match arg:
        case ast.Constant(value=str() as text):
            return ReplyWord(text)
        case _:
            return None


def _word_calls(function: ast.FunctionDef, key: ReplyWord) -> list[_PyCall] | Prose:
    """Return each of a function's ``field_word`` calls at ``key``."""
    at_key: list[_PyCall] = []
    for node in ast.walk(function):
        match node:
            case ast.Call(func=ast.Name(id="field_word"), args=args, keywords=keywords):
                literals = [_literal(arg) for arg in args[2:]]
            case _:
                continue
        if literals[1:] == [] or literals[0] is None or keywords:
            return Prose(f"{ast.unparse(node)} names no string literal key or no word")
        if literals[0] == key:
            if None in literals[1:]:
                return Prose(f"{ast.unparse(node)} awaits a word that is not a string literal")
            words = frozenset(word for word in literals[1:] if word is not None)
            at_key.append(_PyCall(node, words))
    return at_key or Prose(f"no field_word call at {key!r}")


def _call_words(function: ast.FunctionDef, key: ReplyWord) -> frozenset[ReplyWord] | Prose:
    """Return the words a function's ``field_word`` calls at ``key`` await."""
    match _word_calls(function, key):
        case [*calls]:
            return frozenset(word for call in calls for word in call.words)
        case refused:
            return refused


def _test_of(function: ast.FunctionDef, call: ast.Call) -> tuple[ast.If, ast.Compare] | None:
    """Return the ``if`` of a function's body whose whole test compares ``call``, and the test."""
    for statement in function.body:
        match statement:
            case ast.If(test=ast.Compare(left=left) as compare) if left is call:
                return statement, compare
            case _:
                pass
    return None


def _bound_name(function: ast.FunctionDef, call: ast.Call) -> PySymbol | None:
    """Return the name a statement of a function's body assigns ``call`` to alone, or None."""
    for statement in function.body:
        match statement:
            case ast.Assign(targets=[ast.Name(id=name)], value=value) if value is call:
                return PySymbol(name)
            case _:
                pass
    return None


# A test of a word: its ``if`` and the comparison that is its whole test.
type _PyTest = tuple[ast.If, ast.Compare]


def _tests_of(function: ast.FunctionDef, name: PySymbol) -> list[_PyTest]:
    """Return the chain of ``if``s of a function's body from the first testing ``name``.

    An assignment between two of them ends no arm, so the chain goes on past it.
    """
    chain: list[_PyTest] = []
    for statement in function.body:
        match statement:
            case ast.If(test=ast.Compare(left=ast.Name(id=tested)) as compare) if tested == name:
                chain.append((statement, compare))
            case ast.Assign():
                pass
            case _ if chain:
                break
            case _:
                pass
    return chain


def _named_by(tests: list[_PyTest], test_name: Prose) -> frozenset[ReplyWord] | Prose:
    """Return the literals a mapping's tests compare its word to, each arm ending in return."""
    named: set[ReplyWord] = set()
    for test, compare in tests:
        match compare.ops, compare.comparators:
            case [ast.Eq()], [ast.Constant(value=str() as word)]:
                named.add(ReplyWord(word))
            case _:
                return Prose(f"{test_name} is not == to one literal")
        match test:
            case ast.If(body=[*_, ast.Return()], orelse=[]):
                pass
            case _:
                return Prose(f"{test_name} has an else or an arm not ending in return")
    return frozenset(named)


# The tests mapping a word, how a refusal names them, and how it names one of them.
type _PyMapping = tuple[list[_PyTest], Prose, Prose]


def _hands(node: ast.AST, name: PySymbol, helper: PySymbol) -> bool:
    """Say whether a node is a call of ``helper`` by its bare name, ``name`` its first argument."""
    match node:
        case ast.Call(func=ast.Name(id=callee), args=[ast.Name(id=first), *_]):
            return callee == helper and first == name
        case _:
            return False


def _unmapped_use(
    function: ast.FunctionDef, name: PySymbol, tests: list[_PyTest], helper: PySymbol | None
) -> Prose | None:
    """Return how a function uses the name its tests map other than to map it, or None.

    A ``helper`` takes the name once more, from the code after the tests.
    """
    after = function.body[function.body.index(tests[-1][0]) + 1 :]
    if helper is not None and not any(
        _hands(node, name, helper) for statement in after for node in ast.walk(statement)
    ):
        return Prose(f"hands {name} to {helper} nowhere after its tests, as its first argument")
    read = [node.id for node in ast.walk(function) if isinstance(node, ast.Name)]
    if read.count(name) != 1 + len(tests) + (0 if helper is None else 1):
        return Prose(f"uses {name} other than to map it")
    return None


def _mapping_tests(
    function: ast.FunctionDef, call: ast.Call, key: ReplyWord, helper: PySymbol | None
) -> _PyMapping | Prose:
    """Return the tests mapping the word ``call`` reads at ``key``.

    They are the one test comparing the call, or the chain of tests of the name
    the call is assigned to, a name used nowhere but in them and a ``helper``'s call.
    """
    tested = _test_of(function, call)
    if tested is not None:
        mapping = Prose(f"the test of the word at {key!r}")
        if helper is None:
            return [tested], mapping, mapping
        return Prose(f"hands the word at {key!r} to {helper} nowhere, testing it where it reads it")
    bound = _bound_name(function, call)
    if bound is None:
        return Prose(f"compares the word field_word reads at {key!r} in no if of its body")
    tests = _tests_of(function, bound)
    if not tests:
        return Prose(f"maps {bound} in no chain of tests of it")
    refused = _unmapped_use(function, bound, tests, helper)
    if refused is not None:
        return refused
    return tests, Prose(f"the tests of {bound}"), Prose(f"a test of {bound}")


def _helper_words(
    module: ast.Module, helper: PySymbol, names: MappingNames
) -> tuple[frozenset[ReplyWord], MappingNames] | Prose:
    """Return the words a helper's tests of its first parameter name, and ``names`` naming them.

    The tests are a chain read as a caller's are, the parameter used nowhere else.
    """
    function = _py_function(module, helper)
    if function is None:
        return Prose(f"{helper} is not defined")
    match function.args.posonlyargs + function.args.args:
        case [first, *_]:
            word = PySymbol(first.arg)
        case _:
            return Prose(f"{helper} takes no positional parameter")
    tests = _tests_of(function, word)
    read = [node.id for node in ast.walk(function) if isinstance(node, ast.Name)]
    if read.count(word) != len(tests):
        return Prose(f"{helper} uses {word} other than to map it")
    named = _named_by(tests, Prose(f"a test of {word} in {helper}"))
    if isinstance(named, str):
        return named
    tests_named = Prose(f"the tests of {word} in {helper}")
    mapping = Prose(f"{names.mapping} and {tests_named}")
    return named, replace(names, mapping=mapping, last_arm=Prose(f"the code after {tests_named}"))


def _mapped_call_words(
    module: ast.Module, function: ast.FunctionDef, key: ReplyWord, helper: PySymbol | None
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return the words a function's one call at ``key`` awaits and the word its last arm reads.

    A ``helper`` handed the word adds the words its tests name to the function's own.
    """
    match _word_calls(function, key):
        case [call]:
            found = _mapping_tests(function, call.node, key, helper)
        case [*calls]:
            return Prose(f"reads {key!r} with field_word {len(calls)} times, not once")
        case refused:
            return refused
    if isinstance(found, str):
        return found
    tests, mapping, test_name = found
    named = _named_by(tests, test_name)
    if isinstance(named, str):
        return named
    names = MappingNames(
        mapping, Prose(f"field_word call at {key!r}"), Prose(f"the code after {mapping}")
    )
    if helper is not None:
        handed = _helper_words(module, helper, names)
        if isinstance(handed, str):
            return handed
        helper_named, names = handed
        named |= helper_named
    return mapped_last(call.words, named, frozenset(), names)


def _py_source(path: Path) -> PyText:
    """Return the text of a Python module."""
    return PyText(path.read_text(encoding="utf-8"))


def _py_function(module: ast.Module, name: PySymbol) -> ast.FunctionDef | None:
    """Return the function a module defines at its top level as ``name``, or None."""
    for node in module.body:
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
    return None


def _python_words(
    spec: _PySet, py_codes: frozenset[ReplyWord]
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return a Python reader set's words and last arm, or why the gate cannot read them."""
    if isinstance(spec, _PyBoundKinds):
        return py_codes
    if not spec.module.is_file():
        return Prose(f"{spec.module.relative_to(REPO_ROOT)} not found")
    module = ast.parse(_py_source(spec.module))
    if isinstance(spec, _PyWordCall | _PyMappedWordCall):
        where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.function}"
        function = _py_function(module, spec.function)
        if function is None:
            return Prose(f"{where} is not defined")
        if isinstance(spec, _PyMappedWordCall):
            found = _mapped_call_words(module, function, spec.key, spec.helper)
        else:
            found = _call_words(function, spec.key)
        return Prose(f"{where}: {found}") if isinstance(found, str) else found
    bound = _top_level(module)
    if isinstance(spec, _PyField):
        return _field_words(spec, bound)
    return _enum_words(spec, bound)


# The greatest Unicode code point, and the surrogates, which name no character.
_MAX_CODE_POINT = 0x10FFFF
_SURROGATES = range(0xD800, 0xE000)


def scalar(code: CodePoint) -> LiteralText | None:
    """Return the character a Unicode escape names, None when the code is no scalar value."""
    return LiteralText(chr(code)) if code <= _MAX_CODE_POINT and code not in _SURROGATES else None


def read_text(chars: Iterable[LiteralText | None]) -> LiteralText | None:
    """Return the text a literal's characters and escapes read as, None when one reads as none."""
    read: list[LiteralText] = []
    for char in chars:
        if char is None:
            return None
        read.append(char)
    return LiteralText("".join(read))


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
