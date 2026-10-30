# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags arm of ``tools/check_limits_parity.py``.

The reply proof in ``src/Aletheia/Protocol/ReplyRange.agda`` lists, in
``replyText``, the words the kernel writes at each string place of a reply and,
in ``replyNonEmpty``, the arrays it writes with at least one element.  It leaves
a place no row names free, so this module holds each row a reader relies on: it
reads both tables, reads the set each Python reader takes at the place from its
type, and reports a row one side drops and a word one side holds alone.

A clause of either table, or a reader's type, that the module cannot read is
reported rather than passed over, every one of them in one run; the two
catch-all clauses, which leave every other place free, and the tables' type
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
    from collections.abc import Iterator

REPO_ROOT = Path(__file__).resolve().parent.parent
AGDA_REPLY_RANGE = REPO_ROOT / "src" / "Aletheia" / "Protocol" / "ReplyRange.agda"
PYTHON_TYPES = REPO_ROOT / "python" / "aletheia" / "types.py"
PYTHON_DBC_TYPES = REPO_ROOT / "python" / "aletheia" / "_dbc_types.py"
PYTHON_ISSUE_CODES = REPO_ROOT / "python" / "aletheia" / "codes" / "_issue.py"

# A reply place: the keys from the reply's root joined by "/", then, when the
# row depends on it, the `kind` or `type` its object carries in angle brackets.
ReplyPlace = NewType("ReplyPlace", str)
# A string the kernel writes at a reply place.
ReplyWord = NewType("ReplyWord", str)
# A top-level name in a Python module: an alias, a class or a field.
PySymbol = NewType("PySymbol", str)
# Agda source: a module, a clause of it or a fragment of a clause.
AgdaText = NewType("AgdaText", str)


@dataclass(frozen=True)
class _OneOf:
    """A place that holds one of a fixed set of words."""

    words: frozenset[ReplyWord]


@dataclass(frozen=True)
class _AnyNonEmpty:
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
PYTHON_REPLY_TEXT: dict[ReplyPlace, _PySet | _AnyNonEmpty] = {
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
        "dbc/messages/signals/multiplexor": _AnyNonEmpty(),
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

# Every row of `replyNonEmpty`: the arrays a reader takes as holding at least
# one element.
REPLY_NON_EMPTY: frozenset[ReplyPlace] = frozenset(
    {
        ReplyPlace("results <property_batch>"),
        ReplyPlace("dbc/messages/signals/multiplex_values"),
    }
)


@dataclass(frozen=True)
class ReplyTables:
    """The reply proof's two tables and the Python reader's set at each place."""

    agda_text: dict[ReplyPlace, _OneOf | _AnyNonEmpty]
    agda_non_empty: frozenset[ReplyPlace]
    python_text: dict[ReplyPlace, frozenset[ReplyWord] | _AnyNonEmpty]


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


def _text_form(rhs: AgdaText, named: dict[AgdaText, AgdaText]) -> _OneOf | _AnyNonEmpty | None:
    """Return the form a `replyText` row's right-hand side names, or None when none reads it."""
    if rhs == "just anyNonEmpty":
        return _AnyNonEmpty()
    if (one_of := _ONE_OF_NAMED.match(rhs)) is not None:
        body = named.get(AgdaText(one_of.group("name")))
        words = None if body is None else _list_words(body)
    elif (one_of := _ONE_OF_LITERAL.match(rhs)) is not None:
        words = _list_words(AgdaText(one_of.group("body")))
    else:
        return None
    return None if words is None else _OneOf(frozenset(words))


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
) -> tuple[dict[ReplyPlace, _OneOf | _AnyNonEmpty], frozenset[ReplyPlace], list[Prose]]:
    """Return the `replyText` rows, the `replyNonEmpty` places and every clause no form reads."""
    clauses = list(_clauses(_without_block_comments(text)))
    named = {
        AgdaText(m.group("name")): AgdaText(m.group("body"))
        for clause in clauses
        if (m := _DEFINITION.match(clause)) is not None
    }
    text_rows: dict[ReplyPlace, _OneOf | _AnyNonEmpty] = {}
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


def read_reply_tables(text: AgdaText, py_codes: frozenset[ReplyWord]) -> ReplyTables | list[Prose]:
    """Return both tables of ``text`` and the Python sets, or every clause or set none reads."""
    agda_text, agda_non_empty, unread = _parse_agda_reply_places(text)
    if not agda_text or not agda_non_empty:
        unread.append(Prose("no replyText or replyNonEmpty rows parsed"))
    python_text: dict[ReplyPlace, frozenset[ReplyWord] | _AnyNonEmpty] = {}
    for place, spec in PYTHON_REPLY_TEXT.items():
        words = spec if isinstance(spec, _AnyNonEmpty) else _python_words(spec, py_codes)
        if isinstance(words, str):
            unread.append(Prose(f"reply place {place}: {words}"))
        else:
            python_text[place] = words
    return unread or ReplyTables(agda_text, agda_non_empty, python_text)


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


def check_reply_places(tables: ReplyTables, agda_codes: frozenset[ReplyWord]) -> list[Prose]:
    """Return the divergences between the reply proof's tables and the Python reader's sets."""
    diffs: list[Prose] = []
    for place, words in tables.python_text.items():
        row = tables.agda_text.get(place)
        if row is None:
            diffs.append(
                Prose(
                    f"reply place {place}: replyText has no row, so the proof holds nothing there"
                )
            )
        elif isinstance(words, _AnyNonEmpty) or isinstance(row, _AnyNonEmpty):
            if not (isinstance(words, _AnyNonEmpty) and isinstance(row, _AnyNonEmpty)):
                diffs.append(
                    Prose(
                        f"reply place {place}: one side reads any non-empty text, "
                        + "the other a word set"
                    )
                )
        else:
            diffs.extend(
                _one_side(
                    place, (Prose("replyText"), row.words), (Prose("the Python reader"), words)
                )
            )
    diffs.extend(
        Prose(f"reply place {place}: replyText has a row PYTHON_REPLY_TEXT does not name")
        for place in sorted(tables.agda_text.keys() - tables.python_text.keys())
    )
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
