# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Go reader of the reply-tags arm, ``tools/_reply_places.py``.

It reads the set the Go binding's reply readers take at each string place of
``replyText`` from their own code, through tree-sitter-go's syntax tree of each
file of the package: the literals a reader's ``fieldWord`` calls await, alone
or with the ``switch`` or the chain of tests mapping the word one such call
binds, the one ``var`` block of a struct type's values, or the ``BoundKind*``
codes.  A mapping's last arm, which
reads every awaited word its other arms do not name, holds its word to the
row's last word.  A line of the package that could give a value of such a type
its word outside that block is reported with each set the module cannot read,
as is a line of a reader file comparing a word, a string literal whose text, as
the compiler reads its escapes, is identifier-shaped, outside the lines these
rows read and the switch and select statements of the functions ``GO_UNTAGGED``
names, which compare a word at a place ``replyText`` has no row for and are a
divergence once it has one.  A line of the package the grammar cannot parse is
reported too, so that no file is read past in silence.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from tools._reply_places import (
    REPO_ROOT,
    AnyNonEmpty,
    Arms,
    GoLine,
    GoSymbol,
    GoText,
    MappingNames,
    ReaderSets,
    ReplyPlace,
    ReplyWord,
    mapped_last,
    read_sets,
)
from tools._reply_places_go_tree import (
    GO_COMMENTS,
    GO_LANGUAGE,
    GO_LITERALS,
    GO_NAMES,
    go_function,
    go_function_lines,
    go_line,
    go_lines,
    holds_no_word,
    is_name,
    is_word,
    mentions,
    plain,
    plains,
    unwrapped,
)
from tools._reply_places_tree import (
    NodeKind,
    NodeText,
    SourceOffset,
    SourceTree,
    TreeLine,
    broken_lines,
    child_of,
    edge,
    first_line,
    node_lines,
    parse_source,
    walk,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterator
    from pathlib import Path

    from tree_sitter import Node

    from tools._reply_places import BindingReader

GO_PACKAGE = REPO_ROOT / "go" / "aletheia"
GO_DBC = GO_PACKAGE / "json_dbc.go"
GO_RESPONSE = GO_PACKAGE / "json_response.go"
GO_REPLY_SHAPE = GO_PACKAGE / "reply_shape.go"
# The files of the package that read a reply's words.
GO_READER_FILES = (GO_RESPONSE, GO_DBC, GO_REPLY_SHAPE)


@dataclass(frozen=True)
class _GoWordCall:
    """The literals a function's ``fieldWord`` calls at a key await."""

    module: Path
    function: GoSymbol
    key: ReplyWord


@dataclass(frozen=True)
class _GoMappedWordCall:
    """The literals a function's one ``fieldWord`` call at a key awaits, and the code mapping them.

    The call binds the word to a variable the function compares only in one
    ``switch`` on it, whose last clause is ``default``, or in a chain of
    ``if <word> == "<literal>"`` tests, the code after them its last arm.  Each
    arm gives one value, an exported name or a composite literal of an exported
    type, which the type stands for: one statement assigns it, or the arm's last
    returns it with a nil error and every other return of it an error, every arm
    assigning one variable or every arm returning.  The last arm reads the
    awaited words no other arm names and the words of the arms giving its value,
    and must read one word or none.
    """

    module: Path
    function: GoSymbol
    key: ReplyWord


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


type _GoSet = _GoWordCall | _GoMappedWordCall | _GoValues | _GoBoundKinds

# Every row of `replyText`, with the set the Go reader takes at its place, read
# from the reader's own code, under the rules PYTHON_REPLY_TEXT is held to; the
# word a mapping's last arm reads is the row's last word.
GO_REPLY_TEXT: dict[ReplyPlace, _GoSet | AnyNonEmpty] = {
    ReplyPlace(place): spec
    for place, spec in {
        "status": _GoValues(
            GO_RESPONSE, GoSymbol("replyStatus"), GoSymbol("word"), GoSymbol("fieldStatus")
        ),
        "type": _GoWordCall(GO_RESPONSE, GoSymbol("parseFrameResponse"), ReplyWord("type")),
        "results/type": _GoWordCall(GO_RESPONSE, GoSymbol("readVerdict"), ReplyWord("type")),
        "results/status <property>": _GoMappedWordCall(
            GO_RESPONSE, GoSymbol("readVerdict"), ReplyWord("status")
        ),
        "warnings/kind": _GoWordCall(
            GO_RESPONSE, GoSymbol("parseStreamWarning"), ReplyWord("kind")
        ),
        "issues/severity": _GoMappedWordCall(
            GO_RESPONSE, GoSymbol("readSeverity"), ReplyWord("severity")
        ),
        "warnings/severity": _GoMappedWordCall(
            GO_RESPONSE, GoSymbol("readSeverity"), ReplyWord("severity")
        ),
        "bound_kind": _GoBoundKinds(),
        "dbc/messages/signals/byteOrder": _GoMappedWordCall(
            GO_DBC, GoSymbol("readByteOrder"), ReplyWord("byteOrder")
        ),
        "dbc/messages/signals/presence": _GoMappedWordCall(
            GO_DBC, GoSymbol("parseSignalPresence"), ReplyWord("presence")
        ),
        "dbc/messages/signals/multiplexor": AnyNonEmpty(),
        "dbc/comments/target/kind": _GoMappedWordCall(
            GO_DBC, GoSymbol("parseCommentTarget"), ReplyWord("kind")
        ),
        "dbc/attributes/kind": _GoMappedWordCall(
            GO_DBC, GoSymbol("parseAttribute"), ReplyWord("kind")
        ),
        "dbc/attributes/scope <definition>": _GoMappedWordCall(
            GO_DBC, GoSymbol("readAttrScope"), ReplyWord("scope")
        ),
        "dbc/attributes/attrType/kind": _GoMappedWordCall(
            GO_DBC, GoSymbol("parseAttrType"), ReplyWord("kind")
        ),
        "dbc/attributes/value/kind": _GoMappedWordCall(
            GO_DBC, GoSymbol("parseAttrValue"), ReplyWord("kind")
        ),
        "dbc/attributes/target/kind": _GoMappedWordCall(
            GO_DBC, GoSymbol("parseAttrTarget"), ReplyWord("kind")
        ),
    }.items()
}

# The functions of a reader file that compare a word with literals at a place
# `replyText` has no row for, whose switch and select statements the gate reads
# past.  The package reads an issue's code and an error's code as a member of a
# set keyed by constants, comparing no literal, so it names none.
GO_UNTAGGED: dict[ReplyPlace, tuple[Path, GoSymbol]] = {}

# The kinds of node the readers below read.
_CALL = NodeKind("call_expression")
_COMPOSITE = NodeKind("composite_literal")
_STRUCT = NodeKind("struct_type")
_CASE = NodeKind("expression_case")
_DEFAULT = NodeKind("default_case")
_CLAUSES = frozenset(
    NodeKind(kind)
    for kind in ("expression_case", "type_case", "communication_case", "default_case")
)
# The fields of a clause's head: what an expression case or a select case compares.
_CASE_HEADS = ("value", "communication")
_CASE_HOLDERS = frozenset(
    NodeKind(kind)
    for kind in ("expression_switch_statement", "type_switch_statement", "select_statement")
)
_COMPARISONS = frozenset(NodeKind(op) for op in ("==", "!=", "<", "<=", ">", ">="))
# The call whose awaited words a row reads, and what an arm returning gives its value to.
_WORD_READER = GoSymbol("fieldWord")
_RETURN = GoSymbol("return")
# The calls comparing their first argument with the rest as a whole text, by
# package: a `strings` call testing, cutting or trimming a text, or
# `slices.Contains`.  Trim, TrimLeft and TrimRight take a cutset, a set of
# characters, so they compare no word.
_COMPARING_CALLS: dict[NodeText, frozenset[NodeText]] = {
    NodeText("strings"): frozenset(
        map(
            NodeText,
            [
                "Compare",
                "Contains",
                "Cut",
                "CutPrefix",
                "CutSuffix",
                "EqualFold",
                "HasPrefix",
                "HasSuffix",
                "Index",
                "TrimPrefix",
                "TrimSuffix",
            ],
        )
    ),
    NodeText("slices"): frozenset({NodeText("Contains")}),
}

# A line of a file of the Go package.
type _GoSite = tuple[Path, GoLine]


def _go_source(path: Path) -> GoText:
    """Return the source of a file of the Go package."""
    return GoText(path.read_text(encoding="utf-8"))


def _go_package() -> dict[Path, SourceTree]:
    """Return every non-test file of the Go package, parsed."""
    return {
        path: parse_source(GO_LANGUAGE, GO_COMMENTS, path, NodeText(_go_source(path)))
        for path in sorted(GO_PACKAGE.glob("*.go"))
        if not path.name.endswith("_test.go")
    }


def _clauses(holder: Node) -> list[Node]:
    """Return the ``case`` and ``default`` clauses of a switch or a select, in order."""
    return [child for child in holder.named_children if child.type in _CLAUSES]


def _header(tree: SourceTree, clause: Node) -> NodeText:
    """Return the line a clause opens on, as a refusal shows it."""
    return tree.line(first_line(clause))


def _case_words(tree: SourceTree, clause: Node) -> frozenset[ReplyWord] | None:
    """Return the words of a ``case`` of string literals written on its first line, or None."""
    values = clause.child_by_field_name("value")
    if clause.type != _CASE or values is None or node_lines(values)[-1] != first_line(clause):
        return None
    return plains(tree, tree.named(values))


@dataclass(frozen=True)
class _GoCall:
    """A ``fieldWord`` call at a key, and its words."""

    node: Node
    words: frozenset[ReplyWord]


def _word_calls(tree: SourceTree, function: Node, key: ReplyWord) -> list[_GoCall] | Prose:
    """Return each of a function's ``fieldWord`` calls at ``key``."""
    calls = [
        (node, node.child_by_field_name("arguments"))
        for node in walk(function)
        if node.type == _CALL and is_name(tree, node.child_by_field_name("function"), _WORD_READER)
    ]
    if any(part.type == "(" for _, args in calls for arg in tree.named(args) for part in walk(arg)):
        return Prose("a fieldWord call holds a call of its own")
    at_key: list[_GoCall] = []
    for call, arguments in calls:
        written = NodeText("")
        if arguments is not None:
            inside = (SourceOffset(arguments.start_byte + 1), SourceOffset(arguments.end_byte - 1))
            written = tree.code(*inside)
        args = tree.named(arguments)
        at = plain(tree, args[2]) if args[3:] else None
        if at is None:
            return Prose(f"fieldWord({written}) names no literal key or no word")
        if at != key:
            continue
        words = plains(tree, args[3:])
        if words is None:
            return Prose(f"fieldWord({written}) awaits a word that is not a literal")
        at_key.append(_GoCall(call, words))
    return at_key or Prose(f"no fieldWord call at {key!r}")


def _word_call_words(
    tree: SourceTree, function: Node, key: ReplyWord
) -> frozenset[ReplyWord] | Prose:
    """Return the words a function's ``fieldWord`` calls at ``key`` await."""
    match _word_calls(tree, function, key):
        case [*calls]:
            return frozenset(word for call in calls for word in call.words)
        case refused:
            return refused


@dataclass(frozen=True)
class _GoArm:
    """An arm of a mapping: the words it names, none for the last, what it assigns, and its value.

    ``giver`` is the variable the arm assigns its value to, or ``return``.
    """

    words: frozenset[ReplyWord]
    giver: GoSymbol
    value: GoSymbol


@dataclass(frozen=True)
class _GoArms:
    """A mapping's arms, its last arm last, how a refusal names it and that arm, and its lines.

    ``heads`` are the lines comparing the word: the ``switch``, or each test.
    """

    arms: list[_GoArm]
    mapping: Prose
    last_arm: Prose
    lines: frozenset[GoLine]
    heads: frozenset[GoLine]


@dataclass(frozen=True)
class _GoMapping:
    """What a mapped row reads: the words its call awaits, the mapping, and the lines of both."""

    awaited: frozenset[ReplyWord]
    arms: _GoArms
    lines: frozenset[GoLine]


@dataclass(frozen=True)
class _GoBody:
    """The statements of an arm, and its code as a refusal shows it."""

    statements: list[Node]
    code: NodeText


def _body(tree: SourceTree, holder: Node | None) -> _GoBody:
    """Return the statements of a clause or a block."""
    listed = child_of(holder, NodeKind("statement_list"))
    if listed is None:
        return _GoBody([], NodeText(""))
    return _GoBody(tree.named(listed), tree.code_of(listed))


def _value(tree: SourceTree, node: Node) -> GoSymbol | None:
    """Return a node's identifier or a composite literal's type, opening with an ASCII capital."""
    named, kind = node, "identifier"
    if node.type == _COMPOSITE:
        named, kind = node.child_by_field_name("type"), "type_identifier"
    if named is None or named.type != kind:
        return None
    initial = tree.text(named)[:1]
    return GoSymbol(tree.text(named)) if initial.isascii() and initial.isupper() else None


def _returned(tree: SourceTree, statement: Node) -> list[Node]:
    """Return the values a return statement returns."""
    return [value for listed in tree.named(statement) for value in tree.named(listed)]


def _return_errors(tree: SourceTree, statements: list[Node]) -> bool:
    """Say whether every return in ``statements`` returns an error, its last value no nil."""
    nodes = (node for each in statements for node in walk(each))
    returned = (_returned(tree, node) for node in nodes if node.type == "return_statement")
    return all(values and values[-1].type != "nil" for values in returned)


def _given(tree: SourceTree, statements: list[Node]) -> tuple[GoSymbol, GoSymbol] | None:
    """Return what an arm's statements give their one value to and the value, or None.

    One statement assigns the value to one variable, or the last returns it with
    a nil error, every return before it returning an error.
    """
    match statements:
        case [statement] if statement.type == "assignment_statement":
            operator = statement.child_by_field_name("operator")
            targets = tree.named(statement.child_by_field_name("left"))
            values = tree.named(statement.child_by_field_name("right"))
            value = _value(tree, values[0]) if len(values) == 1 else None
            if (
                operator is not None
                and operator.type == "="
                and [target.type for target in targets] == ["identifier"]
                and value is not None
            ):
                return GoSymbol(tree.text(targets[0])), value
        case [*before, last] if last.type == "return_statement" and _return_errors(tree, before):
            values = _returned(tree, last)
            value = _value(tree, values[0]) if values else None
            if [each.type for each in values[1:]] == ["nil"] and value is not None:
                return _RETURN, value
        case _:
            pass
    return None


def _arm(tree: SourceTree, words: frozenset[ReplyWord], body: _GoBody) -> _GoArm | Prose:
    """Return an arm whose code gives one value, or why it gives none."""
    given = _given(tree, body.statements)
    if given is None:
        return Prose(f"{body.code!r} gives no one value")
    return _GoArm(words, *given)


def _case_arm(tree: SourceTree, clause: Node) -> _GoArm | Prose:
    """Return a ``case`` clause of string literals as an arm, or why it is not one."""
    words = _case_words(tree, clause)
    if words is None:
        return Prose(f"{_header(tree, clause)!r} is not a case of string literals on one line")
    return _arm(tree, words, _body(tree, clause))


def _read_arms(read: list[_GoArm | Prose]) -> list[_GoArm] | Prose:
    """Return the arms read, or why the first the gate cannot read is not one."""
    arms = [arm for arm in read if isinstance(arm, _GoArm)]
    return arms if len(arms) == len(read) else next(arm for arm in read if isinstance(arm, str))


def _switch_arms(tree: SourceTree, switch: Node, word: GoSymbol) -> _GoArms | Prose:
    """Return the clauses of a switch on ``word`` as arms, its ``default`` last."""
    mapping = Prose(f"the switch on {word}")
    clauses = _clauses(switch)
    if not clauses or clauses[-1].type != _DEFAULT:
        return Prose(f"{mapping} does not end in default")
    arms = _read_arms(
        [
            *(_case_arm(tree, clause) for clause in clauses[:-1]),
            _arm(tree, frozenset(), _body(tree, clauses[-1])),
        ]
    )
    if isinstance(arms, str):
        return arms
    last_arm = Prose(f"the default of {mapping}")
    return _GoArms(arms, mapping, last_arm, go_lines(switch), frozenset({go_line(switch)}))


def _tested(tree: SourceTree, node: Node, word: GoSymbol) -> ReplyWord | None:
    """Return the literal an ``if <word> == "<literal>"`` test with no else compares, or None."""
    condition = node.child_by_field_name("condition")
    if (
        node.type != "if_statement"
        or node.child_by_field_name("initializer") is not None
        or node.child_by_field_name("alternative") is not None
        or condition is None
        or condition.type != "binary_expression"
    ):
        return None
    operator = condition.child_by_field_name("operator")
    right = condition.child_by_field_name("right")
    if operator is None or operator.type != "==" or right is None:
        return None
    if not is_name(tree, condition.child_by_field_name("left"), word):
        return None
    return plain(tree, right)


def _next_statement(tree: SourceTree, node: Node) -> Node | None:
    """Return the statement after a node in its list, or None."""
    sibling = node.next_named_sibling
    while sibling is not None and sibling.type in tree.comments:
        sibling = sibling.next_named_sibling
    return sibling


def _after_tests(tree: SourceTree, last: Node, function: Node) -> tuple[_GoBody, GoLine]:
    """Return the function's code after its last test, and the line its closing brace stands on.

    That code's statements are the ones after the test in the function's body;
    a test in a block of its own leaves the code with the block's closing brace
    in it, which is no statement giving a value.
    """
    body = function.child_by_field_name("body")
    closing = child_of(body, NodeKind("}"))
    end = SourceOffset(function.end_byte if closing is None else closing.start_byte)
    rest: list[Node] = []
    after = _next_statement(tree, last)
    while body is not None and last.parent is not None and last.parent.parent == body and after:
        rest.append(after)
        after = _next_statement(tree, after)
    code = _GoBody(rest, tree.code(SourceOffset(last.end_byte), end))
    return code, GoLine(node_lines(function).stop if closing is None else go_line(closing))


def _test_arms(tree: SourceTree, first: Node, word: GoSymbol, function: Node) -> _GoArms | Prose:
    """Return a chain of tests of ``word`` as arms, the function's code after them last."""
    mapping = Prose(f"the tests of {word}")
    read: list[_GoArm | Prose] = []
    heads: set[GoLine] = set()
    last, test = first, first
    while test is not None and (tested := _tested(tree, test, word)) is not None:
        consequence = _body(tree, test.child_by_field_name("consequence"))
        read.append(_arm(tree, frozenset({tested}), consequence))
        heads.add(go_line(test))
        last, test = test, _next_statement(tree, test)
    code, closing = _after_tests(tree, last, function)
    arms = _read_arms([*read, _arm(tree, frozenset(), code)])
    if isinstance(arms, str):
        return arms
    lines = frozenset(map(GoLine, range(go_line(first), closing)))
    return _GoArms(arms, mapping, Prose(f"the code after {mapping}"), lines, frozenset(heads))


def _mapping_arms(tree: SourceTree, function: Node, word: GoSymbol) -> _GoArms | Prose:
    """Return the arms of the first switch on ``word`` or chain of tests of it in a function."""
    for node in walk(function):
        if (
            node.type == "expression_switch_statement"
            and node.child_by_field_name("initializer") is None
            and is_name(tree, node.child_by_field_name("value"), word)
        ):
            return _switch_arms(tree, node, word)
        if _tested(tree, node, word) is not None:
            return _test_arms(tree, node, word, function)
    return Prose(f"maps {word} in no switch on it and no chain of tests of it")


def _binding(tree: SourceTree, call: Node) -> GoSymbol | None:
    """Return the variable a statement binds the first of a call's two results to, or None.

    The call opens the values ``word, err := ...``, ``word, err = ...`` or
    ``var word, err = ...`` binds.
    """
    values = call.parent
    binding = None if values is None else values.parent
    if values is None or binding is None or tree.named(values)[:1] != [call]:
        return None
    if binding.type in {"short_var_declaration", "assignment_statement"}:
        operator = binding.child_by_field_name("operator")
        if binding.child_by_field_name("right") != values or (
            operator is not None and operator.type != "="
        ):
            return None
        names = tree.named(binding.child_by_field_name("left"))
    elif binding.type == "var_spec" and binding.child_by_field_name("type") is None:
        names = binding.children_by_field_name("name")
    else:
        return None
    if len(names) < len(("word", "err")) or any(name.type != "identifier" for name in names[-2:]):
        return None
    return GoSymbol(tree.text(names[-2]))


def _bound_call(
    tree: SourceTree, function: Node, key: ReplyWord
) -> tuple[_GoCall, GoSymbol] | Prose:
    """Return a function's one ``fieldWord`` call at ``key`` and the variable binding its word."""
    match _word_calls(tree, function, key):
        case [call]:
            bound = _binding(tree, call.node)
        case [*calls]:
            return Prose(f"reads {key!r} with fieldWord {len(calls)} times, not once")
        case refused:
            return refused
    if bound is None or bound == "_":
        return Prose(f"binds the word fieldWord reads at {key!r} to no variable")
    return call, bound


def _go_mapping(spec: _GoMappedWordCall, tree: SourceTree, function: Node) -> _GoMapping | Prose:
    """Return what a mapped row reads of its function: its one call at its key and the mapping."""
    bound = _bound_call(tree, function, spec.key)
    if isinstance(bound, str):
        return bound
    call, word = bound
    arms = _mapping_arms(tree, function, word)
    if isinstance(arms, str):
        return arms
    if sum(is_name(tree, node, word) for node in walk(function)) != 1 + len(arms.heads):
        return Prose(f"uses {word} other than to map it")
    if len({arm.giver for arm in arms.arms}) != 1:
        return Prose(f"the arms of {arms.mapping} give their values in more than one way")
    return _GoMapping(call.words, arms, go_lines(call.node) | arms.lines)


def _mapped_words(
    spec: _GoMappedWordCall, tree: SourceTree, function: Node
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return the words a call at its key awaits and the word its mapping's last arm reads.

    The last arm reads, beside the awaited words no other arm names, the words of
    the arms giving the value it gives.
    """
    mapping = _go_mapping(spec, tree, function)
    if isinstance(mapping, str):
        return mapping
    *named, last = mapping.arms.arms
    shared = frozenset(word for arm in named if arm.value == last.value for word in arm.words)
    names = MappingNames(
        mapping.arms.mapping, Prose(f"fieldWord call at {spec.key!r}"), mapping.arms.last_arm
    )
    return mapped_last(
        mapping.awaited, frozenset(word for arm in named for word in arm.words), shared, names
    )


def _string_field(tree: SourceTree, struct: Node | None, field: GoSymbol) -> Node | None:
    """Return a struct type's one field when it is ``field`` of type ``string``, or None."""
    if struct is None or struct.type != _STRUCT:
        return None
    match tree.named(child_of(struct, NodeKind("field_declaration_list"))):
        case [declared] if is_name(
            tree, declared.child_by_field_name("type"), GoSymbol("string")
        ) and [tree.text(name) for name in declared.children_by_field_name("name")] == [field]:
            return declared
        case _:
            return None


def _value_word(tree: SourceTree, spec: _GoValues, value: Node) -> ReplyWord | None:
    """Return the word of a ``var`` specification of one name and one value of a word, or None."""
    match tree.named(value.child_by_field_name("value")):
        case [built] if (
            len(value.children_by_field_name("name")) == 1
            and value.child_by_field_name("type") is None
            and built.type == _COMPOSITE
            and is_name(tree, built.child_by_field_name("type"), spec.name)
        ):
            elements = tree.named(built.child_by_field_name("body"))
        case _:
            return None
    match elements:
        case [element] if element.type == "literal_element" and len(tree.named(element)) == 1:
            return plain(tree, tree.named(element)[0])
        case _:
            return None


@dataclass(frozen=True)
class _GoBreach:
    """A kind of node that could give a value its word outside its block, and the lines exempt.

    ``found`` says whether a node of one of ``kinds`` is one, reported at its first line.
    """

    kinds: frozenset[NodeKind]
    found: Callable[[SourceTree, Node], bool]
    what: Prose
    exempt: frozenset[_GoSite]


def _converts(tree: SourceTree, node: Node, name: GoSymbol) -> bool:
    """Say whether a call converts to the type ``name``, or a conversion to a type ending in it."""
    if node.type == _CALL:
        return is_name(tree, unwrapped(tree, node.child_by_field_name("function")), name)
    converted = node.child_by_field_name("type")
    return converted is not None and is_name(tree, edge(converted, GO_NAMES, last=True), name)


def _value_breaches(
    spec: _GoValues, block: frozenset[_GoSite], declared: _GoSite, reader: frozenset[_GoSite]
) -> tuple[_GoBreach, ...]:
    """Return the nodes that could give a value of the type a word outside its block."""
    name, field = spec.name, spec.field
    return (
        _GoBreach(
            frozenset({_COMPOSITE}),
            lambda tree, node: mentions(tree, node.child_by_field_name("type"), name),
            Prose(f"builds a {name} outside its block"),
            block,
        ),
        _GoBreach(
            frozenset({_CALL, NodeKind("type_conversion_expression")}),
            lambda tree, node: _converts(tree, node, name),
            Prose(f"converts a value to {name}"),
            frozenset(),
        ),
        _GoBreach(
            frozenset({NodeKind("type_alias")}),
            lambda tree, node: is_name(tree, node.child_by_field_name("type"), name),
            Prose(f"aliases {name}"),
            frozenset(),
        ),
        _GoBreach(
            frozenset({NodeKind("type_parameter_declaration")}),
            lambda tree, node: mentions(tree, node.child_by_field_name("type"), name),
            Prose(f"constrains a type parameter to {name}"),
            frozenset(),
        ),
        _GoBreach(
            frozenset({_STRUCT}),
            lambda tree, node: _string_field(tree, node, field) is not None,
            Prose(f"declares an unnamed struct a {name} is assigned from"),
            frozenset({declared}),
        ),
        _GoBreach(
            frozenset({NodeKind("selector_expression")}),
            lambda tree, node: is_name(tree, node.child_by_field_name("field"), field),
            Prose(f"reaches the {field} of a value outside {spec.reader}"),
            reader,
        ),
    )


def _values_built_elsewhere(
    spec: _GoValues, package: dict[Path, SourceTree], block: frozenset[_GoSite], declared: _GoSite
) -> Iterator[Prose]:
    """Yield each line of the package that could give a value of the type a word elsewhere."""
    reader = frozenset(
        (path, line)
        for path, tree in package.items()
        for line in go_function_lines(tree, spec.reader)
    )
    breaches = _value_breaches(spec, block, declared, reader)
    for path, tree in package.items():
        hits = {
            (go_line(node), index)
            for index, breach in enumerate(breaches)
            for kind in breach.kinds
            for node in tree.nodes(kind)
            if breach.found(tree, node) and (path, go_line(node)) not in breach.exempt
        }
        for line, index in sorted(hits):
            shown = tree.line(TreeLine(line))
            yield Prose(f"{path.relative_to(REPO_ROOT)}:{line}: {shown!r} {breaches[index].what}")


def _value_words(spec: _GoValues, package: dict[Path, SourceTree]) -> frozenset[ReplyWord] | Prose:
    """Return the words of a type's one block of values, or each line that hides them."""
    where = spec.module.relative_to(REPO_ROOT)
    tree = package.get(spec.module)
    declaration = f"type {spec.name} struct{{ {spec.field} string }}"
    at = [
        node
        for node in ([] if tree is None else tree.nodes(NodeKind("type_spec")))
        if tree is not None
        and is_name(tree, node.child_by_field_name("name"), spec.name)
        and (declared := _string_field(tree, node.child_by_field_name("type"), spec.field))
        and declared.child_by_field_name("tag") is None
    ]
    if tree is None or len(at) != 1:
        return Prose(f"{where}:{spec.name} is not declared once as {declaration!r}")
    blocks = [b for b in tree.nodes(NodeKind("var_spec_list")) if mentions(tree, b, spec.name)]
    if len(blocks) != 1:
        return Prose(f"{where}:{spec.name}: {len(blocks)} var blocks declare its values, not one")
    words: set[ReplyWord] = set()
    unread: list[Prose] = []
    values = [value for value in tree.named(blocks[0]) if value.type == "var_spec"]
    for value in values:
        word = _value_word(tree, spec, value)
        if word is not None:
            words.add(word)
            continue
        unread.append(
            Prose(
                f"{where}:{go_line(value)}: {tree.code_of(value)!r} "
                + f"is not one name and one {spec.name} of a word"
            )
        )
    block = frozenset((spec.module, line) for value in values for line in go_lines(value))
    unread.extend(_values_built_elsewhere(spec, package, block, (spec.module, go_line(at[0]))))
    return Prose("; ".join(unread)) if unread else frozenset(words)


def _go_words(
    spec: _GoSet, go_codes: frozenset[ReplyWord], package: dict[Path, SourceTree]
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return a Go reader set's words and last arm, or why the gate cannot read them."""
    if isinstance(spec, _GoBoundKinds):
        return go_codes
    if isinstance(spec, _GoValues):
        return _value_words(spec, package)
    where = f"{spec.module.relative_to(REPO_ROOT)}:{spec.function}"
    tree = package.get(spec.module)
    function = go_function(tree, spec.function)
    if tree is None or function is None:
        return Prose(f"{where} is not defined")
    if isinstance(spec, _GoMappedWordCall):
        found = _mapped_words(spec, tree, function)
    else:
        found = _word_call_words(tree, function, spec.key)
    return Prose(f"{where}: {found}") if isinstance(found, str) else found


def _mapped_sites(package: dict[Path, SourceTree]) -> frozenset[_GoSite]:
    """Return the lines of the package each mapped row of ``GO_REPLY_TEXT`` reads.

    They are its call and its mapping; a row the gate cannot read gives none, its
    place reporting why.
    """
    sites: set[_GoSite] = set()
    for spec in GO_REPLY_TEXT.values():
        if not isinstance(spec, _GoMappedWordCall):
            continue
        tree = package.get(spec.module)
        function = go_function(tree, spec.function)
        mapping = None if tree is None or function is None else _go_mapping(spec, tree, function)
        if isinstance(mapping, _GoMapping):
            sites |= {(spec.module, line) for line in mapping.lines}
    return frozenset(sites)


def go_mapped_sites() -> frozenset[_GoSite]:
    """Return the lines of the Go package, as it stands, each mapped row reads."""
    return _mapped_sites(_go_package())


def _compares_word(tree: SourceTree, call: Node) -> bool:
    """Say whether a comparing call compares with anything but literals holding no word."""
    function = call.child_by_field_name("function")
    if function is None or function.type != "selector_expression":
        return False
    package = function.child_by_field_name("operand")
    name = function.child_by_field_name("field")
    if package is None or name is None or package.type != "identifier":
        return False
    if tree.text(name) not in _COMPARING_CALLS.get(tree.text(package), frozenset()):
        return False
    arguments = tree.named(call.child_by_field_name("arguments"))
    return not all(holds_no_word(tree, argument) for argument in arguments[1:])


def _go_comparisons(tree: SourceTree) -> list[GoLine]:
    """Return, in order, each line of a file holding a comparison that could read a word.

    A word beside an ``==``, ``!=``, ``<``, ``<=``, ``>`` or ``>=`` is one, at
    the line of the operator before it or of the word before the operator; so
    is a word in the head of a ``case`` clause, at its line, and a word before
    the colon of a composite literal's key; and a comparing call, at its first
    line, unless every argument after its first is a literal holding no word.
    """
    lines: set[GoLine] = set()
    for node in tree.nodes(NodeKind("binary_expression")):
        operator = node.child_by_field_name("operator")
        left, right = node.child_by_field_name("left"), node.child_by_field_name("right")
        if operator is None or operator.type not in _COMPARISONS:
            continue
        if left is not None and is_word(tree, word := edge(left, GO_LITERALS, last=True)):
            lines.add(go_line(word))
        if right is not None and is_word(tree, edge(right, GO_LITERALS, last=False)):
            lines.add(go_line(operator))
    for clause in (node for kind in _CLAUSES for node in tree.nodes(kind)):
        heads = (head for field in _CASE_HEADS for head in clause.children_by_field_name(field))
        lines |= {go_line(node) for head in heads for node in walk(head) if is_word(tree, node)}
    for element in tree.nodes(NodeKind("keyed_element")):
        key = element.child_by_field_name("key")
        if key is not None and is_word(tree, word := edge(key, GO_LITERALS, last=True)):
            lines.add(go_line(word))
    lines |= {go_line(call) for call in tree.nodes(_CALL) if _compares_word(tree, call)}
    return sorted(lines)


def _go_unparsed(package: dict[Path, SourceTree]) -> Iterator[Prose]:
    """Yield each line of the package holding code the grammar cannot parse."""
    for path, tree in package.items():
        for line in broken_lines(tree):
            yield Prose(
                f"{path.relative_to(REPO_ROOT)}:{line}: {tree.line(line)!r} "
                + "is not Go tree-sitter-go parses"
            )


def _go_reader_breaches(package: dict[Path, SourceTree]) -> Iterator[Prose]:
    """Yield each line of a reader file comparing a word outside the lines the gate reads.

    Those are each line a mapped row of ``GO_REPLY_TEXT`` reads, which the gate
    reads, and of each switch and select statement of a function ``GO_UNTAGGED``
    names, which it reads past.
    """
    exempt = set(_mapped_sites(package))
    for module, function in GO_UNTAGGED.values():
        passed = go_function(package.get(module), function)
        if passed is None:
            yield Prose(
                f"GO_UNTAGGED names {module.relative_to(REPO_ROOT)}:{function}, not defined"
            )
            continue
        holders = (node for node in walk(passed) if node.type in _CASE_HOLDERS)
        exempt |= {(module, line) for holder in holders for line in go_lines(holder)}
    for path in GO_READER_FILES:
        tree = package.get(path)
        if tree is None:
            yield Prose(f"{path.relative_to(REPO_ROOT)} is no file of the Go package")
            continue
        for line in _go_comparisons(tree):
            if (path, line) not in exempt:
                yield Prose(
                    f"{path.relative_to(REPO_ROOT)}:{line}: {tree.line(TreeLine(line))!r} "
                    + "compares a word outside the lines GO_REPLY_TEXT reads"
                )


def go_untagged_rows(rows: Collection[ReplyPlace]) -> list[Prose]:
    """Return a divergence for each place ``GO_UNTAGGED`` reads past that ``replyText`` has."""
    return [
        Prose(
            f"reply place {place}: replyText has a row, so "
            + f"{module.relative_to(REPO_ROOT)}:{function}, "
            + "which GO_UNTAGGED reads past, reads a tag place; name it in GO_REPLY_TEXT"
        )
        for place, (module, function) in GO_UNTAGGED.items()
        if place in rows
    ]


def go_reader(go_codes: frozenset[ReplyWord]) -> BindingReader:
    """Return the Go reader, whose bound kinds are ``go_codes``.

    It adds each line of the package the grammar cannot parse, and each line of
    a reader file that could read a tag word outside its sets, to the places
    none reads.
    """

    def read(unread: list[Prose]) -> ReaderSets:
        package = _go_package()
        unread.extend(_go_unparsed(package))
        sets = read_sets(
            Prose("the Go reader"),
            Prose("GO_REPLY_TEXT"),
            GO_REPLY_TEXT,
            lambda spec: _go_words(spec, go_codes, package),
            unread,
        )
        unread.extend(_go_reader_breaches(package))
        return sets

    return read
