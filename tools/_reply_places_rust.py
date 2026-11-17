# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Rust reader of the reply-tags arm, ``tools/_reply_places.py``.

It reads the set the Rust binding's reply readers take at each string place of
``replyText`` from their own code, through tree-sitter-rust's syntax tree of
each file of the crate's library: the string-literal arms of a function's one
``match`` on its ``word``, the literals its ``field_word`` calls await, alone or
with the match function, whose every literal arm is one of them, each call
hands its word to as its first argument or through a ``let`` binding used for
nothing else, the words one method gives an enum's variants, which no line
elsewhere may give or reach, or the ``BOUND_KIND_*`` codes.  A match's final
``_`` arm, which reads every word its other arms do not name, reads as the word
of the arm building the variant it builds, or as no word when no other arm
builds it; behind a ``field_word`` call, the awaited words it reads and the
word of an arm building its variant are one word or none.  The arm holds its
word to the row's last word.  A line of a reader file comparing a word, a
literal of identifier shape as the compiler reads its escapes, outside the
lines these rows read is reported with each set the module cannot read, and a
function ``RUST_UNTAGGED`` reads past at its matches, which match a word at a
place ``replyText`` has no row for, is a divergence once it has one.  A
comparison, and a shape that could give a variant a second word, is read from a
file's tokens in order, which a macro's arguments are in the grammar too.  An
item ``#[cfg(test)]`` marks and a file of a test module are no part of the
library, and a line of the library the grammar cannot parse is reported, so
that no file is read past in silence.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, NewType

from tools._reply_places import (
    REPO_ROOT,
    AnyNonEmpty,
    Arms,
    MappingNames,
    ReaderSets,
    ReplyPlace,
    ReplyWord,
    UnnamedLast,
    mapped_last,
    read_sets,
)
from tools._reply_places_rust_tree import (
    RUST_COMMENTS,
    RUST_LANGUAGE,
    RUST_STRINGS,
    RustFile,
    Token,
    TokenAt,
    capital,
    holds,
    in_pattern,
    is_text,
    joined,
    opens_impl,
    path_name,
    plain,
    rust_comparisons,
    rust_file,
    test_modules,
    texts,
    whole_test,
    within,
)
from tools._reply_places_tree import (
    NodeKind,
    NodeText,
    SourceOffset,
    broken_lines,
    child_of,
    edge,
    first_line,
    node_lines,
    parse_source,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterator
    from pathlib import Path

    from tree_sitter import Node

    from tools._reply_places import BindingReader

RUST_SOURCE = REPO_ROOT / "rust" / "src"
RUST_RESPONSE = RUST_SOURCE / "response.rs"
RUST_REPLY_SHAPE = RUST_SOURCE / "reply_shape.rs"
RUST_DECODE = RUST_SOURCE / "dbc" / "decode.rs"
# The files of the crate that read a reply's words.
RUST_READER_FILES = (RUST_RESPONSE, RUST_REPLY_SHAPE, RUST_DECODE)

# A name in the Rust crate: a function, an enum, a variant or a constant.
RustSymbol = NewType("RustSymbol", str)
# Rust source: a file, a function of it or a fragment of either.
RustText = NewType("RustText", str)
# The number of a line of a Rust file, from 1.
RustLine = NewType("RustLine", int)


@dataclass(frozen=True)
class _RustMatch:
    """The string-literal arms of a function's one ``match word``, its last arm ``_``.

    The function takes the word first, as ``word: &str``, and uses it only as
    the match's scrutinee; each arm builds one variant of the type it returns,
    and the ``_`` arm reads as the word of an arm building the same variant.
    """

    module: Path
    function: RustSymbol


@dataclass(frozen=True)
class _RustWordCall:
    """The literals a function's ``field_word`` calls at a key await."""

    module: Path
    function: RustSymbol
    key: ReplyWord


@dataclass(frozen=True)
class _RustMappedWordCall:
    """The literals a function's ``field_word`` calls at a key await, and the match mapping them.

    ``mapping`` is read as a ``_RustMatch`` is, each literal arm an awaited word;
    its ``_`` arm reads the awaited words no literal arm names and the words of
    every arm building its variant, and must read one word or none.
    """

    module: Path
    function: RustSymbol
    key: ReplyWord
    mapping: RustSymbol


@dataclass(frozen=True)
class _RustEnumWords:
    """The words one method gives the variants of an enum declared once in the crate.

    A second word for a variant, or its word reached outside ``reader``, could
    stand for a word the method does not give, so the gate refuses, where it
    stands, a pattern of a variant outside ``words``, a reference to ``words``
    outside it and ``reader``, an import of the variants, an ``impl`` naming the
    enum other than the one holding ``words``, and an attribute on the enum or a
    variant other than a derive of traits that give no word.
    """

    module: Path
    enum: RustSymbol
    words: RustSymbol
    reader: RustSymbol


@dataclass(frozen=True)
class _RustBoundKinds:
    """The ``BOUND_KIND_*`` codes of ``rust/src/limits.rs``."""


type _RustSet = _RustMatch | _RustWordCall | _RustMappedWordCall | _RustEnumWords | _RustBoundKinds

# Every row of `replyText`, with the set the Rust reader takes at its place, read
# from the reader's own code, under the rules PYTHON_REPLY_TEXT is held to; a
# match's `_` arm, building a variant no other arm builds, reads the row's last
# word.
RUST_REPLY_TEXT: dict[ReplyPlace, _RustSet | AnyNonEmpty] = {
    ReplyPlace(place): spec
    for place, spec in {
        "status": _RustEnumWords(
            RUST_REPLY_SHAPE,
            RustSymbol("ReplyStatus"),
            RustSymbol("word"),
            RustSymbol("field_status"),
        ),
        "type": _RustWordCall(RUST_RESPONSE, RustSymbol("decode_frame"), ReplyWord("type")),
        "results/type": _RustWordCall(RUST_RESPONSE, RustSymbol("read_verdict"), ReplyWord("type")),
        "results/status <property>": _RustMappedWordCall(
            RUST_RESPONSE, RustSymbol("read_verdict"), ReplyWord("status"), RustSymbol("verdict")
        ),
        "warnings/kind": _RustWordCall(
            RUST_RESPONSE, RustSymbol("read_stream_warning"), ReplyWord("kind")
        ),
        "issues/severity": _RustMappedWordCall(
            RUST_RESPONSE, RustSymbol("read_issue"), ReplyWord("severity"), RustSymbol("severity")
        ),
        "warnings/severity": _RustMappedWordCall(
            RUST_RESPONSE, RustSymbol("read_issue"), ReplyWord("severity"), RustSymbol("severity")
        ),
        "bound_kind": _RustBoundKinds(),
        "dbc/messages/signals/byteOrder": _RustMappedWordCall(
            RUST_DECODE, RustSymbol("read_signal"), ReplyWord("byteOrder"), RustSymbol("byte_order")
        ),
        "dbc/messages/signals/presence": _RustMappedWordCall(
            RUST_DECODE, RustSymbol("read_signal"), ReplyWord("presence"), RustSymbol("presence")
        ),
        "dbc/messages/signals/multiplexor": AnyNonEmpty(),
        "dbc/comments/target/kind": _RustMappedWordCall(
            RUST_DECODE, RustSymbol("read_comment"), ReplyWord("kind"), RustSymbol("comment_target")
        ),
        "dbc/attributes/kind": _RustMappedWordCall(
            RUST_DECODE, RustSymbol("read_attribute"), ReplyWord("kind"), RustSymbol("attribute")
        ),
        "dbc/attributes/scope <definition>": _RustMappedWordCall(
            RUST_DECODE, RustSymbol("attribute"), ReplyWord("scope"), RustSymbol("attr_scope")
        ),
        "dbc/attributes/attrType/kind": _RustMappedWordCall(
            RUST_DECODE, RustSymbol("read_attr_type"), ReplyWord("kind"), RustSymbol("attr_type")
        ),
        "dbc/attributes/value/kind": _RustMappedWordCall(
            RUST_DECODE, RustSymbol("read_attr_value"), ReplyWord("kind"), RustSymbol("attr_value")
        ),
        "dbc/attributes/target/kind": _RustMappedWordCall(
            RUST_DECODE,
            RustSymbol("read_attr_target"),
            ReplyWord("kind"),
            RustSymbol("attr_target"),
        ),
    }.items()
}

# The functions of a reader file that match a word with literals at a place
# `replyText` has no row for, whose matches the gate reads past: an issue's code,
# a set that grows with the kernel's checks, read as unknown when unnamed.  A row
# `replyText` gains at the place is a divergence.
RUST_UNTAGGED: dict[ReplyPlace, tuple[Path, RustSymbol]] = {
    ReplyPlace("issues/code"): (RUST_RESPONSE, RustSymbol("from_wire")),
}

# The kinds of node, and the texts of tokens, the readers below read.
_FUNCTION = NodeKind("function_item")
_MATCH = NodeKind("match_expression")
_CALL = NodeKind("call_expression")
_ATTRIBUTE = NodeKind("attribute_item")
_WORD = NodeText("word")
_MATCH_TOKEN = NodeText("match")
_ARROW = NodeText("=>")
_PATH = NodeText("::")
_SELF = NodeText("Self")
_FIELD_WORD = NodeText("field_word")
# The uses of a match function's word: its parameter and the match's scrutinee.
_WORD_USES = 2
# The traits an enum whose words one method gives may derive, none giving a word.
_WORDLESS_TRAITS = frozenset(
    map(NodeText, ("Debug", "Clone", "Copy", "PartialEq", "Eq", "Hash", "PartialOrd", "Ord"))
)

# A line of a file of the crate.
type _RustSite = tuple[Path, RustLine]


def _shown(path: Path) -> Prose:
    """Return a path from the repository's root."""
    return Prose(str(path.relative_to(REPO_ROOT)))


def _module_dir(path: Path) -> Path:
    """Return the directory a file's child modules live in."""
    return path.parent if path.name in {"lib.rs", "main.rs", "mod.rs"} else path.parent / path.stem


def _rust_source(path: Path) -> RustText:
    """Return the source of a file of the crate."""
    return RustText(path.read_text(encoding="utf-8"))


def _rust_package() -> dict[Path, RustFile]:
    """Return every file of the crate's library outside its test modules, parsed."""
    trees = {
        path: parse_source(RUST_LANGUAGE, RUST_COMMENTS, path, NodeText(_rust_source(path)))
        for path in sorted(RUST_SOURCE.rglob("*.rs"))
    }
    tests = {
        _module_dir(path) / name for path, tree in trees.items() for name in test_modules(tree)
    }
    return {
        path: rust_file(tree)
        for path, tree in trees.items()
        if not whole_test(tree)
        and not any(path.with_suffix("") == test or test in path.parents for test in tests)
    }


def _rust_function(file: RustFile, name: RustSymbol) -> Node | Prose | None:
    """Return the function a file defines with a body, None when none is, or why not once."""
    found = [
        node
        for node in file.nodes(_FUNCTION)
        if is_text(file, node.child_by_field_name("name"), NodeText(name))
    ]
    if len(found) > 1:
        return Prose(f"is defined {len(found)} times, not once")
    return found[0] if found else None


@dataclass(frozen=True)
class _ArmReading:
    """The literals an arm's pattern names and their words, none for ``_``, and its variant."""

    literals: list[Node]
    words: list[ReplyWord]
    variant: RustSymbol


def _takes_word(file: RustFile, function: Node) -> bool:
    """Say whether a function takes the word first, as ``word: &str``."""
    match file.tree.named(function.child_by_field_name("parameters"))[:1]:
        case [parameter]:
            taken = parameter.child_by_field_name("type")
            return (
                is_text(file, parameter.child_by_field_name("pattern"), _WORD)
                and taken is not None
                and taken.type == "reference_type"
                and joined(*file.tokens_of(taken)[:2])
                and child_of(taken, NodeKind("mutable_specifier")) is None
                and is_text(file, taken.child_by_field_name("type"), NodeText("str"))
            )
        case _:
            return False


def _returned(file: RustFile, function: Node) -> RustSymbol | None:
    """Return the name opening the type a function returns, or returns in a ``Result``."""
    returned = function.child_by_field_name("return_type")
    if returned is not None and is_text(
        file, returned.child_by_field_name("type"), NodeText("Result")
    ):
        arguments = file.tree.named(returned.child_by_field_name("type_arguments"))
        returned = arguments[0] if arguments else None
    opening = None if returned is None else edge(returned, frozenset(), last=False)
    name = NodeText("") if opening is None else file.tree.text(opening)
    return RustSymbol(name) if capital(name) else None


def _match_head(file: RustFile, function: Node) -> tuple[RustSymbol, Node] | Prose:
    """Return the type a match function returns and its one match on ``word``."""
    run = texts(file.tokens_of(function))
    returned = _returned(file, function)
    held = [
        node
        for node in within(file, _MATCH, function)
        if is_text(file, node.child_by_field_name("value"), _WORD)
    ]
    if not _takes_word(file, function):
        return Prose("does not take the word first, as word: &str")
    if returned is None or len(held) != 1 or run.count(_MATCH_TOKEN) != 1:
        return Prose("is not one match on word returning a type of its own")
    if run.count(_WORD) != _WORD_USES:
        return Prose("uses word other than to match on it")
    return returned, held[0]


def _alternatives(file: RustFile, pattern: Node) -> list[Node]:
    """Return the patterns ``|`` joins in a pattern, in order."""
    if pattern.type != "or_pattern":
        return [pattern]
    return [part for joined in file.tree.named(pattern) for part in _alternatives(file, joined)]


def _arm_literals(file: RustFile, arm: Node) -> list[tuple[Node, ReplyWord]] | None:
    """Return the string literals ``|`` joins in an arm's pattern, unescaped, and their words."""
    match file.tree.named(arm):
        case [pattern, _]:
            parts = file.tree.named(pattern)
        case _:
            return None
    if len(parts) != 1:
        return None
    literals = [(part, plain(file.tree, part)) for part in _alternatives(file, parts[0])]
    words = [(part, word) for part, word in literals if word is not None]
    return words if len(words) == len(literals) else None


def _built(tokens: list[Token], kind: RustSymbol) -> list[RustSymbol]:
    """Return each variant of ``kind`` the tokens name, as ``kind::Variant`` names it."""
    return [
        RustSymbol(variant.text)
        for path, colons, variant in zip(tokens, tokens[1:], tokens[2:], strict=False)
        if path.text == kind and colons.text == _PATH and capital(variant.text)
    ]


def _arm_readings(file: RustFile, match: Node, kind: RustSymbol) -> list[_ArmReading] | Prose:
    """Return each arm's words and the variant of ``kind`` it builds, the ``_`` arm's words none."""
    arms = file.tree.named(match.child_by_field_name("body"))
    patterns = [
        file.tree.code(SourceOffset(arm.start_byte), SourceOffset(arrow.start_byte))
        if (arrow := child_of(arm, NodeKind(_ARROW))) is not None
        else file.tree.code_of(arm)
        for arm in arms
    ]
    if not arms or patterns[-1] != "_":
        return Prose("its match's last arm is not _")
    readings: list[_ArmReading] = []
    for index, (arm, pattern) in enumerate(zip(arms, patterns, strict=True)):
        value = arm.child_by_field_name("value")
        built = [] if value is None else _built(file.tokens_of(value), kind)
        literals = [] if index == len(arms) - 1 else _arm_literals(file, arm)
        if literals is None:
            return Prose(f"the arm {pattern!r} is neither _ nor string literals joined by |")
        if len(built) != 1:
            return Prose(f"the arm {pattern!r} builds {len(built)} variants of {kind}, not one")
        readings.append(
            _ArmReading([part for part, _ in literals], [word for _, word in literals], built[0])
        )
    return readings


def _match_arms(file: RustFile, function: Node) -> tuple[Arms, frozenset[ReplyWord]] | Prose:
    """Return the words a function's match on ``word`` names and the word its ``_`` arm reads as.

    The ``_`` arm reads as the last word of the last arm building the variant it
    builds, and as no word when no other arm builds that variant; beside them
    come the words of every arm building that variant.
    """
    head = _match_head(file, function)
    if isinstance(head, str):
        return head
    kind, match = head
    readings = _arm_readings(file, match, kind)
    if isinstance(readings, str):
        return readings
    words = [word for reading in readings for word in reading.words]
    if len(set(words)) != len(words):
        return Prose("its match names a word twice")
    patterns = {literal for reading in readings for literal in reading.literals}
    if any(hit not in patterns for hit in rust_comparisons(file, file.tokens_of(function))):
        return Prose("compares a word other than in its match's patterns")
    *named, last = readings
    sharing = [reading.words for reading in named if reading.variant == last.variant]
    shared = frozenset(word for words in sharing for word in words)
    return Arms(frozenset(words), sharing[-1][-1] if sharing else UnnamedLast()), shared


def _awaited(file: RustFile, arguments: Node) -> tuple[ReplyWord, list[Node]] | None:
    """Return the literal key a ``field_word`` call's arguments read at and its words, or None.

    The arguments hold no call of their own; the key is a literal written with
    no escape, the last argument but one, and the words a borrowed array, the last.
    """
    args = file.tree.named(arguments)
    inner = texts(file.tokens_of(arguments)[1:-1])
    if len(args) < len(("obj", "key", "words")) or "(" in inner or ")" in inner:
        return None
    key, words = plain(file.tree, args[-2]), args[-1]
    listed = words.child_by_field_name("value")
    if key is None or words.type != "reference_expression" or listed is None:
        return None
    if child_of(words, NodeKind("mutable_specifier")) or listed.type != "array_expression":
        return None
    return key, file.tree.named(listed)


@dataclass(frozen=True)
class _KeyCall:
    """A ``field_word`` call at a key and the words it awaits."""

    node: Node
    words: frozenset[ReplyWord]


def _key_calls(file: RustFile, function: Node, key: ReplyWord) -> list[_KeyCall] | Prose:
    """Return each ``field_word`` call of a function at ``key``, in order."""
    calls: list[_KeyCall] = []
    for call in within(file, _CALL, function):
        called = call.child_by_field_name("function")
        arguments = call.child_by_field_name("arguments")
        if called is None or not is_text(file, edge(called, frozenset(), last=True), _FIELD_WORD):
            continue
        awaited = None if arguments is None else _awaited(file, arguments)
        if arguments is None or awaited is None:
            return Prose("a field_word call holds a call of its own, or no literal key and words")
        if awaited[0] != key:
            continue
        found = [plain(file.tree, word) for word in awaited[1]]
        if not found or None in found:
            inside = (SourceOffset(arguments.start_byte + 1), SourceOffset(arguments.end_byte - 1))
            written = file.tree.code(*inside)
            return Prose(f"field_word({written}) awaits a word that is not a literal")
        calls.append(_KeyCall(call, frozenset(word for word in found if word is not None)))
    return calls


def _word_call_words(
    file: RustFile, function: Node, key: ReplyWord
) -> tuple[frozenset[ReplyWord], list[_KeyCall]] | Prose:
    """Return the words a function's ``field_word`` calls at ``key`` await, and the calls."""
    calls = _key_calls(file, function, key)
    if isinstance(calls, str):
        return calls
    words = frozenset(word for call in calls for word in call.words)
    return (words, calls) if words else Prose(f"no field_word call at {key!r}")


def _unraw(name: NodeText) -> NodeText:
    """Return a name as Rust reads it, ``r#`` cut from a raw identifier."""
    return NodeText(name.removeprefix("r#"))


def _first_argument_of(file: RustFile, argument: Node | None, mapping: RustSymbol) -> bool:
    """Say whether a node is the first argument of a call of ``mapping`` by its bare name."""
    arguments = None if argument is None else argument.parent
    call = None if arguments is None else arguments.parent
    return (
        call is not None
        and is_text(file, call.child_by_field_name("function"), NodeText(mapping))
        and file.tree.named(arguments)[:1] == [argument]
    )


def _handed(spec: _RustMappedWordCall, file: RustFile, function: Node, call: Node) -> Prose | None:
    """Return why a ``field_word`` call at a mapped row's key does not hand its word to the mapping.

    The call, ``?`` after it, is the mapping's first argument, which its
    ``word`` parameter takes, or the value of a ``let`` whose name the function
    uses once more, as that argument; None when it is so.
    """
    parent = call.parent
    tried = parent if parent is not None and parent.type == "try_expression" else None
    held = None if tried is None else tried.parent
    if _first_argument_of(file, tried, spec.mapping):
        return None
    bound = None
    if held is not None and held.type == "let_declaration":
        bound = held.child_by_field_name("pattern")
    if bound is None:
        return Prose(
            f"does not hand the word field_word reads at {spec.key!r} to {spec.mapping}, "
            + "as its first argument or through a let"
        )
    name = _unraw(file.tree.text(bound))
    uses = [token.node for token in file.tokens_of(function) if _unraw(token.text) == name]
    if len(uses) != len(("let", "argument")) or not _first_argument_of(
        file, uses[-1], spec.mapping
    ):
        return Prose(f"uses {name} other than once, as the first argument of {spec.mapping}")
    return None


def _mapped_words(
    spec: _RustMappedWordCall, file: RustFile, function: Node
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return the words a caller's ``field_word`` calls await and the word its mapping's _ reads.

    Each call hands its word to the mapping, as ``_handed`` reads it.
    """
    awaited = _word_call_words(file, function, spec.key)
    mapping = _rust_function(file, spec.mapping)
    if isinstance(awaited, str):
        return awaited
    words, calls = awaited
    unhanded = (_handed(spec, file, function, call.node) for call in calls)
    refused = next((why for why in unhanded if why is not None), None)
    if refused is not None:
        return refused
    if mapping is None or isinstance(mapping, str):
        return Prose(f"{spec.mapping} {mapping or 'is not defined'}")
    read = _match_arms(file, mapping)
    if isinstance(read, str):
        return Prose(f"{spec.mapping}: {read}")
    arms, shared = read
    return _mapped_last(spec, words, arms.words, shared)


def _mapped_last(
    spec: _RustMappedWordCall,
    awaited: frozenset[ReplyWord],
    named: frozenset[ReplyWord],
    shared: frozenset[ReplyWord],
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return the awaited words and the one word a mapping's ``_`` arm reads, or them alone if none.

    Each word a literal arm names is an awaited word; the ``_`` arm reads the
    others and ``shared``, the words of every arm building its variant.
    """
    names = MappingNames(
        Prose(spec.mapping),
        Prose(f"field_word call at {spec.key!r}"),
        Prose(f"the _ arm of {spec.mapping}"),
    )
    return mapped_last(awaited, named, shared, names)


def _attributes(item: Node) -> list[Node]:
    """Return the attributes on an item, in order."""
    found: list[Node] = []
    before = item.prev_named_sibling
    while before is not None and before.type in RUST_COMMENTS | {_ATTRIBUTE}:
        if before.type == _ATTRIBUTE:
            found.insert(0, before)
        before = before.prev_named_sibling
    return found


def _derives_wordless(file: RustFile, attribute: Node) -> bool:
    """Say whether an attribute derives traits alone, none of which gives a word."""
    tokens = file.tokens_of(attribute)
    match texts(tokens):
        case ["#", "[", "derive", "(", *traits, ")", "]"] if joined(tokens[2], tokens[3]):
            derived: list[list[NodeText]] = [[]]
            for trait in traits:
                if trait == ",":
                    derived.append([])
                else:
                    derived[-1].append(trait)
            return all(len(each) <= 1 and set(each) <= _WORDLESS_TRAITS for each in derived)
        case _:
            return False


def _enum_variants(spec: _RustEnumWords, file: RustFile, enum: Node) -> list[RustSymbol] | Prose:
    """Return an enum's variants, or why the enum or a variant could carry a word unread."""
    for attribute in _attributes(enum):
        if not _derives_wordless(file, attribute):
            inside = (
                SourceOffset(attribute.start_byte + len("#[")),
                SourceOffset(attribute.end_byte - 1),
            )
            return Prose(f"#[{file.tree.code(*inside)}] on {spec.enum} could give it a word")
    variants = file.tree.named(enum.child_by_field_name("body"))
    names = [variant.child_by_field_name("name") for variant in variants]
    if any(
        name is None or len(file.tree.named(variant)) != 1 or not capital(file.tree.text(name))
        for variant, name in zip(variants, names, strict=True)
    ):
        return Prose(f"a variant of {spec.enum} is not a unit variant without an attribute")
    return [RustSymbol(file.tree.text(name)) for name in names if name is not None]


def _given_words(
    spec: _RustEnumWords, module: RustFile, giver: Node, variants: list[RustSymbol]
) -> frozenset[ReplyWord] | Prose:
    """Return the word a method's one match on ``self`` gives each variant, or why it cannot."""
    body = giver.child_by_field_name("body")
    tokens = [] if body is None else module.tokens_of(body)
    run = texts(tokens)
    arms = [
        (variant.text, word)
        for path, colons, variant, arrow, given in zip(
            tokens, tokens[1:], tokens[2:], tokens[3:], tokens[4:], strict=False
        )
        if path.text in {spec.enum, _SELF}
        and colons.text == _PATH
        and arrow.text == _ARROW
        and (word := plain(module.tree, given.node)) is not None
    ]
    shaped = (
        run.count(_MATCH_TOKEN) == 1
        and any(run[at : at + 3] == ["match", "self", "{"] for at in range(len(run)))
        and "return" not in run
        and run.count(_ARROW) == len(arms)
        and sum(token.node.type in RUST_STRINGS for token in tokens) == len(arms)
    )
    if not shaped:
        return Prose("its body is not one match on self, each arm one variant giving one literal")
    words = [word for _, word in arms]
    if sorted(variant for variant, _ in arms) != sorted(variants) or len(set(words)) != len(words):
        return Prose(f"its arms do not give each variant of {spec.enum} its own word")
    return frozenset(words)


def _holding_impl(file: RustFile, enum: RustSymbol, giver: Node) -> Node | None:
    """Return the ``impl`` naming ``enum`` before its body that holds ``giver``, or None."""
    for impl in file.nodes(NodeKind("impl_item")):
        body = impl.child_by_field_name("body")
        if body is None or not holds(body, giver):
            continue
        head = [token for part in impl.children if part != body for token in file.tokens_of(part)]
        if enum in texts(head):
            return impl
    return None


@dataclass(frozen=True)
class _RustBreach:
    """A shape that could give a variant a second word or reach its word, and where it may stand.

    ``opens`` says whether the shape opens at a token of a file; the shape may
    stand in ``exempt``, nodes of the enum's module, and is looked for only in
    ``within`` when it is given.
    """

    opens: Callable[[list[NodeText], TokenAt], bool]
    what: Prose
    exempt: tuple[Node, ...]
    within: Node | None


def _enum_breach_shapes(
    spec: _RustEnumWords, giver: Node, reader: Node, holder: Node
) -> tuple[_RustBreach, ...]:
    """Return the shapes that could give a variant a second word or reach its word elsewhere."""
    enum, words = NodeText(spec.enum), NodeText(spec.words)
    reach = Prose(f"reaches {words} outside {spec.reader}")
    second = Prose(f"matches on a {enum} outside {words}, which could give it a second word")
    return (
        _RustBreach(
            lambda run, at: (
                (run[at] == "." and run[at + 1 : at + 2] == [words])
                or path_name(run, at, enum) == words
            ),
            reach,
            (giver, reader),
            None,
        ),
        _RustBreach(
            lambda run, at: path_name(run, at, _SELF) == words, reach, (giver, reader), holder
        ),
        _RustBreach(lambda run, at: in_pattern(run, at, enum), second, (giver,), None),
        _RustBreach(lambda run, at: in_pattern(run, at, _SELF), second, (giver,), holder),
        _RustBreach(
            lambda run, at: path_name(run, at, enum) in {"{", "*"},
            Prose(f"imports the variants of {enum}, which a pattern could name bare"),
            (),
            None,
        ),
        _RustBreach(
            lambda run, at: opens_impl(run, at, enum),
            Prose(f"implements for {enum} beside the impl holding {words}"),
            (holder,),
            None,
        ),
    )


def _excused(shape: _RustBreach, at: Node) -> bool:
    """Whether a shape standing at a token is one the gate allows there.

    It is outside ``within`` when that is given, a node of the enum's module
    no token of another file stands in, or in a node ``exempt`` names.
    """
    if shape.within is not None and not holds(shape.within, at):
        return True
    return any(holds(span, at) for span in shape.exempt)


def _enum_word_breaches(
    spec: _RustEnumWords, package: dict[Path, RustFile], giver: Node
) -> Iterator[Prose]:
    """Yield each line that could give a variant a second word or reach its word elsewhere."""
    module = package[spec.module]
    reader = _rust_function(module, spec.reader)
    holder = _holding_impl(module, spec.enum, giver)
    if reader is None or isinstance(reader, str) or holder is None:
        yield Prose(
            f"{_shown(spec.module)}: {spec.reader} is not defined once, "
            + f"or {spec.words} is no method of an impl of {spec.enum}"
        )
        return
    shapes = _enum_breach_shapes(spec, giver, reader, holder)
    for path, file in package.items():
        run = texts(list(file.tokens))
        for shape in shapes:
            for at, token in enumerate(file.tokens):
                if shape.opens(run, TokenAt(at)) and not _excused(shape, token.node):
                    line = first_line(token.node)
                    yield Prose(f"{_shown(path)}:{line}: {file.tree.line(line)!r} {shape.what}")


def _rust_enum_words(
    spec: _RustEnumWords, package: dict[Path, RustFile]
) -> frozenset[ReplyWord] | Prose:
    """Return the word a method gives each variant of an enum, or each line that hides them."""
    where = f"{_shown(spec.module)}:{spec.enum}::{spec.words}"
    declared = [
        (path, node)
        for path, file in package.items()
        for node in file.nodes(NodeKind("enum_item"))
        if is_text(file, node.child_by_field_name("name"), NodeText(spec.enum))
        and node.child_by_field_name("type_parameters") is None
    ]
    if [path for path, _ in declared] != [spec.module]:
        return Prose(f"{spec.enum} is not declared once, in {_shown(spec.module)}")
    module = package[spec.module]
    variants = _enum_variants(spec, module, declared[0][1])
    giver = _rust_function(module, spec.words)
    if isinstance(variants, str) or giver is None or isinstance(giver, str):
        return Prose(f"{where}: {variants if isinstance(variants, str) else 'not defined once'}")
    words = _given_words(spec, module, giver, variants)
    if isinstance(words, str):
        return Prose(f"{where}: {words}")
    breaches = list(dict.fromkeys(_enum_word_breaches(spec, package, giver)))
    return Prose("; ".join(breaches)) if breaches else words


def _rust_words(
    spec: _RustSet, rust_codes: frozenset[ReplyWord], package: dict[Path, RustFile]
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return a Rust reader set's words and last arm, or why the gate cannot read them."""
    if isinstance(spec, _RustBoundKinds):
        return rust_codes
    if isinstance(spec, _RustEnumWords):
        return _rust_enum_words(spec, package)
    where = f"{_shown(spec.module)}:{spec.function}"
    file = package.get(spec.module)
    function = None if file is None else _rust_function(file, spec.function)
    if file is None or function is None or isinstance(function, str):
        return Prose(f"{where} {function or 'is not defined'}")
    if isinstance(spec, _RustMatch):
        read = _match_arms(file, function)
        found = read if isinstance(read, str) else read[0]
    elif isinstance(spec, _RustMappedWordCall):
        found = _mapped_words(spec, file, function)
    else:
        awaited = _word_call_words(file, function, spec.key)
        found = awaited if isinstance(awaited, str) else awaited[0]
    return Prose(f"{where}: {found}") if isinstance(found, str) else found


def _defined(
    package: dict[Path, RustFile], module: Path, function: RustSymbol
) -> tuple[RustFile, Node] | None:
    """Return a file of the crate and its function, None when the file does not define it once."""
    file = package.get(module)
    found = None if file is None else _rust_function(file, function)
    if file is None or found is None or isinstance(found, str):
        return None
    return file, found


def _match_sites(
    package: dict[Path, RustFile], module: Path, function: RustSymbol
) -> frozenset[_RustSite]:
    """Return the lines of a function's matches, each from its head to its closing brace."""
    defined = _defined(package, module, function)
    if defined is None:
        return frozenset()
    file, found = defined
    matches = within(file, _MATCH, found)
    return frozenset((module, RustLine(line)) for match in matches for line in node_lines(match))


def _call_sites(package: dict[Path, RustFile], spec: _RustMappedWordCall) -> frozenset[_RustSite]:
    """Return the lines of a mapped row's ``field_word`` calls at its key, none if one is unread."""
    defined = _defined(package, spec.module, spec.function)
    calls = None if defined is None else _key_calls(*defined, spec.key)
    if calls is None or isinstance(calls, str):
        return frozenset()
    return frozenset(
        (spec.module, RustLine(line)) for call in calls for line in node_lines(call.node)
    )


def _read_sites(package: dict[Path, RustFile]) -> frozenset[_RustSite]:
    """Return the lines of the crate the rows read, and those the gate reads past.

    A match row reads its function's match, and a mapped row its mapping's and
    its calls at its key; the gate reads past the matches of a function
    ``RUST_UNTAGGED`` names.  A function its file does not define once gives none.
    """
    sites: set[_RustSite] = set()
    for spec in RUST_REPLY_TEXT.values():
        if isinstance(spec, _RustMatch):
            sites |= _match_sites(package, spec.module, spec.function)
        elif isinstance(spec, _RustMappedWordCall):
            sites |= _match_sites(package, spec.module, spec.mapping) | _call_sites(package, spec)
    for module, function in RUST_UNTAGGED.values():
        sites |= _match_sites(package, module, function)
    return frozenset(sites)


def rust_read_sites() -> frozenset[_RustSite]:
    """Return the lines of the crate as it stands that ``_read_sites`` names."""
    return _read_sites(_rust_package())


def _rust_unparsed(package: dict[Path, RustFile]) -> Iterator[Prose]:
    """Yield each line of the crate's library holding code the grammar cannot parse."""
    for path, file in package.items():
        for line in broken_lines(file.tree):
            yield Prose(
                f"{_shown(path)}:{line}: {file.tree.line(line)!r} "
                + "is not Rust tree-sitter-rust parses"
            )


def _rust_reader_breaches(package: dict[Path, RustFile]) -> Iterator[Prose]:
    """Yield each line of a reader file comparing a word outside the lines ``_read_sites`` names."""
    for module, function in sorted(set(RUST_UNTAGGED.values())):
        if _defined(package, module, function) is None:
            yield Prose(f"RUST_UNTAGGED names {_shown(module)}:{function}, not defined once")
    exempt = _read_sites(package)
    for path in RUST_READER_FILES:
        file = package.get(path)
        if file is None:
            yield Prose(f"{_shown(path)} is no file of the crate's library")
            continue
        hits = {first_line(node) for node in rust_comparisons(file, list(file.tokens))}
        for line in sorted(hits - {line for module, line in exempt if module == path}):
            yield Prose(
                f"{_shown(path)}:{line}: {file.tree.line(line)!r} "
                + "compares a word outside the lines RUST_REPLY_TEXT reads"
            )


def rust_untagged_rows(rows: Collection[ReplyPlace]) -> list[Prose]:
    """Return a divergence for each place ``RUST_UNTAGGED`` reads past that ``replyText`` has."""
    return [
        Prose(
            f"reply place {place}: replyText has a row, so {_shown(module)}:{function}, "
            + "which RUST_UNTAGGED reads past, reads a tag place; name it in RUST_REPLY_TEXT"
        )
        for place, (module, function) in RUST_UNTAGGED.items()
        if place in rows
    ]


def rust_reader(rust_codes: frozenset[ReplyWord]) -> BindingReader:
    """Return the Rust reader, whose bound kinds are ``rust_codes``.

    It adds each line of the library the grammar cannot parse, and each line of
    a reader file that could read a tag word outside its sets, to the places
    none reads.
    """

    def read(unread: list[Prose]) -> ReaderSets:
        package = _rust_package()
        unread.extend(_rust_unparsed(package))
        sets = read_sets(
            Prose("the Rust reader"),
            Prose("RUST_REPLY_TEXT"),
            RUST_REPLY_TEXT,
            lambda spec: _rust_words(spec, rust_codes, package),
            unread,
        )
        unread.extend(_rust_reader_breaches(package))
        return sets

    return read
