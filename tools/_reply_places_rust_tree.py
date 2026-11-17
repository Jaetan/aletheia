# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What the Rust reader of the reply-tags arm reads Rust's syntax with.

``tools/_reply_places_rust.py`` reads each row through tree-sitter-rust's syntax
tree of a file of the crate.  This module holds what its readers share about
Rust: the grammar and the kinds of node its comments and literals have, a
literal's text as the compiler reads its escapes, whether a literal holds a
word, the text of a string literal written with no escape, a file of the
library (its tree, the items ``#[cfg(test)]`` marks, written so, which no
reader reads, and its tokens outside them in source order), a path and an
``impl`` its tokens spell, and each comparison that could read a word.  A
macro's arguments are tokens alone in the grammar, so what the tokens spell is
read there too.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import islice
from typing import TYPE_CHECKING, NewType

import tree_sitter_rust
from tree_sitter import Language

from tools._reply_places import CodePoint, LiteralText, ReplyWord, read_text, scalar
from tools._reply_places_tree import NodeKind, NodeText, SourceTree, holds_word, walk

if TYPE_CHECKING:
    from tree_sitter import Node

# The index of a token among a run of a file's tokens, from 0; and how many
# tokens one comparison spans.
TokenAt = NewType("TokenAt", int)
_Span = NewType("_Span", int)

# The Rust grammar, and the kinds of node a comment and a literal have.
RUST_LANGUAGE = Language(tree_sitter_rust.language())
RUST_COMMENTS = frozenset({NodeKind("line_comment"), NodeKind("block_comment")})
_STRING = NodeKind("string_literal")
_RAW = NodeKind("raw_string_literal")
_CHAR = NodeKind("char_literal")
RUST_STRINGS = frozenset({_STRING, _RAW})
RUST_LITERALS = RUST_STRINGS | {_CHAR}
_CONTENT = NodeKind("string_content")
_ESCAPE = NodeKind("escape_sequence")
_ATTRIBUTE = NodeKind("attribute_item")
# What each named escape reads as; the greatest byte a byte escape may name; the
# most digits a Unicode escape takes; a line continuation, and the white space
# after it the compiler skips.  The grammar hands an escape over as `\` and one
# character, `\x` and two hex digits, or `\u{}` around one hex digit or more,
# and refuses any other, the `_` Rust allows among a Unicode escape's digits
# included.
_NAMED = dict(zip("nrt\\0'\"", "\n\r\t\\\0'\"", strict=True))
_MAX_ASCII = 0x7F
_UNICODE_WIDTH = 6
_CONTINUED = NodeText("\\\n")
_SKIPPED = " \t\n\r"
# The attribute marking an item, and a whole file, compiled for the tests alone, as written.
_OUTER_TEST = NodeText("#[cfg(test)]")
_INNER_TEST = NodeText("#![cfg(test)]")
# The tokens beside a string literal holding a word that compare it: an
# operator before it, a borrow perhaps between; an operator, an arm's arrow, a
# pattern's `|` or a guard's `if` after it, which also follow a path in a
# pattern.  The tokens of the longest comparison, `== & "<word>"`.  The methods
# comparing the value they are called on with their arguments.
_OPERATORS = frozenset(map(NodeText, ("==", "!=")))
_AFTER_PATTERN = frozenset(map(NodeText, ("=>", "|", "if")))
_AFTER_WORD = _OPERATORS | _AFTER_PATTERN
_LONGEST = _Span(3)
_COMPARING_METHODS = frozenset(
    map(
        NodeText,
        (
            "eq",
            "ne",
            "eq_ignore_ascii_case",
            "starts_with",
            "ends_with",
            "strip_prefix",
            "strip_suffix",
        ),
    )
)
_OPENING = frozenset(map(NodeText, "({"))
_CLOSING = frozenset(map(NodeText, ")]}"))
_PATH = NodeText("::")


def _rust_escape(escape: NodeText) -> LiteralText | None:
    """Return what an escape reads as, None when Rust reads none, a line continuation as none."""
    kind, digits = escape[1:2], escape[2:]
    if escape == _CONTINUED:
        return LiteralText("")
    if kind in _NAMED:
        return LiteralText(_NAMED[kind])
    if kind == "x":
        return LiteralText(chr(int(digits, 16))) if int(digits, 16) <= _MAX_ASCII else None
    braced = digits[1:-1]
    if kind == "u" and len(braced) <= _UNICODE_WIDTH:
        return scalar(CodePoint(int(braced, 16)))
    return None


def rust_read(tree: SourceTree, literal: Node) -> LiteralText | None:
    """Return the text a Rust string or character literal holds, as the compiler reads it.

    A raw string's is its text as written; None when an escape is none Rust reads.
    """
    if literal.type == _CHAR:
        written = tree.text(literal)
        inside = written[written.index("'") + 1 : -1]
        return _rust_escape(NodeText(inside)) if inside.startswith("\\") else LiteralText(inside)
    if literal.type == _RAW:
        return LiteralText("".join(tree.text(part) for part in literal.named_children))
    parts: list[LiteralText | None] = []
    continued = False
    for part in literal.children:
        if part.type == _CONTENT:
            text = tree.text(part)
            parts.append(LiteralText(text.lstrip(_SKIPPED) if continued else text))
        elif part.type == _ESCAPE:
            parts.append(_rust_escape(tree.text(part)))
        continued = part.type == _ESCAPE and tree.text(part) == _CONTINUED
    return read_text(parts)


def is_word(tree: SourceTree, node: Node) -> bool:
    """Say whether a node is a string literal holding a word."""
    return node.type in RUST_STRINGS and holds_word(rust_read(tree, node))


def holds_no_word(tree: SourceTree, node: Node) -> bool:
    """Say whether a node is a string or character literal holding no word."""
    return node.type in RUST_LITERALS and not holds_word(rust_read(tree, node))


def plain(tree: SourceTree, node: Node) -> ReplyWord | None:
    """Return the text of a string literal opened by a bare quote and written with no escape."""
    parts = node.named_children
    if node.type != _STRING or tree.text(node.children[0]) != '"':
        return None
    if any(part.type != _CONTENT for part in parts):
        return None
    return ReplyWord("".join(tree.text(part) for part in parts))


@dataclass(frozen=True)
class Token:
    """A token of a file, a literal read whole, and its text."""

    node: Node
    text: NodeText


def holds(holder: Node, node: Node) -> bool:
    """Say whether ``node`` is ``holder`` or stands in it."""
    current: Node | None = node
    while current is not None and current != holder:
        current = current.parent
    return current is not None


@dataclass(frozen=True)
class RustFile:
    """A file of the crate, parsed: its tree, its test items, and its other tokens.

    A test item is the ``#[cfg(test)]`` marking an item, the attributes after
    it and the item; ``tokens`` are the file's tokens outside them but its
    comments, in order.
    """

    tree: SourceTree
    tests: frozenset[Node]
    tokens: tuple[Token, ...]

    def live(self, node: Node) -> bool:
        """Say whether a node stands outside every test item."""
        return not any(holds(test, node) for test in self.tests)

    def nodes(self, kind: NodeKind) -> list[Node]:
        """Return the file's nodes of ``kind`` outside its test items, in source order."""
        return [node for node in self.tree.nodes(kind) if self.live(node)]

    def tokens_of(self, node: Node) -> list[Token]:
        """Return the tokens of a node outside the file's test items, in order."""
        return _tokens(self.tree, node, self.tests)


def _tokens(tree: SourceTree, node: Node, skipped: frozenset[Node]) -> list[Token]:
    """Return a node's tokens in order: its leaves and literals but its comments and ``skipped``."""
    found: list[Token] = []
    stack = [node]
    while stack:
        current = stack.pop()
        if current.type in tree.comments or current in skipped:
            continue
        if current.type in RUST_LITERALS or not current.children:
            found.append(Token(current, tree.text(current)))
            continue
        stack.extend(reversed(current.children))
    return found


def _marked(tree: SourceTree, attribute: Node) -> list[Node]:
    """Return an attribute, the attributes after it and the item they mark, or none past it.

    The item is the next part beside the attribute but comments and attributes.
    """
    marked = [attribute]
    item = attribute.next_named_sibling
    while item is not None and (item.type in tree.comments or item.type == _ATTRIBUTE):
        if item.type == _ATTRIBUTE:
            marked.append(item)
        item = item.next_named_sibling
    return marked if item is None else [*marked, item]


def _test_attributes(tree: SourceTree) -> list[Node]:
    """Return each ``#[cfg(test)]`` of a file."""
    return [node for node in tree.nodes(_ATTRIBUTE) if tree.text(node) == _OUTER_TEST]


def rust_file(tree: SourceTree) -> RustFile:
    """Return a parsed file of the crate, its test items found."""
    tests = frozenset(node for found in _test_attributes(tree) for node in _marked(tree, found))
    return RustFile(tree, tests, tuple(_tokens(tree, tree.root, tests)))


def test_modules(tree: SourceTree) -> list[NodeText]:
    """Return the name of each module ``#[cfg(test)] mod <name>;`` declares in a file of its own."""
    modules = [_marked(tree, attribute)[-1] for attribute in _test_attributes(tree)]
    return [
        tree.text(name)
        for module in modules
        if module.type == "mod_item"
        and module.child_by_field_name("body") is None
        and (name := module.child_by_field_name("name")) is not None
    ]


def whole_test(tree: SourceTree) -> bool:
    """Say whether a file compiles for the tests alone: whether it holds ``#![cfg(test)]``."""
    inner = tree.nodes(NodeKind("inner_attribute_item"))
    return any(tree.text(node) == _INNER_TEST for node in inner)


def texts(tokens: list[Token]) -> list[NodeText]:
    """Return the texts of tokens, in order."""
    return [token.text for token in tokens]


def capital(text: NodeText) -> bool:
    """Say whether a token opens with an ASCII capital letter."""
    return text[:1].isascii() and text[:1].isupper()


def is_name(text: NodeText) -> bool:
    """Say whether a token is a name or a number: letters, digits and ``_`` alone."""
    return all(char == "_" or char.isalnum() for char in text)


def is_text(file: RustFile, node: Node | None, text: NodeText) -> bool:
    """Say whether a node is written ``text``."""
    return node is not None and file.tree.text(node) == text


def within(file: RustFile, kind: NodeKind, holder: Node) -> list[Node]:
    """Return the nodes of ``kind`` in a node outside the file's test items, in source order."""
    return [node for node in walk(holder) if node.type == kind and file.live(node)]


def path_name(run: list[NodeText], at: TokenAt, path: NodeText) -> NodeText | None:
    """Return the name a path ``<path>::<name>`` opening at ``at`` reaches, or None."""
    if run[at] != path or run[at + 1 : at + 2] != [_PATH]:
        return None
    return next(iter(run[at + 2 : at + 3]), None)


def opens_impl(run: list[NodeText], at: TokenAt, name: NodeText) -> bool:
    """Say whether an ``impl`` naming ``name`` before its body opens at ``at``."""
    if run[at] != "impl":
        return False
    for text in run[at + 1 :]:
        if text in {"{", ";"}:
            return False
        if text == name:
            return True
    return False


def in_pattern(run: list[NodeText], at: TokenAt, path: NodeText) -> bool:
    """Say whether ``<path>::<name>`` opens at ``at`` as a pattern: an arrow, `|` or `if` after."""
    name = path_name(run, at, path)
    after = next(iter(run[at + 3 : at + 4]), None)
    return name is not None and is_name(name) and after in _AFTER_PATTERN


def _compared(file: RustFile, ahead: list[Token]) -> _Span:
    """Return how many tokens a comparison that could read a word opening ``ahead`` spans, or 0."""
    words = [is_word(file.tree, token.node) for token in ahead]
    match texts(ahead):
        case [operator, _, *_] if operator in _OPERATORS and words[1]:
            return _Span(2)
        case [operator, "&", _] if operator in _OPERATORS and words[2]:
            return _Span(3)
        case [_, after, *_] if words[0] and after in _AFTER_WORD:
            return _Span(2)
        case ["let", _, *_] if words[1]:
            return _Span(2)
        case ["matches", "!", *_] if joined(ahead[0], ahead[1]):
            return _Span(2)
        case _:
            return _Span(0)


def _arguments(tokens: list[Token], opening: TokenAt) -> list[list[Token]]:
    """Return the arguments of the call whose ``(`` stands at ``opening``, a trailing comma none."""
    arguments: list[list[Token]] = [[]]
    depth = 0
    for token in islice(tokens, opening, None):
        if token.text in _CLOSING:
            depth -= 1
            if depth == 0:
                break
        if depth == 1 and token.text == ",":
            arguments.append([])
        elif depth:
            arguments[-1].append(token)
        if token.text in _OPENING:
            depth += 1
    return [argument for argument in arguments if argument]


def joined(first: Token, second: Token) -> bool:
    """Say whether a token ends where the next opens, with no space or comment between."""
    return first.node.end_byte == second.node.start_byte


def _compares_call(file: RustFile, tokens: list[Token], dot: TokenAt) -> bool:
    """Say whether the ``.`` at ``dot`` calls a comparing method but with literals of no word.

    The method's name follows the ``.`` with nothing between.
    """
    method = tokens[dot + 1 : dot + 3]
    if texts(method)[1:] != ["("] or method[0].text not in _COMPARING_METHODS:
        return False
    if not joined(tokens[dot], method[0]):
        return False
    return not all(
        len(argument) == 1 and holds_no_word(file.tree, argument[0].node)
        for argument in _arguments(tokens, TokenAt(dot + 2))
    )


def rust_comparisons(file: RustFile, tokens: list[Token]) -> list[Node]:
    """Return the token each comparison that could read a word opens with, among ``tokens``.

    A string literal holding a word compares it after an ``==`` or ``!=``, a
    borrow perhaps between, or after ``let``, and before an ``==``, ``!=``, an
    arm's ``=>``, a pattern's ``|`` or a guard's ``if``, the tokens of one
    comparison read once; so does ``matches!`` and a call of a comparing method,
    each written with nothing between its name and the ``!`` or ``.`` before it,
    the call unless every argument is a literal holding no word.
    """
    hits: list[Node] = []
    at = 0
    while at < len(tokens):
        spanned = _compared(file, tokens[at : at + _LONGEST])
        if spanned:
            hits.append(tokens[at].node)
        at += spanned or 1
    hits.extend(
        token.node
        for dot, token in enumerate(tokens)
        if token.text == "." and _compares_call(file, tokens, TokenAt(dot))
    )
    return hits
