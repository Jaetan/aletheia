# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What the Go reader of the reply-tags arm reads Go's syntax with.

``tools/_reply_places_go.py`` reads each row through tree-sitter-go's syntax
tree of a file of the Go package.  This module holds what its readers share
about Go: the grammar and the kinds of node its comments, literals and names
have, a literal's text as the compiler reads its escapes, whether a literal
holds a word, the text of a string literal written with no escape, a name, a
top-level function, and the lines a node spans.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import tree_sitter_go
from tree_sitter import Language

from tools._reply_places import CodePoint, GoLine, GoSymbol, LiteralText, ReplyWord, scalar
from tools._reply_places_tree import (
    NodeKind,
    NodeText,
    SourceTree,
    first_line,
    holds_word,
    literal_text,
    node_lines,
    top_level,
    walk,
)

if TYPE_CHECKING:
    from tree_sitter import Node

# The Go grammar, and the kinds of node a comment, a literal and a name have.
GO_LANGUAGE = Language(tree_sitter_go.language())
GO_COMMENTS = frozenset({NodeKind("comment")})
_STRING = NodeKind("interpreted_string_literal")
_STRINGS = frozenset({_STRING, NodeKind("raw_string_literal")})
_RUNE = NodeKind("rune_literal")
GO_LITERALS = _STRINGS | {_RUNE}
_CONTENT = frozenset(
    {NodeKind("interpreted_string_literal_content"), NodeKind("raw_string_literal_content")}
)
GO_NAMES = frozenset(
    NodeKind(kind)
    for kind in ("identifier", "field_identifier", "type_identifier", "package_identifier")
)
_PARENTHESIZED = frozenset({NodeKind("parenthesized_expression"), NodeKind("parenthesized_type")})
# What each named escape reads as; the quote a string or a rune may not escape,
# the other's; the digits a byte or Unicode escape takes; the digits an octal
# escape takes and the greatest byte it may name.
_NAMED = dict(zip("abfnrtv\\'\"", "\a\b\f\n\r\t\v\\'\"", strict=True))
_FOREIGN_QUOTE = {'"': "'", "'": '"'}
_HEX_WIDTH = {"x": 2, "u": 4, "U": 8}
_HEX = frozenset("0123456789abcdefABCDEF")
_OCTAL = frozenset("01234567")
_OCTAL_WIDTH = 3
_MAX_BYTE = 0xFF


def _go_escape(escape: NodeText, quote: NodeText) -> LiteralText | None:
    """Return what an escape of a literal opened by ``quote`` reads as, None when Go reads none."""
    kind, digits = escape[1:2], escape[2:]
    if kind in _NAMED and not digits:
        return None if kind == _FOREIGN_QUOTE[quote] else LiteralText(_NAMED[kind])
    octal = escape[1:]
    if len(octal) == _OCTAL_WIDTH and set(octal) <= _OCTAL:
        return LiteralText(chr(int(octal, 8))) if int(octal, 8) <= _MAX_BYTE else None
    if kind in _HEX_WIDTH and len(digits) == _HEX_WIDTH[kind] and set(digits) <= _HEX:
        return scalar(CodePoint(int(digits, 16)))
    return None


def _go_rune(written: NodeText) -> LiteralText | None:
    """Return the character a rune's text between its quotes reads as, None when Go reads none."""
    if written.startswith("\\"):
        return _go_escape(written, NodeText("'"))
    return None if "\\" in written else LiteralText(written)


def go_read(tree: SourceTree, literal: Node) -> LiteralText | None:
    """Return the text a Go string or rune literal holds, as ``strconv.Unquote`` reads it.

    A raw string's is its text as written; None when an escape is none Go reads.
    """
    if literal.type == _RUNE:
        return _go_rune(NodeText(tree.text(literal)[1:-1]))
    return literal_text(tree, literal, _CONTENT, lambda escape: _go_escape(escape, NodeText('"')))


def is_word(tree: SourceTree, node: Node) -> bool:
    """Say whether a node is a string literal holding a word."""
    return node.type in _STRINGS and holds_word(go_read(tree, node))


def holds_no_word(tree: SourceTree, node: Node) -> bool:
    """Say whether a node is a string or rune literal holding no word."""
    return node.type in GO_LITERALS and not holds_word(go_read(tree, node))


def plain(tree: SourceTree, node: Node) -> ReplyWord | None:
    """Return the text of an interpreted string literal written with no escape, or None."""
    parts = node.named_children
    if node.type != _STRING or any(part.type not in _CONTENT for part in parts):
        return None
    return ReplyWord("".join(tree.text(part) for part in parts))


def plains(tree: SourceTree, nodes: list[Node]) -> frozenset[ReplyWord] | None:
    """Return the texts of string literals each written with no escape, or None when one is not."""
    words = [plain(tree, node) for node in nodes]
    return None if None in words else frozenset(word for word in words if word is not None)


def unwrapped(tree: SourceTree, node: Node | None) -> Node | None:
    """Return a node with the parentheses around it removed."""
    while node is not None and node.type in _PARENTHESIZED and len(tree.named(node)) == 1:
        node = tree.named(node)[0]
    return node


def is_name(tree: SourceTree, node: Node | None, name: GoSymbol) -> bool:
    """Say whether a node is a name spelled ``name``."""
    return node is not None and node.type in GO_NAMES and tree.text(node) == name


def mentions(tree: SourceTree, node: Node | None, name: GoSymbol) -> bool:
    """Say whether a name spelled ``name`` stands in a node."""
    return node is not None and any(is_name(tree, part, name) for part in walk(node))


def go_line(node: Node) -> GoLine:
    """Return the line a node starts on."""
    return GoLine(first_line(node))


def go_lines(node: Node) -> frozenset[GoLine]:
    """Return the lines a node spans."""
    return frozenset(map(GoLine, node_lines(node)))


def go_function(tree: SourceTree | None, name: GoSymbol) -> Node | None:
    """Return a top-level function, or None when there is no file or it does not define it."""
    return (
        None if tree is None else top_level(tree, NodeKind("function_declaration"), NodeText(name))
    )


def go_function_lines(tree: SourceTree | None, name: GoSymbol) -> frozenset[GoLine]:
    """Return the lines a top-level function spans, none when the file does not define it."""
    function = go_function(tree, name)
    return frozenset() if function is None else go_lines(function)
