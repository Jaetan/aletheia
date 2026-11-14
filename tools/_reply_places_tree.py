# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The syntax trees the reply-tags gate reads a binding's reader code through.

tree-sitter parses a file once into nodes, each of a kind its grammar names and
spanning a range of the file's bytes.  A binding's reader of
``tools/_reply_places.py`` asks the tree for the functions, calls, literals and
comparisons it reads; this module holds what every one of them asks alike: a
file parsed with its nodes listed by kind and its comments blanked for the code
a refusal shows, a top-level declaration found by name, the nodes under one in
source order, a node's text, lines, parts and edge token, a string literal
read from its parts through the binding's own escape reader, and each line
holding a node the grammar could not parse, which a reader reports rather than
reads past.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import TYPE_CHECKING, NewType

from tree_sitter import Parser

from tools._reply_places import WORD_SHAPE, LiteralText, read_text

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator
    from pathlib import Path

    from tree_sitter import Language, Node

# A file's source as the parser reads it: its UTF-8 bytes.
SourceBytes = NewType("SourceBytes", bytes)
# The index of a byte of a file's source, from 0.
SourceOffset = NewType("SourceOffset", int)
# The kind a grammar gives a node, such as ``call_expression``.
NodeKind = NewType("NodeKind", str)
# The text of a node or of a line, as the file writes it.
NodeText = NewType("NodeText", str)
# The number of a line of a file, from 1.
TreeLine = NewType("TreeLine", int)

# The kind every grammar gives an escape inside a string literal.
_ESCAPE = NodeKind("escape_sequence")
_NEWLINE = ord("\n")
_BLANK = ord(" ")


@dataclass(frozen=True, eq=False)
class SourceTree:
    """A file parsed once: its source, that source with each comment blanked, and its nodes.

    ``kinds`` lists the nodes of each kind in source order, ``broken`` each
    node the grammar could not parse or found missing, and ``comments`` are the
    kinds a comment has in the file's grammar.
    """

    path: Path
    source: SourceBytes
    shown: SourceBytes
    root: Node
    kinds: dict[NodeKind, list[Node]]
    broken: list[Node]
    comments: frozenset[NodeKind]

    def nodes(self, kind: NodeKind) -> list[Node]:
        """Return the file's nodes of ``kind``, in source order."""
        return self.kinds.get(kind, [])

    def text(self, node: Node) -> NodeText:
        """Return a node's text as the file writes it."""
        return NodeText(self.source[node.start_byte : node.end_byte].decode("utf-8"))

    def code(self, start: SourceOffset, end: SourceOffset) -> NodeText:
        """Return the code between two offsets, each comment blanked, as a refusal shows it."""
        return NodeText(self.shown[start:end].decode("utf-8").strip())

    def code_of(self, node: Node) -> NodeText:
        """Return a node's code, each comment blanked, as a refusal shows it."""
        return self.code(SourceOffset(node.start_byte), SourceOffset(node.end_byte))

    def line(self, line: TreeLine) -> NodeText:
        """Return a line of the file, each comment blanked, as a refusal shows it."""
        return NodeText(self.shown.split(b"\n")[line - 1].decode("utf-8").strip())

    def named(self, node: Node | None) -> list[Node]:
        """Return a node's named parts but its comments, none for no node."""
        if node is None:
            return []
        return [part for part in node.named_children if part.type not in self.comments]


def walk(node: Node) -> Iterator[Node]:
    """Yield ``node`` and every node under it, in source order."""
    stack = [node]
    while stack:
        current = stack.pop()
        yield current
        stack.extend(reversed(current.children))


def parse_source(
    language: Language, comments: frozenset[NodeKind], path: Path, text: NodeText
) -> SourceTree:
    """Return ``text``, the source of ``path``, parsed; ``comments`` are the kinds a comment has."""
    source = SourceBytes(text.encode("utf-8"))
    root = Parser(language).parse(source).root_node
    kinds: dict[NodeKind, list[Node]] = {}
    broken: list[Node] = []
    shown = bytearray(source)
    for node in walk(root):
        kinds.setdefault(NodeKind(node.type), []).append(node)
        if node.is_error or node.is_missing:
            broken.append(node)
        if node.type in comments:
            for at in range(node.start_byte, node.end_byte):
                if shown[at] != _NEWLINE:
                    shown[at] = _BLANK
    return SourceTree(path, source, SourceBytes(bytes(shown)), root, kinds, broken, comments)


def edge(node: Node, atoms: frozenset[NodeKind], *, last: bool) -> Node:
    """Return the atom or token a node's code opens with, or ends with when ``last``.

    An atom, such as a literal, is read whole rather than by its parts.  The
    grammars hang a comment between two tokens on the node holding both, so no
    node's code opens or ends with one.
    """
    while node.type not in atoms and node.children:
        node = node.children[-1 if last else 0]
    return node


def first_line(node: Node) -> TreeLine:
    """Return the line a node starts on."""
    return TreeLine(node.start_point.row + 1)


def node_lines(node: Node) -> range:
    """Return the lines a node spans."""
    return range(first_line(node), node.end_point.row + 2)


def child_of(node: Node | None, kind: NodeKind) -> Node | None:
    """Return a node's first part of ``kind``, or None."""
    if node is None:
        return None
    return next((part for part in node.children if part.type == kind), None)


def top_level(tree: SourceTree, kind: NodeKind, name: NodeText) -> Node | None:
    """Return the first declaration of ``kind`` at the top of the file named ``name``, or None."""
    for node in tree.root.named_children:
        named = node.child_by_field_name("name")
        if node.type == kind and named is not None and tree.text(named) == name:
            return node
    return None


def broken_lines(tree: SourceTree) -> list[TreeLine]:
    """Return each line holding a node the grammar could not parse, or a token it found missing."""
    return sorted({first_line(node) for node in tree.broken})


def literal_text(
    tree: SourceTree,
    literal: Node,
    content: frozenset[NodeKind],
    escape: Callable[[NodeText], LiteralText | None],
) -> LiteralText | None:
    """Return the text a string literal's parts read as, None when one reads as none.

    A part of a ``content`` kind reads as written and an escape as ``escape``
    reads it; any other named part, such as a span the grammar could not parse,
    reads as none.  The delimiters are the literal's unnamed parts.
    """
    parts: list[LiteralText | None] = []
    for part in literal.children:
        if part.type in content:
            parts.append(LiteralText(tree.text(part)))
        elif part.type == _ESCAPE:
            parts.append(escape(tree.text(part)))
        elif part.is_named:
            parts.append(None)
    return read_text(parts)


def holds_word(read: LiteralText | None) -> bool:
    """Say whether a literal's text, as read, is a word: identifier-shaped, or unreadable."""
    return read is None or re.fullmatch(WORD_SHAPE, read) is not None
