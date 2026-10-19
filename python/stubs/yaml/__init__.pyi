# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Type stubs for PyYAML library.

Only covers the subset of PyYAML's API Aletheia uses: the yaml_loader module,
and the node tree the licence tools read to refuse a repeated key.
PyYAML is a third-party library that does not ship inline types.
"""

import re
from collections.abc import Callable
from typing import IO, ClassVar

def safe_load(stream: str | bytes | IO[str] | IO[bytes]) -> object: ...

# Returns the document as text when no stream is given, which is the only way
# it is called here: the C++ mutation lane writes a slice's configuration.
def safe_dump(data: object, *, sort_keys: bool = True) -> str: ...

class YAMLError(Exception):
    """Every error PyYAML raises for a document it cannot read."""

class Mark:
    """A position in the document, printed as its line, column and snippet."""

class MarkedYAMLError(YAMLError):
    """A ``YAMLError`` naming its problem and where in the document it lies."""

    def __init__(
        self,
        context: str | None = None,
        context_mark: Mark | None = None,
        problem: str | None = None,
        problem_mark: Mark | None = None,
        note: str | None = None,
    ) -> None: ...

class Node:
    """Subset of ``yaml.nodes.Node`` used by the number-tag constructor."""

    # ``scalar``, ``sequence`` or ``mapping``.
    id: ClassVar[str]
    tag: str
    value: object
    start_mark: Mark

class ScalarNode(Node):
    """A scalar node; ``value`` is the scalar's literal text."""

    value: str

class MappingNode(Node):
    """A mapping node; ``value`` is its key and value nodes, in document order."""

    value: list[tuple[Node, Node]]

class SequenceNode(Node):
    """A sequence node; ``value`` is its item nodes, in document order."""

    value: list[Node]

class SafeLoader:
    """Subset of ``yaml.SafeLoader`` used by the loader subclass that keeps numbers as text.

    ``yaml_implicit_resolvers`` maps a scalar's first character (or ``None``
    for the catch-all bucket) to the ``(tag, regexp)`` pairs that classify it;
    the subclass rebuilds this table without the int, float, bool and
    timestamp tags so a scalar stays its text, which the kernel reads.  ``add_constructor`` /
    ``construct_scalar`` support the constructor for an explicit ``!!int`` or
    ``!!float`` tag, which also keeps the text.
    """

    yaml_implicit_resolvers: ClassVar[dict[str | None, list[tuple[str, re.Pattern[str]]]]]
    def __init__(self, stream: str | bytes | IO[str] | IO[bytes]) -> None: ...
    def get_single_data(self) -> object: ...
    def get_single_node(self) -> Node | None: ...
    def dispose(self) -> None: ...
    @classmethod
    def add_constructor(
        cls, tag: str, constructor: Callable[[SafeLoader, Node], object]
    ) -> None: ...
    # The scalar's text; a node that is neither a scalar nor a mapping holding
    # a ``=`` key raises ``yaml.constructor.ConstructorError``.
    def construct_scalar(self, node: Node) -> str: ...
