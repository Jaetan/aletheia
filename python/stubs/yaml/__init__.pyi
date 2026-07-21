# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Type stubs for PyYAML library.

Only covers the subset of PyYAML API used by Aletheia's yaml_loader module.
PyYAML is a third-party library that does not ship inline types.
"""

import re
from collections.abc import Callable
from typing import IO, ClassVar

def safe_load(stream: str | bytes | IO[str] | IO[bytes]) -> object: ...

class Node:
    """Subset of ``yaml.nodes.Node`` used by the float-tag constructor."""

    tag: str
    value: object

class ScalarNode(Node):
    """A scalar node; ``value`` is the scalar's literal text."""

    value: str

class SafeLoader:
    """Subset of ``yaml.SafeLoader`` used by the no-float loader subclass.

    ``yaml_implicit_resolvers`` maps a scalar's first character (or ``None``
    for the catch-all bucket) to the ``(tag, regexp)`` pairs that classify it;
    the no-float loader rebuilds this table without the float tag so a decimal
    scalar stays a string (the float principle).  ``add_constructor`` /
    ``construct_yaml_float`` support the explicit ``!!float``-tag constructor
    layered on top of that table.
    """

    yaml_implicit_resolvers: ClassVar[dict[str | None, list[tuple[str, re.Pattern[str]]]]]
    def __init__(self, stream: str | bytes | IO[str] | IO[bytes]) -> None: ...
    def get_single_data(self) -> object: ...
    def dispose(self) -> None: ...
    @classmethod
    def add_constructor(
        cls, tag: str, constructor: Callable[[SafeLoader, Node], object]
    ) -> None: ...
    def construct_yaml_float(self, node: Node) -> float: ...
