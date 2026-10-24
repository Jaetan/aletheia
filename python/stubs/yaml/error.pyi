# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The errors PyYAML raises, as ``yaml.error`` defines them; the package re-exports them."""

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
