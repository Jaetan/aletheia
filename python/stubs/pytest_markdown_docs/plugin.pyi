# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
import pathlib
from collections.abc import Generator
from enum import Enum
from typing import Self

import pytest
from markdown_it import MarkdownIt
from pytest_markdown_docs.definitions import FenceTestDefinition

class FenceSyntax(Enum):
    default = "default"
    superfences = "superfences"

class MarkdownInlinePythonItem(pytest.Item):
    test_definition: FenceTestDefinition
    start_line: int
    fixture_request: pytest.FixtureRequest
    @classmethod
    def from_parent(
        cls, parent: pytest.Collector, *, name: str, test_definition: FenceTestDefinition
    ) -> Self: ...

class MarkdownDocstringCodeModule(pytest.Module):
    def collect(self) -> Generator[MarkdownInlinePythonItem]: ...

def extract_fence_tests(
    markdown_it_parser: MarkdownIt,
    markdown_string: str,
    start_line_offset: int,
    source_path: pathlib.Path,
    markdown_type: str = "md",
    fence_syntax: FenceSyntax = ...,
) -> Generator[FenceTestDefinition]: ...
