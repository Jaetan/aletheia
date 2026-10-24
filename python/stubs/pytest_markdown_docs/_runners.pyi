# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
import abc
from collections.abc import Callable

from pytest_markdown_docs.definitions import FenceTestDefinition

class _Runner(abc.ABC):
    @abc.abstractmethod
    def runtest(self, test: FenceTestDefinition, args: dict[str, object]) -> None: ...

def register_runner[R: type[_Runner]](*, default: bool = False) -> Callable[[R], R]: ...

class DefaultRunner(_Runner):
    # The item passes pytest-asyncio's runner when that plugin is installed, and the
    # harness does not install it.
    def runtest(
        self,
        test: FenceTestDefinition,
        args: dict[str, object],
        *,
        asyncio_runner: None = None,
    ) -> None: ...
