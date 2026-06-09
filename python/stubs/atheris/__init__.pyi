# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Type stubs for the atheris coverage-guided fuzzing library.

Only covers the subset of the atheris API used by Aletheia's fuzz
harnesses under ``tests/fuzz/``.  Atheris is an opt-in fuzz extra
(``aletheia[fuzz]``) and ships no type information of its own, so the
strict ``basedpyright`` gate needs this stub to resolve member access on
the ``atheris`` module.  Member names are PascalCase to match atheris's
C++-derived public API.
"""

from collections.abc import Callable, Sequence
from contextlib import AbstractContextManager

class FuzzedDataProvider:
    """Maps the fuzzer's raw byte stream to typed values deterministically."""

    def __init__(self, data: bytes) -> None: ...
    def ConsumeBytes(self, count: int) -> bytes: ...
    def ConsumeUnicodeNoSurrogates(self, count: int) -> str: ...

def instrument_imports(
    include: Sequence[str] = ...,
    exclude: Sequence[str] = ...,
) -> AbstractContextManager[None]: ...
def Setup(args: Sequence[str], test_one_input: Callable[[bytes], None]) -> list[str]: ...
def Fuzz() -> None: ...
