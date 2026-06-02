"""Type stubs for openpyxl.worksheet.worksheet module."""

from collections.abc import Generator, Iterable
from typing import Literal, overload

from openpyxl.styles import Font

type _CellValue = str | int | float | bool | None

class Cell:
    value: _CellValue
    font: Font

class Worksheet:
    title: str
    def cell(self, row: int = ..., column: int = ..., value: _CellValue = ...) -> Cell: ...
    @overload
    def iter_rows(self, *, values_only: Literal[True]) -> Generator[tuple[_CellValue, ...]]: ...
    @overload
    def iter_rows(self, *, values_only: Literal[False] = ...) -> Generator[tuple[Cell, ...]]: ...
    def append(self, iterable: Iterable[object]) -> None: ...
    @overload
    def __getitem__(self, key: int) -> tuple[Cell, ...]: ...
    @overload
    def __getitem__(self, key: str) -> Cell: ...
