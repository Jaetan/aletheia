"""Minimal type stubs for openpyxl.

Only covers the API surface used by Aletheia's excel_loader module.
"""

from pathlib import Path

from openpyxl.workbook import Workbook as Workbook

def load_workbook(
    filename: str | Path,
    *,
    read_only: bool = ...,
    keep_vba: bool = ...,
    data_only: bool = ...,
    keep_links: bool = ...,
) -> Workbook: ...
