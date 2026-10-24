# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
import pathlib
from collections.abc import Sequence
from dataclasses import dataclass

@dataclass(frozen=True)
class FenceTestDefinition:
    source: str
    fixture_names: Sequence[str]
    start_line: int
    source_path: pathlib.Path
    runner_name: str | None
    max_retries: int = 0
