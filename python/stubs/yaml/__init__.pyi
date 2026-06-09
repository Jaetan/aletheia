# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Type stubs for PyYAML library.

Only covers the subset of PyYAML API used by Aletheia's yaml_loader module.
PyYAML is a third-party library that does not ship inline types.
"""

from typing import IO

def safe_load(stream: str | bytes | IO[str] | IO[bytes]) -> object: ...
