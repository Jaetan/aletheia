# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Aletheia developer tooling (CI gates, dead-import detection, warm-process checks).

A package so modules can import siblings explicitly (`from tools.X import ...`);
the warm tools are invoked as `python -m tools.warm_check_properties` etc.

The tools share their common types with the library (`aletheia.common_types`).
The project's virtual environment installs the library; the pre-commit hook's
bare interpreter does not, so the library's source is appended to the path,
where an installed copy is found first and this one only when there is none.
"""

import sys
from pathlib import Path

_LIBRARY_SOURCE = str(Path(__file__).resolve().parent.parent / "python")
if _LIBRARY_SOURCE not in sys.path:
    sys.path.append(_LIBRARY_SOURCE)
