# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The repository's root, for the tests that read the tree above ``python/``.

The mutation lane runs the suite from mutmut's copy under ``python/mutants/``,
where a test file's own ancestors stop one level short of the root, so the
lane names the root in ``ALETHEIA_REPO_ROOT``, as the Go lane and the C++
tests' environment name it; anywhere else it is two levels above ``tests/``.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(os.environ.get("ALETHEIA_REPO_ROOT") or Path(__file__).resolve().parents[2])
