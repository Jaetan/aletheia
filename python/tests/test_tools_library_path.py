# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The tooling finds the library's common types under an interpreter that never installed it.

The pre-commit hook runs the fast tier under a bare interpreter, where only
``tools/__init__.py`` puts the library's source on the path.  The interpreter
running the tests is started with ``-S``, so no site directory, and so no
installed copy of the library, is on its path; the control shows the library
is not found there without ``tools``.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]


def test_the_bare_interpreter_imports_the_common_types_through_tools() -> None:
    """Importing the tools package is enough to reach the library's source."""
    code = "import tools, aletheia.common_types as shared; print(shared.__file__)"
    run = subprocess.run(
        [sys.executable, "-S", "-c", code], cwd=REPO, capture_output=True, text=True, check=False
    )
    assert run.returncode == 0, run.stderr
    assert Path(run.stdout.strip()) == REPO / "python" / "aletheia" / "common_types.py"


def test_without_tools_the_bare_interpreter_does_not_find_the_library() -> None:
    """The control: the path the first test relies on is the one the tools package adds."""
    run = subprocess.run(
        [sys.executable, "-S", "-c", "import aletheia"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=False,
    )
    assert run.returncode != 0
    assert "No module named 'aletheia'" in run.stderr
