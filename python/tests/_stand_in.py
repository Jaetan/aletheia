# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A tool's stand-in for the tests that drive a lane against a fake of its tool."""

from __future__ import annotations

import os
import sys
from typing import TYPE_CHECKING, NewType

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

# A tool's name, as the lane looks it up on the search path.
ToolName = NewType("ToolName", str)

# A Python script's source, run by the test's own interpreter.
ScriptSource = NewType("ScriptSource", str)


def install_stand_in(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, name: ToolName, source: ScriptSource
) -> None:
    """Put an executable script named ``name`` first on the search path, run by this interpreter."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    tool = bin_dir / name
    _ = tool.write_text(f"#!{sys.executable}\n{source}", encoding="utf-8")
    tool.chmod(0o755)
    monkeypatch.setenv("PATH", f"{bin_dir}:{os.environ['PATH']}")
