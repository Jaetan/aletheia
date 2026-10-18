# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Test stand-ins: a tool's fake on the search path, and the stand-in kernels the build makes."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NewType

if TYPE_CHECKING:
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


# A stand-in kernel's name, the stem of its source under haskell-shim/test.
StandInName = NewType("StandInName", str)

_REPO = Path(__file__).resolve().parents[2]


def stand_in_kernel(name: StandInName) -> Path:
    """Return the stand-in kernel the build makes beside the library the tests run against.

    ``cabal run shake -- build`` makes each one in the directory ``ALETHEIA_LIB``
    names, or the repository's ``build/``.
    """
    lib = os.environ.get("ALETHEIA_LIB")
    built = Path(lib).parent if lib else _REPO / "build"
    path = built / "stand-ins" / f"{name}.so"
    assert path.exists(), f"stand-in {path} not built; run 'cabal run shake -- build'"
    return path
