# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_shim_builds_no_kernel_value`` — the Haskell shim builds no kernel value.

The patterns the shim reads results with (a case alternative, a lambda, a
function clause, a nested pattern) pass; an application in each position the
shim has used one (after ``$``, as an argument, as a point-free definition, on
a continuation line, before a ``where``) fails; comments are ignored; an empty
tree and a tree naming no generated constructor exit 2.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tools.check_shim_builds_no_kernel_value import HaskellSource, constructions, run

PATTERNS: list[HaskellSource] = [
    HaskellSource(t)
    for t in (
        "    case r of\n      AgdaSum.C_inj'8321'_38 errAny -> fail errAny\n",
        "dispatch (AgdaSum.C_inj'8322'_42 vecAny) out = do\n",
        "go n (AgdaVec.C__'8759'__38 x xs) ptr = do\n",
        "    go n AgdaVec.C_'91''93'_32 _ = return n\n",
        "  f = \\(AgdaSum.C_inj'8321'_38 e) -> e\n",
    )
]

APPLICATIONS: list[HaskellSource] = [
    HaskellSource(t)
    for t in (
        "        then Right $ AgdaFrame.C_Extended_16 (toInteger canId)\n",
        "mkAgdaDLC = AgdaDLC.C_mkDLC_28\n",
        "    k = AgdaBatch.d_code_160 AgdaBatch.C_ValueExceedsWireRange_148\n",
        "    let tf = g\n            (AgdaTime.C_mkTs_26 (toInteger ts))\n",
        '  run (AgdaTrace.C_Error_38 t)\n  where\n    ctx = "x"\n',
    )
]


@pytest.mark.parametrize("text", PATTERNS)
def test_pattern_passes(text: HaskellSource) -> None:
    """Pattern passes."""
    assert not constructions(Path("x.hs"), text)


@pytest.mark.parametrize("text", APPLICATIONS)
def test_application_fails(text: HaskellSource) -> None:
    """Application fails."""
    assert len(constructions(Path("x.hs"), text)) == 1


def test_comment_is_ignored() -> None:
    """Comment is ignored."""
    text = HaskellSource("-- built with AgdaRational.C_mkℚ_24\n{- and AgdaVec.C_'91''93'_32 -}\n")
    assert not constructions(Path("x.hs"), text)


def test_run_exit_codes(tmp_path: Path) -> None:
    """Run exit codes."""
    assert run(tmp_path) == 2
    source = tmp_path / "A.hs"
    _ = source.write_text("main = pure ()\n", encoding="utf-8")
    assert run(tmp_path) == 2
    _ = source.write_text(PATTERNS[0], encoding="utf-8")
    assert run(tmp_path) == 0
    _ = source.write_text(PATTERNS[0] + APPLICATIONS[0], encoding="utf-8")
    assert run(tmp_path) == 1
