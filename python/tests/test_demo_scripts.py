# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Gate: every example demo under ``examples/demo/`` runs end-to-end.

The demos are the user-facing "proper usage" examples. Because nothing executed
them, two drifted silently — ``demo.py`` / ``demo_ltl_bug.py`` subscripted an
integer violation ``timestamp`` as a rational dict — and the float-principle
decimal-SSOT changes would have broken them invisibly too. This gate runs each demo as a
subprocess (``python examples/demo/<name>.py``) from that directory so sibling
imports (``drive_log`` / ``engine_ecu_sim``) resolve and each demo's own
``AletheiaClient`` brings up the GHC runtime the loaders' decimal parser needs.
A demo that crashes — stale API, missing fixture, a float where an exact
``Fraction`` is required — fails here instead of in a user's hands.

Runs against the real ``libaletheia-ffi.so``; ``ALETHEIA_LIB`` is resolved the
same way the binding resolves it (:func:`find_ffi_library`) and passed through to
each subprocess.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

from aletheia.client._ffi import find_ffi_library

_DEMO_DIR = Path(__file__).resolve().parents[2] / "examples" / "demo"
_DEMOS = sorted(p.name for p in _DEMO_DIR.glob("*.py"))


def test_demo_dir_is_populated() -> None:
    """Guard against the glob silently matching nothing (a vacuous gate)."""
    assert _DEMOS, f"no demo scripts found under {_DEMO_DIR}"


@pytest.mark.parametrize("script", _DEMOS)
def test_demo_script_runs(script: str) -> None:
    """Each example demo executes cleanly (exit 0) against the built ``.so``."""
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(find_ffi_library())
    result = subprocess.run(
        [sys.executable, script],
        cwd=_DEMO_DIR,
        env=env,
        capture_output=True,
        text=True,
        timeout=180,
        check=False,
    )
    assert result.returncode == 0, (
        f"demo {script!r} exited {result.returncode}\n"
        f"--- stdout (tail) ---\n{result.stdout[-2000:]}\n"
        f"--- stderr (tail) ---\n{result.stderr[-2000:]}"
    )
    # Guard the vacuous-gate class: a demo that swallows a failure and still exits
    # 0.  returncode alone let a demo print "0/4 tests passed" (after catching the
    # exception) and pass.  Two convention-stable markers across the demos:
    #   * a swallowed-exception line ("<name>: ERROR — <exc>"), and
    #   * a self-test summary "N/M tests passed" whose N != M.
    assert "ERROR —" not in result.stdout, (
        f"demo {script!r} swallowed an error (exited 0 but printed 'ERROR —'):\n"
        f"{result.stdout[-2000:]}"
    )
    self_test = re.search(r"(\d+)/(\d+) tests passed", result.stdout)
    assert self_test is None or self_test[1] == self_test[2], (
        f"demo {script!r} self-test failed ({self_test[0]}):\n{result.stdout[-2000:]}"
    )
