# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Gate: every example script (top-level ``examples/`` + ``examples/demo/``) runs end-to-end.

The examples are the user-facing "proper usage" scripts. Because nothing executed
them, they drift silently — ``demo.py`` / ``demo_ltl_bug.py`` once subscripted an
integer violation ``timestamp`` as a rational dict; the flagship
``examples/simple_verification.py`` shipped a bare float the float principle now
rejects (it was ungated because an earlier glob covered only ``demo/``). This
gate runs each script as a subprocess from its OWN directory, so sibling imports
(``drive_log`` / ``engine_ecu_sim``) resolve and each script's own
``AletheiaClient`` brings up the GHC runtime the loaders' decimal parser needs.
A script that crashes — stale API, missing fixture, a float where an exact
``Fraction`` is required — fails here instead of in a user's hands.

Runs against the real ``libaletheia-ffi.so``; ``ALETHEIA_LIB`` is resolved the
same way the binding resolves it (:func:`find_ffi_library`) and passed through to
each subprocess.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from aletheia.client._ffi import find_ffi_library

_EXAMPLES_DIR = Path(__file__).resolve().parents[2] / "examples"
_DEMO_DIR = _EXAMPLES_DIR / "demo"
# Every runnable example: the top-level flagship (simple_verification.py) plus
# every script under demo/.  A top-level example is NOT under demo/, so a
# demo-only glob left the documented first-run example ungated.
_SCRIPTS = sorted(
    [*_EXAMPLES_DIR.glob("*.py"), *_DEMO_DIR.glob("*.py")],
    key=lambda p: p.relative_to(_EXAMPLES_DIR).as_posix(),
)
_SCRIPT_IDS = [p.relative_to(_EXAMPLES_DIR).as_posix() for p in _SCRIPTS]


def _examples_state() -> dict[Path, os.stat_result]:
    """Every file under ``examples/`` with its stat, taken either side of a script run."""
    return {path: path.stat() for path in _EXAMPLES_DIR.rglob("*") if path.is_file()}


def test_demo_dir_is_populated() -> None:
    """Guard against the glob silently matching nothing (a vacuous gate)."""
    assert _SCRIPTS, f"no example scripts found under {_EXAMPLES_DIR}"


@pytest.mark.parametrize("script", _SCRIPTS, ids=_SCRIPT_IDS)
def test_demo_script_runs(script: Path) -> None:
    """Each example exits 0 against the built ``.so`` and writes nothing under ``examples/``."""
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(find_ffi_library())
    # The sibling imports would otherwise write bytecode into examples/demo/__pycache__.
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    before = _examples_state()
    result = subprocess.run(
        [sys.executable, script.name],
        cwd=script.parent,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, (
        f"example {script.name!r} exited {result.returncode}\n"
        f"--- stdout (tail) ---\n{result.stdout[-2000:]}\n"
        f"--- stderr (tail) ---\n{result.stderr[-2000:]}"
    )
    # A run that rewrites a tracked fixture, even with the same bytes, moves its mtime.
    after = _examples_state()
    written = sorted(
        path.relative_to(_EXAMPLES_DIR).as_posix()
        for path in before.keys() | after.keys()
        if path not in before
        or path not in after
        or before[path].st_mtime_ns != after[path].st_mtime_ns
    )
    assert not written, f"example {script.name!r} wrote under examples/: {written}"
    # Guard the vacuous-gate class: a demo that swallows a failure and still exits
    # 0.  returncode alone let a demo print "0/4 tests passed" (after catching the
    # exception) and pass.  Scan stdout AND stderr (a demo may print to either),
    # and require EVERY self-test summary to be passing (a demo may print more than
    # one).  Two convention-stable markers across the demos:
    #   * a swallowed-exception line ("<name>: ERROR — <exc>"), and
    #   * every "N/M tests passed" summary must have N == M.
    combined = f"{result.stdout}\n{result.stderr}"
    assert "ERROR —" not in combined, (
        f"example {script.name!r} swallowed an error "
        f"(exited 0 but printed 'ERROR —'):\n{combined[-2000:]}"
    )
    summaries = re.findall(r"(\d+)/(\d+) tests passed", combined)
    failed = [m for m in summaries if m[0] != m[1]]
    assert not failed, (
        f"example {script.name!r} self-test reported failures {failed} "
        f"(all summaries: {summaries}):\n{combined[-2000:]}"
    )
    # A script may declare its OWN semantic failure yet still exit 0 — e.g. the
    # four-tier equivalence proof printing "MISMATCH DETECTED", or an equivalence
    # section printing "Identical: False".  returncode alone would let that broken
    # parity claim ship; forbid the self-declared-failure markers too.  These two
    # strings are RESERVED as failure markers — a demo must not emit them except
    # to signal a genuine failure (print a contrast some other way).
    for marker in ("MISMATCH DETECTED", "Identical: False"):
        assert marker not in combined, (
            f"example {script.name!r} printed {marker!r} but exited 0:\n{combined[-2000:]}"
        )


def test_drive_log_refuses_a_drifted_fixture(tmp_path: Path) -> None:
    """``drive_log.py`` exits 1 on a ``drive.log`` its generators do not make, leaving it intact."""
    _ = shutil.copy(_DEMO_DIR / "drive_log.py", tmp_path)
    fixture = tmp_path / "drive.log"
    drifted = (_DEMO_DIR / "drive.log").read_bytes() + b"\n"
    _ = fixture.write_bytes(drifted)
    result = subprocess.run(
        [sys.executable, "drive_log.py"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 1, f"drift read as a match:\n{result.stdout}{result.stderr}"
    assert "--update" in result.stderr
    assert fixture.read_bytes() == drifted


def test_drive_log_update_rewrites_the_fixture(tmp_path: Path) -> None:
    """``drive_log.py --update`` writes the tracked ``drive.log``'s bytes over a drifted copy."""
    _ = shutil.copy(_DEMO_DIR / "drive_log.py", tmp_path)
    fixture = tmp_path / "drive.log"
    _ = fixture.write_bytes(b"")
    result = subprocess.run(
        [sys.executable, "drive_log.py", "--update"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, f"--update failed:\n{result.stdout}{result.stderr}"
    assert fixture.read_bytes() == (_DEMO_DIR / "drive.log").read_bytes()
