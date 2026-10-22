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

Runs against the real ``libaletheia-ffi.so`` through the forwarding stand-in
kernel, which hands every call to the library resolved the way the binding
resolves it (:func:`find_ffi_library`) and logs every refusal it answers. A
script exiting 0 can still have discarded a refused call, so each run's
refusals are held to the codes ``_STATED_REFUSALS`` names for the script, none
for a script it does not name.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from _stand_in import StandInName, stand_in_kernel

from aletheia.client._ffi import find_ffi_library
from aletheia.codes import ErrorCode

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

# The refusals an example shows on purpose, in the order the kernel answers them.
_STATED_REFUSALS: dict[Path, list[ErrorCode]] = {
    # Its hard-error DBC, overlapping signals, refused at load.
    _DEMO_DIR / "dbc_validation.py": [ErrorCode.HANDLER_VALIDATION_FAILED],
}

# Why every example runs as a user runs it.
_RUNS_AS_A_PROGRAM = (
    "each example runs as a user runs it, as a program from its own directory, so its"
    + " own exit status and output streams, with the runtime it starts once in a fresh"
    + " interpreter, are the claim"
)


def _examples_state() -> dict[Path, os.stat_result]:
    """Every file under ``examples/`` with its stat, taken either side of a script run."""
    return {path: path.stat() for path in _EXAMPLES_DIR.rglob("*") if path.is_file()}


def test_demo_dir_is_populated() -> None:
    """Guard against the glob silently matching nothing (a vacuous gate)."""
    assert _SCRIPTS, f"no example scripts found under {_EXAMPLES_DIR}"


@pytest.mark.parametrize("script", _SCRIPTS, ids=_SCRIPT_IDS)
@pytest.mark.process(_RUNS_AS_A_PROGRAM)
def test_demo_script_runs(script: Path, tmp_path: Path) -> None:
    """Each example exits 0, is refused only what it states, and writes nothing in examples/."""
    refusals = tmp_path / "refusals.log"
    env = dict(os.environ)
    env["ALETHEIA_FORWARD_TO"] = str(find_ffi_library())
    env["ALETHEIA_LIB"] = str(stand_in_kernel(StandInName("forwarding_kernel")))
    env["ALETHEIA_REFUSAL_LOG"] = str(refusals)
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
    # A line of the log is the refusing entry, a tab and the kernel's envelope.
    envelopes = [
        line.split("\t", 1)[1]
        for line in (refusals.read_text(encoding="utf-8") if refusals.exists() else "").splitlines()
    ]
    refused = [ErrorCode(json.loads(envelope)["code"]) for envelope in envelopes]
    assert refused == _STATED_REFUSALS.get(script, []), (
        f"example {script.name!r} was refused other than it states:\n" + "\n".join(envelopes)
    )
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


@pytest.mark.process(
    "the script runs as a user runs it, as a program, and its refusal is that program's"
    + " own exit status and error stream, set from the message the script exits with"
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


@pytest.mark.process(_RUNS_AS_A_PROGRAM)
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
