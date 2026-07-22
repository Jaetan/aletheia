# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Runtime GHC RTS parameters — Python parity + containment behaviour.

Two concerns, one file (the Python leg of the K.1 runtime tier):

* **Parity** — reads ``docs/RESOURCE_BUDGETS.yaml`` (the cross-binding SSOT,
  itself enforced against every binding by ``tools/check_rts_runtime.py``) and
  asserts the Python mirror constants in ``aletheia.client._ffi`` match.  Clones
  the ``test_wire_codes_parity.py`` shape.

* **Containment-by-abort** — the heap cap is NOT a recoverable error: when it
  fires the process TERMINATES (a GHC HeapExhausted abort) so the host survives.
  A subprocess boots the real FFI client with the default cap and processes a
  workload (the correct path), and a second boots it under a tight
  ``ALETHEIA_RTS_OPTS=-M12M`` cap over a large DBC and must ABORT (non-zero exit,
  no success sentinel).  Both run out-of-process because the abort is
  process-terminating and the GHC RTS is one-shot per process.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml
from _yaml_shape import as_str_object_dict

from aletheia.client._ffi import (
    DEFAULT_RTS_CORES,
    DEFAULT_RTS_HEAP_CAP,
    RTS_INIT_SYMBOL,
    RTS_OVERRIDE_ENV,
    find_ffi_library,
)

_REPO_ROOT = Path(__file__).resolve().parents[2]
_YAML_PATH = _REPO_ROOT / "docs" / "RESOURCE_BUDGETS.yaml"

# The subprocess workload: boot the real FFI client and parse a VALID DBC of
# `argv[1]` messages.  A large count builds a live parse tree well past a tight
# -M cap, so the cap fires mid-parse (the process aborts); a small count fits any
# cap and completes.  The sentinel is printed only on a clean finish; a parse
# error (which a valid DBC never produces) exits 3, distinct from the abort.
_WORKLOAD = r"""
import sys
from aletheia import AletheiaClient

n = int(sys.argv[1])
lines = ['VERSION ""', "", "NS_ :", "", "BS_:", "", "BU_: ECU", ""]
for i in range(n):
    lines.append(f"BO_ {256 + i} Msg{i}: 8 ECU")
    lines.append(f' SG_ Sig{i} : 0|16@1+ (0.25,0) [0|8000] "u" ECU')
    lines.append("")
dbc = "\n".join(lines)
with AletheiaClient() as client:
    resp = client.parse_dbc_text(dbc)
    if isinstance(resp, dict) and resp.get("status") == "error":
        sys.exit(3)
print("ALETHEIA_RTS_OK")
"""

_SENTINEL = "ALETHEIA_RTS_OK"


def _runtime_block() -> dict[str, object]:
    """Load the ``runtime`` block of the RESOURCE_BUDGETS SSOT."""
    with _YAML_PATH.open("r", encoding="utf-8") as fh:
        raw: object = yaml.safe_load(fh)
    root = as_str_object_dict(raw, "RESOURCE_BUDGETS.yaml root")
    return as_str_object_dict(root["runtime"], "runtime")


def _skip_without_ffi() -> None:
    """Skip the calling test if libaletheia-ffi.so cannot be resolved."""
    try:
        find_ffi_library()
    except FileNotFoundError:
        pytest.skip("libaletheia-ffi.so not found — run 'cabal run shake -- build'")


def _run_workload(n: int, extra_env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    """Run the DBC-parse workload out-of-process with ``extra_env`` overlaid."""
    env = os.environ.copy()
    env.update(extra_env)
    return subprocess.run(
        [sys.executable, "-c", _WORKLOAD, str(n)],
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )


# ----- parity -----


def test_python_mirror_matches_ssot() -> None:
    """The Python mirror constants equal the RESOURCE_BUDGETS runtime block."""
    runtime = _runtime_block()
    heap_cap = as_str_object_dict(runtime["heap_cap"], "runtime.heap_cap")
    default_cores = as_str_object_dict(runtime["default_cores"], "runtime.default_cores")

    assert DEFAULT_RTS_HEAP_CAP.decode("ascii") == heap_cap["flag"]
    assert default_cores["value"] == DEFAULT_RTS_CORES
    assert runtime["init_symbol"] == RTS_INIT_SYMBOL
    assert heap_cap["override_env"] == RTS_OVERRIDE_ENV


def test_heap_cap_flag_matches_declared_bytes() -> None:
    """The SSOT's ``-M<n>G`` flag denotes exactly its ``bytes`` field.

    Ties the human-facing flag string to the numeric value the docs/gate cite,
    so the two cannot silently disagree.
    """
    heap_cap = as_str_object_dict(_runtime_block()["heap_cap"], "runtime.heap_cap")
    flag = heap_cap["flag"]
    assert isinstance(flag, str)
    assert flag.startswith("-M")
    assert flag.endswith("G")
    gib = int(flag[2:-1])
    assert gib * 1024 * 1024 * 1024 == heap_cap["bytes"]


# ----- containment behaviour -----


def test_default_cap_boots_and_processes() -> None:
    """The correct path (hs_init_with_rtsopts + -M3G) boots and processes a workload."""
    _skip_without_ffi()
    result = _run_workload(5, {})
    assert result.returncode == 0, result.stderr
    assert _SENTINEL in result.stdout


def test_tight_cap_aborts_the_process() -> None:
    """A tight cap over a large workload TERMINATES the process (containment-by-abort).

    The teeth of the whole feature: with ``ALETHEIA_RTS_OPTS=-M12M`` the parse of
    a large DBC exceeds the cap and GHC aborts the process — a non-zero exit with
    no success sentinel, never a recoverable error.
    """
    _skip_without_ffi()
    result = _run_workload(1000, {RTS_OVERRIDE_ENV: "-M12M"})
    assert result.returncode != 0, "the tight cap must abort the process"
    assert _SENTINEL not in result.stdout
    # Exit 3 is the workload's own parse-error path; a valid DBC never takes it,
    # so a non-zero, non-3 exit is the GHC heap abort (containment), not a masked
    # parse failure.
    assert result.returncode != 3, f"unexpected parse error, not a heap abort: {result.stderr}"
