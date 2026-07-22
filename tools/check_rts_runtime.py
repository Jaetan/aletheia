# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_rts_runtime.py — ``docs/RESOURCE_BUDGETS.yaml`` ↔ binding RTS-init parity gate.

Every binding loads the same ``libaletheia-ffi.so`` and starts the loaded
kernel's GHC RTS once per process.  ``docs/RESOURCE_BUDGETS.yaml`` (the
``runtime:`` block) is the cross-binding single source of truth for the runtime
RTS parameters they pass — the default heap cap, the default capability count,
and the init symbol — so the kernel runs under identical limits no matter which
language drove it.

The values are hand-mirrored, not read at runtime: a bundled binding cannot
read ``docs/`` (the dist bundle omits it) and a file-open + YAML-parse has no
business on the path of code whose job is to survive a runaway.  This gate is
the static enforcement of the mirror — it reads the SSOT and asserts each
binding's named mirror constant matches, in the spirit of
``tools/check_limits_parity.py`` (Limits SSOT ↔ Go/Python mirrors) and
``tools/check_wire_codes.py`` (wire-code SSOT ↔ per-binding vocabularies).

Pure source scanning (no Haskell / no build artefact), so the gate is complete
the moment the mirrors land.  Each binding declares four named constants that
this gate extracts by an exact-name regex:

* heap-cap flag   — the ``-M…`` string emitted into the RTS argv.
* default cores   — the capability count emitted as ``-N<k>`` only when a caller
                    requests more (so the default itself adds no ``-N``).
* init symbol     — ``hs_init_with_rtsopts`` (plain ``hs_init`` cannot carry the
                    ``-M`` cap under the ``.so``'s link-time RtsOptsSafeOnly).
* override env    — ``ALETHEIA_RTS_OPTS``, appended after the cap so a caller
                    ``-M`` wins.

The heap cap is a CONTAINMENT bound: when it fires the process TERMINATES (a GHC
HeapExhausted abort of the foreign-export wrapper) so the host survives — there
is no recoverable error.  See ``docs/RESOURCE_BUDGETS.yaml`` and
``docs/development/RESOURCE_PARAMETERS.md``.

Exit codes:
  0 — every binding's mirror matches the SSOT.
  1 — at least one binding mirror diverges (wrong value or missing constant).
  2 — could not check: missing / malformed SSOT, an absent ``runtime`` block or
      field, or a binding source file missing (a vacuous pass is refused).
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import cast

import yaml

from tools._common import emit

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_YAML_PATH = REPO_ROOT / "docs" / "RESOURCE_BUDGETS.yaml"

COULD_NOT_CHECK = 2


class RTSRuntimeError(Exception):
    """The inputs cannot be checked (missing file / malformed YAML / absent field)."""


@dataclass(frozen=True)
class RuntimeSSOT:
    """The mirrored runtime parameters read from the SSOT ``runtime`` block."""

    heap_cap_flag: str
    default_cores: int
    init_symbol: str
    override_env: str


@dataclass(frozen=True)
class BindingMirror:
    """One binding's source file and the four exact-name constant regexes.

    Each regex has a single capture group holding the mirrored value.  A group
    that fails to match is reported as a divergence (the mirror constant is
    missing or renamed), never a silent pass.
    """

    name: str
    path: Path
    heap_cap_re: re.Pattern[str]
    default_cores_re: re.Pattern[str]
    init_symbol_re: re.Pattern[str]
    override_env_re: re.Pattern[str]


# The four bindings' mirror surfaces.  Each constant is keyed on its EXACT name
# so a rename surfaces as a divergence rather than a wrong-but-parseable match.
BINDING_MIRRORS: tuple[BindingMirror, ...] = (
    BindingMirror(
        name="Python",
        path=REPO_ROOT / "python" / "aletheia" / "client" / "_ffi.py",
        heap_cap_re=re.compile(r'DEFAULT_RTS_HEAP_CAP\s*=\s*b"(-M[^"]+)"'),
        default_cores_re=re.compile(r"DEFAULT_RTS_CORES\s*=\s*(\d+)"),
        init_symbol_re=re.compile(r'RTS_INIT_SYMBOL\s*=\s*"([^"]+)"'),
        override_env_re=re.compile(r'RTS_OVERRIDE_ENV\s*=\s*"([^"]+)"'),
    ),
    BindingMirror(
        name="Go",
        path=REPO_ROOT / "go" / "aletheia" / "rts.go",
        heap_cap_re=re.compile(r'rtsHeapCapFlag\s*=\s*"(-M[^"]+)"'),
        default_cores_re=re.compile(r"rtsDefaultCores\s*=\s*(\d+)"),
        init_symbol_re=re.compile(r'rtsInitSymbol\s*=\s*"([^"]+)"'),
        override_env_re=re.compile(r'rtsOverrideEnv\s*=\s*"([^"]+)"'),
    ),
    BindingMirror(
        name="C++",
        path=REPO_ROOT / "cpp" / "src" / "detail" / "rts_params.hpp",
        heap_cap_re=re.compile(r'rts_heap_cap_flag\s*=\s*"(-M[^"]+)"'),
        default_cores_re=re.compile(r"rts_default_cores\s*=\s*(\d+)"),
        init_symbol_re=re.compile(r'rts_init_symbol\s*=\s*"([^"]+)"'),
        override_env_re=re.compile(r'rts_override_env\s*=\s*"([^"]+)"'),
    ),
    BindingMirror(
        name="Rust",
        path=REPO_ROOT / "rust" / "src" / "backend.rs",
        heap_cap_re=re.compile(r'RTS_HEAP_CAP_FLAG:\s*&str\s*=\s*"(-M[^"]+)"'),
        default_cores_re=re.compile(r"RTS_DEFAULT_CORES:\s*u32\s*=\s*(\d+)"),
        init_symbol_re=re.compile(r'RTS_INIT_SYMBOL:\s*&str\s*=\s*"([^"]+)"'),
        override_env_re=re.compile(r'RTS_OVERRIDE_ENV:\s*&str\s*=\s*"([^"]+)"'),
    ),
)


def load_runtime_ssot(yaml_path: Path) -> RuntimeSSOT:
    """Load and shape-check the SSOT ``runtime`` block, or raise ``RTSRuntimeError``.

    A missing file, a malformed root, an absent ``runtime`` block, or any
    missing/mistyped field is the could-not-check class (exit 2) — never a
    hollow pass.  The sibling ``build`` block is intentionally not read here (it
    does not exist this stage).
    """
    if not yaml_path.is_file():
        message = f"SSOT not found: {yaml_path}"
        raise RTSRuntimeError(message)
    raw: object = yaml.safe_load(yaml_path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        message = f"{yaml_path}: root must be a mapping"
        raise RTSRuntimeError(message)
    root = cast("dict[object, object]", raw)
    runtime_raw = root.get("runtime")
    if not isinstance(runtime_raw, dict):
        message = f"{yaml_path}: missing or malformed 'runtime' block"
        raise RTSRuntimeError(message)
    runtime = cast("dict[object, object]", runtime_raw)

    heap_cap_raw = runtime.get("heap_cap")
    if not isinstance(heap_cap_raw, dict):
        message = f"{yaml_path}: runtime.heap_cap must be a mapping"
        raise RTSRuntimeError(message)
    heap_cap = cast("dict[object, object]", heap_cap_raw)
    default_cores_raw = runtime.get("default_cores")
    if not isinstance(default_cores_raw, dict):
        message = f"{yaml_path}: runtime.default_cores must be a mapping"
        raise RTSRuntimeError(message)
    default_cores = cast("dict[object, object]", default_cores_raw)

    flag = heap_cap.get("flag")
    override_env = heap_cap.get("override_env")
    cores_value = default_cores.get("value")
    init_symbol = runtime.get("init_symbol")

    if not isinstance(flag, str) or not flag:
        message = f"{yaml_path}: runtime.heap_cap.flag must be a non-empty string"
        raise RTSRuntimeError(message)
    if not isinstance(override_env, str) or not override_env:
        message = f"{yaml_path}: runtime.heap_cap.override_env must be a non-empty string"
        raise RTSRuntimeError(message)
    # `bool` is an `int` subclass; reject it so `value: true` cannot pass as 1.
    if not isinstance(cores_value, int) or isinstance(cores_value, bool):
        message = f"{yaml_path}: runtime.default_cores.value must be an integer"
        raise RTSRuntimeError(message)
    if not isinstance(init_symbol, str) or not init_symbol:
        message = f"{yaml_path}: runtime.init_symbol must be a non-empty string"
        raise RTSRuntimeError(message)

    return RuntimeSSOT(
        heap_cap_flag=flag,
        default_cores=cores_value,
        init_symbol=init_symbol,
        override_env=override_env,
    )


def _extract(pattern: re.Pattern[str], text: str) -> str | None:
    """Return the first capture group of ``pattern`` in ``text``, or None."""
    match = pattern.search(text)
    return match.group(1) if match else None


def check_binding(mirror: BindingMirror, ssot: RuntimeSSOT) -> list[str]:
    """Return the divergences between one binding's mirror and the SSOT.

    A missing source file is could-not-check (raised); a missing constant or a
    mismatched value is a divergence (returned), so the gate fails rather than
    passing vacuously over a mirror that has been deleted or renamed.
    """
    if not mirror.path.is_file():
        message = f"{mirror.name} mirror source not found: {mirror.path}"
        raise RTSRuntimeError(message)
    text = mirror.path.read_text(encoding="utf-8")
    rel = mirror.path.relative_to(REPO_ROOT)

    diffs: list[str] = []

    heap = _extract(mirror.heap_cap_re, text)
    if heap is None:
        diffs.append(f"{mirror.name}: no heap-cap mirror constant found in {rel}")
    elif heap != ssot.heap_cap_flag:
        diffs.append(
            f"{mirror.name} heap cap: mirror='{heap}' vs SSOT='{ssot.heap_cap_flag}' ({rel})"
        )

    cores = _extract(mirror.default_cores_re, text)
    if cores is None:
        diffs.append(f"{mirror.name}: no default-cores mirror constant found in {rel}")
    elif int(cores) != ssot.default_cores:
        diffs.append(
            f"{mirror.name} default cores: mirror={cores} vs SSOT={ssot.default_cores} ({rel})"
        )

    init = _extract(mirror.init_symbol_re, text)
    if init is None:
        diffs.append(f"{mirror.name}: no init-symbol mirror constant found in {rel}")
    elif init != ssot.init_symbol:
        diffs.append(
            f"{mirror.name} init symbol: mirror='{init}' vs SSOT='{ssot.init_symbol}' ({rel})"
        )

    env = _extract(mirror.override_env_re, text)
    if env is None:
        diffs.append(f"{mirror.name}: no override-env mirror constant found in {rel}")
    elif env != ssot.override_env:
        diffs.append(
            f"{mirror.name} override env: mirror='{env}' vs SSOT='{ssot.override_env}' ({rel})"
        )

    return diffs


def main() -> int:
    """Check every binding's RTS-init mirror against the RESOURCE_BUDGETS SSOT."""
    try:
        ssot = load_runtime_ssot(DEFAULT_YAML_PATH)
        diffs: list[str] = []
        for mirror in BINDING_MIRRORS:
            diffs.extend(check_binding(mirror, ssot))
    except RTSRuntimeError as exc:
        _ = sys.stderr.write(f"check-rts-runtime: COULD NOT CHECK — {exc}\n")
        return COULD_NOT_CHECK

    if diffs:
        _ = sys.stderr.write("check-rts-runtime: divergences detected\n\n")
        for diff in diffs:
            _ = sys.stderr.write(f"  - {diff}\n")
        _ = sys.stderr.write(
            f"\nfound {len(diffs)} divergence(s) between docs/RESOURCE_BUDGETS.yaml "
            + "(SSOT) and the binding RTS-init mirrors.  Reconcile by updating the "
            + "binding mirror or the SSOT (per the SSOT header's change protocol).\n"
        )
        return 1

    emit(
        f"check-rts-runtime: {len(BINDING_MIRRORS)} bindings mirror "
        + f"heap_cap={ssot.heap_cap_flag} default_cores={ssot.default_cores} "
        + f"init_symbol={ssot.init_symbol} — all in parity with docs/RESOURCE_BUDGETS.yaml"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
