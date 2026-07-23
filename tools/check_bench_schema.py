# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Cross-binding benchmark-schema conformance gate.

Enforces the "same measurement, same name, every API language" rule: every
benchmark harness (Python / C++ / Go / Rust) must emit JSON matching
``benchmarks/SCHEMA.yaml`` for each mode -- identical CLI flags, ``results``
container, per-row key sets, and byte-identical human labels in the same order.

The gate drives each binding with a TINY workload per mode (the schema is
workload-independent) so it runs in seconds, and validates STRUCTURE ONLY --
never the measured values, which are host-dependent.

Binding availability:
  * Python is REQUIRED (the schema reference; always present via python/.venv).
    Its absence is a hard failure, so the gate is never vacuous.
  * C++ / Go / Rust are checked when their built binary is present, and
    skipped-with-notice otherwise (mirrors tools/mutation_run.py's per-tool
    skip). CI builds all four, so the full-teeth check runs there.

Usage:
    python3 tools/check_bench_schema.py             # check available bindings
    python3 tools/check_bench_schema.py --self-test  # prove the gate has teeth
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple, cast

import yaml

REPO = Path(__file__).resolve().parent.parent
SCHEMA_PATH = REPO / "benchmarks" / "SCHEMA.yaml"

# Per-mode tiny workloads -- enough to emit one row per lane/sweep, fast to run.
# Every CLI flag the SCHEMA pins for a mode is passed here (``--warmup 0`` keeps
# the workload tiny while still exercising the flag), so a binding that drops or
# renames a flag fails the gate instead of slipping through on its default.
MODE_ARGS: dict[str, list[str]] = {
    "throughput": ["--frames", "100", "--runs", "1", "--warmup", "0", "--json"],
    "latency": ["--ops", "50", "--warmup", "0", "--json"],
    "scaling": ["--quick", "--runs", "1", "--json"],
}


class Binding(NamedTuple):
    """One benchmark harness: how to run it, and whether it is present."""

    name: str
    exe: Path
    cwd: Path
    available: bool
    required: bool
    # True: invoke ``exe -m benchmarks.<mode>``; False: pass <mode> positionally.
    python_module: bool


def _out(msg: str) -> None:
    _ = sys.stdout.write(msg + "\n")


def _err(msg: str) -> None:
    _ = sys.stderr.write(msg + "\n")


def _strs(value: object) -> list[str]:
    return cast("list[str]", value)


def _obj_map(value: object) -> dict[object, object]:
    return cast("dict[object, object]", value)


def _lib_env() -> dict[str, str]:
    """Environment with ALETHEIA_LIB at the built core (as run_all.sh sets it)."""
    env = dict(os.environ)
    so = REPO / "build" / "libaletheia-ffi.so"
    if so.exists():
        env["ALETHEIA_LIB"] = str(so)
        env.setdefault("LD_LIBRARY_PATH", str(REPO / "build"))
    return env


def _bindings() -> list[Binding]:
    """Every binding, with an availability probe on its built artifact."""
    venv_py = REPO / "python" / ".venv" / "bin" / "python3"
    cpp_bin = REPO / "cpp" / "build" / "benchmark"
    go_bin = REPO / "go" / "benchmarks" / "benchmark"
    rust_bin = REPO / "rust" / "target" / "release" / "examples" / "benchmark"
    return [
        Binding(
            "python",
            venv_py,
            REPO / "python",
            available=venv_py.exists(),
            required=True,
            python_module=True,
        ),
        Binding(
            "cpp", cpp_bin, REPO, available=cpp_bin.exists(), required=False, python_module=False
        ),
        Binding("go", go_bin, REPO, available=go_bin.exists(), required=False, python_module=False),
        Binding(
            "rust",
            rust_bin,
            REPO,
            available=rust_bin.exists(),
            required=False,
            python_module=False,
        ),
    ]


def _argv(binding: Binding, mode: str) -> list[str]:
    if binding.python_module:
        return [str(binding.exe), "-m", f"benchmarks.{mode}", *MODE_ARGS[mode]]
    return [str(binding.exe), mode, *MODE_ARGS[mode]]


def _run(binding: Binding, mode: str) -> dict[object, object]:
    """Run one binding in one mode and return its parsed JSON payload."""
    # Fixed argv (no shell); each element is a str we constructed, not user input.
    proc = subprocess.run(
        _argv(binding, mode),
        cwd=binding.cwd,
        env=_lib_env(),
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
    )
    if proc.returncode != 0:
        message = f"exited {proc.returncode}: {proc.stderr.strip()[:500]}"
        raise RuntimeError(message)
    try:
        parsed: object = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        message = f"stdout is not valid JSON ({exc})"
        raise RuntimeError(message) from exc
    return _obj_map(parsed)


def _check_envelope(
    payload: dict[object, object], mode: str, name: str, top: list[str]
) -> list[str]:
    """Top-level envelope: key set, benchmark field, language field."""
    keys = sorted(str(k) for k in payload)
    if keys != sorted(top):
        return [f"top keys {keys} != {sorted(top)}"]
    errors: list[str] = []
    if payload.get("benchmark") != mode:
        errors.append(f"benchmark field {payload.get('benchmark')!r} != {mode!r}")
    if payload.get("language") != name:
        errors.append(f"language field {payload.get('language')!r} != {name!r}")
    return errors


def _row_keys(row: object) -> set[object] | None:
    """Return ``row``'s key set if it is an object, else None (a shape error)."""
    if not isinstance(row, dict):
        return None
    return set(cast("dict[object, object]", row).keys())


def _check_list_mode(results: object, row_keys: list[str], lanes: list[str]) -> list[str]:
    """List-container modes (throughput, latency): row keys + verbatim lanes."""
    if not isinstance(results, list):
        return [f"results is {type(results).__name__}, expected list"]
    rows = cast("list[object]", results)
    errors: list[str] = []
    want: set[object] = set(row_keys)
    for i, row in enumerate(rows):
        got = _row_keys(row)
        if got is None:
            errors.append(f"results[{i}] is {type(row).__name__}, expected object")
        elif got != want:
            errors.append(f"results[{i}] keys {sorted(map(str, got))} != {sorted(row_keys)}")
    names = [cast("dict[object, object]", r).get("name") for r in rows if isinstance(r, dict)]
    if names != lanes:
        errors.append(f"lane names/order {names} != {lanes}")
    return errors


def _check_sweep(sub: str, rows_obj: object, want_keys: list[str], want_count: int) -> list[str]:
    """One scaling sub-benchmark: it is a list, has ``want_count`` rows, keys match."""
    if not isinstance(rows_obj, list):
        return [f"results[{sub}] is {type(rows_obj).__name__}, expected list"]
    rows = cast("list[object]", rows_obj)
    errors: list[str] = []
    if len(rows) != want_count:
        errors.append(f"results[{sub}] has {len(rows)} rows, expected {want_count} (--quick)")
    want: set[object] = set(want_keys)
    for i, row in enumerate(rows):
        got = _row_keys(row)
        if got != want:
            shown = sorted(map(str, got)) if got is not None else type(row).__name__
            errors.append(f"results[{sub}][{i}] keys {shown} != {sorted(want_keys)}")
    return errors


def _check_dict_mode(results: object, spec: dict[object, object]) -> list[str]:
    """Dict-container mode (scaling): sub-benchmarks, row keys, counts, labels."""
    if not isinstance(results, dict):
        return [f"results is {type(results).__name__}, expected dict"]
    payload = cast("dict[object, object]", results)
    subs = _strs(spec["sub_benchmarks"])
    if [str(k) for k in payload] != subs:
        return [f"sub-benchmark keys/order {list(payload.keys())} != {subs}"]
    row_keys = _obj_map(spec["row_keys"])
    counts = _obj_map(spec["quick_row_counts"])
    errors: list[str] = []
    for sub in subs:
        errors += _check_sweep(sub, payload[sub], _strs(row_keys[sub]), cast("int", counts[sub]))
    comp = cast("list[object]", payload.get("property_complexity", []))
    labels = [
        cast("dict[object, object]", r).get("complexity") for r in comp if isinstance(r, dict)
    ]
    if labels != _strs(spec["complexity_labels"]):
        errors.append(f"complexity labels/order {labels} != {spec['complexity_labels']}")
    return errors


def validate(
    name: str, mode: str, payload: dict[object, object], schema: dict[object, object]
) -> list[str]:
    """Return conformance errors (empty == conformant). Structure only."""
    spec = _obj_map(_obj_map(schema["modes"])[mode])
    top = _strs(_obj_map(schema["envelope"])["top_keys"])
    env_errors = _check_envelope(payload, mode, name, top)
    if env_errors and env_errors[0].startswith("top keys"):
        return [f"[{name} / {mode}] {e}" for e in env_errors]
    results = payload.get("results")
    if spec["results_container"] == "list":
        body = _check_list_mode(results, _strs(spec["row_keys"]), _strs(spec["lane_names"]))
    else:
        body = _check_dict_mode(results, spec)
    return [f"[{name} / {mode}] {e}" for e in env_errors + body]


def check_all(schema: dict[object, object]) -> tuple[list[str], list[str]]:
    """Check every available binding in every mode. Returns (errors, notices)."""
    errors: list[str] = []
    notices: list[str] = []
    modes = _strs(_obj_map(schema["envelope"])["benchmarks"])
    for binding in _bindings():
        if not binding.available:
            if binding.required:
                errors.append(f"REQUIRED binding {binding.name!r} unavailable (expected .venv)")
            else:
                notices.append(f"SKIP {binding.name}: binary not built")
            continue
        for mode in modes:
            try:
                payload = _run(binding, mode)
            except (RuntimeError, subprocess.TimeoutExpired) as exc:
                errors.append(f"[{binding.name} / {mode}] run failed: {exc}")
                continue
            errors.extend(validate(binding.name, mode, payload, schema))
    return errors, notices


def _self_test(schema: dict[object, object]) -> int:
    """Prove the gate has teeth: mutated payloads MUST be rejected."""
    tp = _obj_map(_obj_map(schema["modes"])["throughput"])
    keys = _strs(tp["row_keys"])
    lanes = _strs(tp["lane_names"])
    good_rows: list[object] = [{**dict.fromkeys(keys, 0), "name": n} for n in lanes]
    good: dict[object, object] = {
        "benchmark": "throughput",
        "language": "python",
        "timestamp": "t",
        "system": {},
        "results": good_rows,
    }
    if validate("python", "throughput", good, schema):
        _err("SELF-TEST FAIL: a conformant payload was rejected")
        return 1
    first = cast("dict[object, object]", good_rows[0])
    mutations: list[tuple[str, object]] = [
        ("renamed lane", [{**first, "name": "WRONG"}, *good_rows[1:]]),
        ("dropped row key", [dict.fromkeys(["name", "frames"], 0), *good_rows[1:]]),
        ("wrong container", {"x": 1}),
        ("reordered lanes", list(reversed(good_rows))),
    ]
    for label, bad in mutations:
        if not validate("python", "throughput", {**good, "results": bad}, schema):
            _err(f"SELF-TEST FAIL: gate accepted a bad payload ({label})")
            return 1
    _out("self-test: all 4 injected mutations were rejected -- gate has teeth")
    return 0


def main() -> int:
    """Parse args, run the self-test or the cross-binding conformance check."""
    parser = argparse.ArgumentParser(description="Cross-binding benchmark-schema gate")
    parser.add_argument(
        "--self-test", action="store_true", help="Prove the gate rejects drift, then exit"
    )
    args = parser.parse_args()

    raw: object = yaml.safe_load(SCHEMA_PATH.read_text(encoding="utf-8"))
    schema = _obj_map(raw)

    if bool(args.self_test):
        return _self_test(schema)

    errors, notices = check_all(schema)
    for notice in notices:
        _out(f"  {notice}")
    if errors:
        _err(f"\ncheck-bench-schema: FAIL ({len(errors)} conformance error(s))")
        for error in errors:
            _err(f"  x {error}")
        return 1
    _out("check-bench-schema: ok -- all available bindings conform to benchmarks/SCHEMA.yaml")
    return 0


if __name__ == "__main__":
    sys.exit(main())
