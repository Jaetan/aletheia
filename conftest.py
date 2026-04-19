"""Repo-root conftest — harness for `pytest --markdown-docs`.

Doc-example harness per AGENTS.md § Python Cat 32. Every ```python fence
across the user-facing docs (README, docs/**, python/README.md,
examples/README.md) is collected and executed end-to-end against the
real FFI.

The fakes below paper over fake-path references (``vehicle.dbc``,
``drive.blf``, ``highway.asc``, ``vehicle_checks.xlsx``, ``checks.yaml``)
so doc examples stay readable while still running against live code:

* loader wrappers (``dbc_to_json``, ``iter_can_log``, ...) ignore the path
  argument and return a purpose-built DBC or an empty iterable; this keeps
  the narrative of the fence faithful while side-stepping missing files.
* a pre-built ``dbc`` + already-entered ``client`` are injected so fences
  that reuse names from a prior narrative block (e.g. PYTHON_API
  Examples 2–4 referencing ``dbc`` defined in Example 1) resolve without
  ``continuation``-chaining every block.
* the DBC carries the signal names the docs talk about (``VehicleSpeed``,
  ``Speed``, ``BrakePedal``, ``EngineRPM``, ...) so ``build_frame`` /
  ``update_frame`` calls with those names resolve against a real message.

Scope: this conftest is only loaded when pytest's rootdir resolves to the
repo root (``--markdown-docs`` runs with ``--rootdir=<repo>``). The regular
``python/tests/`` suite uses ``python/pyproject.toml`` as its rootdir, so
these fakes do not leak into unit-test runs.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
from typing import Any, Iterator

import aletheia
import aletheia.can_log
import aletheia.dbc_converter
import aletheia.excel_loader
import aletheia.yaml_loader
from aletheia import (
    AletheiaClient,
    AletheiaError,
    BatchError,
    Check,
    FrameResponse,
    ProcessError,
    ProtocolError,
    Signal,
    eventually_always,
    infinitely_often,
    never,
)
from aletheia.dsl import Predicate, Property

_REPO_ROOT = Path(__file__).parent

# Shared defaults for every signal in the hand-built DBC. Pulled out of
# ``_signal`` so the helper takes a single ``overrides`` dict (3 positional
# + 1 dict arg) and pylint's ``too-many-arguments`` gate stays green.
_SIGNAL_DEFAULTS: dict[str, Any] = {
    "byteOrder": "little_endian",
    "signed": False,
    "factor": Fraction(1),
    "offset": Fraction(0),
    "minimum": Fraction(0),
    "maximum": Fraction(65535),
    "unit": "",
    "presence": "always",
}


def _signal(
    name: str,
    start_bit: int,
    length: int,
    overrides: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Build one signal dict from the shared defaults plus overrides.

    ``overrides`` values that happen to be ``int``/``float``/``Fraction``
    are re-wrapped as bounded ``Fraction`` so the returned dict matches the
    schema the real ``parse_dbc`` call expects (Agda-side types are exact
    rationals, not floats).
    """
    sig: dict[str, Any] = {"name": name, "startBit": start_bit, "length": length}
    sig.update(_SIGNAL_DEFAULTS)
    if overrides:
        for key, val in overrides.items():
            if isinstance(val, (int, float, Fraction)):
                sig[key] = Fraction(val).limit_denominator(10000)
            else:
                sig[key] = val
    return sig


def _doc_dbc() -> dict[str, Any]:
    """Hand-built DBC that covers the signal names used across the docs.

    Docs freely reference Speed/VehicleSpeed/EngineRPM/etc. as illustrative
    examples of property subjects. Pack those names into a single 8-byte
    message at ID 0x100 so ``build_frame``/``update_frame`` calls resolve
    against real signal definitions. The numeric ranges are deliberately
    wide so 72.0 / 130.0 / 0.0 doc-literal values stay inside [min, max].
    """
    vehicle_state = {
        "id": 0x100,
        "name": "VehicleState",
        "dlc": 8,
        "sender": "ECU",
        "signals": [
            _signal("VehicleSpeed", 0, 16,
                    {"factor": 0.01, "maximum": 655.35, "unit": "km/h"}),
            _signal("Speed", 16, 16,
                    {"factor": 0.01, "maximum": 655.35, "unit": "km/h"}),
            _signal("BrakePedal", 32, 8, {"maximum": 255, "unit": "%"}),
            _signal("EngineRPM", 40, 16, {"unit": "rpm"}),
            _signal("CoolantTemp", 56, 8,
                    {"offset": -40, "minimum": -40, "maximum": 215, "unit": "celsius"}),
        ],
    }
    return {"version": "1.0", "messages": [vehicle_state]}


def _harness_dbc_to_json(*_args: Any, **_kwargs: Any) -> Any:
    return _doc_dbc()


def _harness_convert_dbc_file(*_args: Any, **_kwargs: Any) -> str:
    # Deliberately skip the filesystem write — a doc fence like
    # ``convert_dbc_file("vehicle.dbc", "vehicle.json")`` would otherwise
    # leak ``vehicle.json`` into the repo root during harness runs.
    return "{}"


def _harness_iter_can_log(*_args: Any, **_kwargs: Any) -> Iterator[Any]:
    return iter(())


def _harness_load_can_log(*_args: Any, **_kwargs: Any) -> list[Any]:
    return []


def _harness_load_checks(*_args: Any, **_kwargs: Any) -> list[Any]:
    return []


def _harness_load_checks_from_excel(*_args: Any, **_kwargs: Any) -> list[Any]:
    return []


def _harness_load_dbc_from_excel(*_args: Any, **_kwargs: Any) -> Any:
    return _doc_dbc()


def _harness_create_template(*_args: Any, **_kwargs: Any) -> None:
    return None


def _make_globals() -> dict[str, Any]:
    """Per-test globals injected into every markdown code fence.

    Returns a fresh client + mutable collections per invocation so fences
    don't accidentally share state across files. The client is
    ``parse_dbc``'d but deliberately *not* stream-started: fences that
    document ``add_checks``/``set_properties``/``start_stream`` expect
    the pre-start state, and ``send_frame[s]``/``end_stream`` fences
    chain onto their ``start_stream`` predecessor via ``continuation``.
    """
    dbc = _doc_dbc()
    client = AletheiaClient()
    client.__enter__()  # pylint: disable=unnecessary-dunder-call
    client.parse_dbc(dbc)
    return {
        "AletheiaClient": AletheiaClient,
        "Signal": Signal,
        "Predicate": Predicate,
        "Property": Property,
        "Check": Check,
        "AletheiaError": AletheiaError,
        "ProtocolError": ProtocolError,
        "ProcessError": ProcessError,
        "BatchError": BatchError,
        "FrameResponse": FrameResponse,
        "infinitely_often": infinitely_often,
        "eventually_always": eventually_always,
        "never": never,
        "dbc_to_json": _harness_dbc_to_json,
        "convert_dbc_file": _harness_convert_dbc_file,
        "iter_can_log": _harness_iter_can_log,
        "load_can_log": _harness_load_can_log,
        "load_checks": _harness_load_checks,
        "load_checks_from_excel": _harness_load_checks_from_excel,
        "load_dbc_from_excel": _harness_load_dbc_from_excel,
        "create_template": _harness_create_template,
        "dbc": dbc,
        "dbc_json": dbc,
        "client": client,
        "frames": [],
        "trace": [],
        "checks": [],
        "properties": [],
        "safety_checks": [],
        "session_checks": [],
        "can_trace": [],
        "frame_bytes": bytes(8),
        "property": Signal("Speed").less_than(250).always(),
        "brake_pressed": Signal("BrakePedal").greater_than(0),
        "ts": 0,
        "can_id": 0x100,
        "dlc": 8,
        "data": bytes(8),
    }


def pytest_sessionstart() -> None:
    """Replace loader functions project-wide with harness wrappers.

    In-fence ``from aletheia.dbc_converter import dbc_to_json`` binds the
    real function, bypassing the globals hook. Patching both the
    re-exports on ``aletheia`` and the definitions on their submodules
    ensures every import form lands on the fake.
    """
    aletheia.dbc_to_json = _harness_dbc_to_json
    aletheia.dbc_converter.dbc_to_json = _harness_dbc_to_json
    aletheia.convert_dbc_file = _harness_convert_dbc_file
    aletheia.dbc_converter.convert_dbc_file = _harness_convert_dbc_file
    aletheia.iter_can_log = _harness_iter_can_log
    aletheia.can_log.iter_can_log = _harness_iter_can_log
    aletheia.load_can_log = _harness_load_can_log
    aletheia.can_log.load_can_log = _harness_load_can_log
    aletheia.load_checks = _harness_load_checks
    aletheia.yaml_loader.load_checks = _harness_load_checks
    aletheia.load_checks_from_excel = _harness_load_checks_from_excel
    aletheia.excel_loader.load_checks_from_excel = _harness_load_checks_from_excel
    aletheia.load_dbc_from_excel = _harness_load_dbc_from_excel
    aletheia.excel_loader.load_dbc_from_excel = _harness_load_dbc_from_excel
    aletheia.create_template = _harness_create_template
    aletheia.excel_loader.create_template = _harness_create_template


def pytest_markdown_docs_globals() -> dict[str, Any]:
    """pytest-markdown-docs hook — globals merged into every fence's namespace."""
    return _make_globals()
