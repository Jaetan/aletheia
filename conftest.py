# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
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
from typing import TYPE_CHECKING, TypedDict

import pytest

import aletheia
import aletheia.can_log
import aletheia.checks
import aletheia.dbc_converter
import aletheia.excel_loader
import aletheia.yaml_loader
from aletheia import (
    AletheiaClient,
    AletheiaError,
    BatchError,
    CANFrameTuple,
    FrameResponse,
    ProtocolError,
    Signal,
    ValidationError,
    eventually_always,
    infinitely_often,
    never,
)
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.dsl import Predicate, Property
from aletheia.protocols import DLCByteCount, DLCCode

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator
    from types import ModuleType
    from typing import TypeAliasType

    from aletheia import CheckResult, DBCDefinition
    from aletheia.protocols import DBCMessage, DBCSignalAlways

_REPO_ROOT = Path(__file__).parent


class _SignalOverrides(TypedDict, total=False):
    """Per-signal field overrides accepted by :func:`_signal`.

    Bundled into one optional dict so ``_signal`` stays at four parameters
    (pylint ``too-many-arguments``).  Numeric fields are exact ``Fraction``s
    to match the Agda core's rational schema (``parse_dbc`` rejects floats).
    """

    factor: Fraction
    offset: Fraction
    minimum: Fraction
    maximum: Fraction
    unit: str


def _signal(
    name: str,
    start_bit: int,
    length: int,
    overrides: _SignalOverrides | None = None,
) -> DBCSignalAlways:
    """Build one always-present signal from defaults plus optional overrides."""
    o: _SignalOverrides = overrides if overrides is not None else {}
    return {
        "name": name,
        "startBit": start_bit,
        "length": length,
        "byteOrder": "little_endian",
        "signed": False,
        "factor": o.get("factor", Fraction(1)),
        "offset": o.get("offset", Fraction(0)),
        "minimum": o.get("minimum", Fraction(0)),
        "maximum": o.get("maximum", Fraction(65535)),
        "unit": o.get("unit", ""),
        "presence": "always",
    }


def _doc_dbc() -> DBCDefinition:
    """Hand-built DBC that covers the signal names used across the docs.

    Docs freely reference Speed/VehicleSpeed/EngineRPM/etc. as illustrative
    examples of property subjects. Pack those names into a single 8-byte
    message at ID 0x100 so ``build_frame``/``update_frame`` calls resolve
    against real signal definitions. The numeric ranges are deliberately
    wide so 72.0 / 130.0 / 0.0 doc-literal values stay inside [min, max].
    """
    speed_overrides: _SignalOverrides = {
        "factor": Fraction(1, 100),
        "maximum": Fraction("655.35"),
        "unit": "km/h",
    }
    vehicle_state: DBCMessage = {
        "id": 0x100,
        "name": "VehicleState",
        "dlc": DLCByteCount(8),
        "sender": "ECU",
        "signals": [
            _signal("VehicleSpeed", 0, 16, speed_overrides),
            _signal("Speed", 16, 16, speed_overrides),
            _signal("BrakePedal", 32, 8, {"maximum": Fraction(255), "unit": "%"}),
            _signal("EngineRPM", 40, 16, {"unit": "rpm"}),
            _signal(
                "CoolantTemp",
                56,
                8,
                {
                    "offset": Fraction(-40),
                    "minimum": Fraction(-40),
                    "maximum": Fraction(215),
                    "unit": "celsius",
                },
            ),
        ],
    }
    return {"version": "1.0", "messages": [vehicle_state], **empty_dbc_tier2()}


def _harness_dbc_to_json[**P](*_args: P.args, **_kwargs: P.kwargs) -> DBCDefinition:
    return _doc_dbc()


def _harness_convert_dbc_file[**P](*_args: P.args, **_kwargs: P.kwargs) -> str:
    # Deliberately skip the filesystem write — a doc fence like
    # ``convert_dbc_file("vehicle.dbc", "vehicle.json")`` would otherwise
    # leak ``vehicle.json`` into the repo root during harness runs.
    return "{}"


def _harness_iter_can_log[**P](*_args: P.args, **_kwargs: P.kwargs) -> Iterator[CANFrameTuple]:
    """Return a single illustrative 7-tuple frame.

    Empty iterators silently pass any unpack — including a 4-tuple unpack
    against a 7-tuple yield, the exact drift that R18 cluster 11 (5-tuple
    era) and R20 cluster L (5 → 7 transition after R19 cluster 18 added
    BRS/ESI) surfaced across the doc sites. Yielding at least one real
    ``CANFrameTuple`` ensures every fence body that iterates is actually
    exercised, so unpack-arity drift fails fast at fence-execution time.
    The synthetic frame ``(0, 0x100, 8, bytes(8), False, None, None)``
    resolves cleanly against the harness DBC's message id ``0x100`` with
    ``dlc=8``; downstream signal values decode to 0, comfortably below
    the ``Speed < 250`` property the docs commonly reference. ``brs`` and
    ``esi`` are ``None`` (CAN 2.0B; the BRS/ESI bits do not exist).
    """
    return iter([CANFrameTuple(0, 0x100, DLCCode(8), bytes(8), extended=False, brs=None, esi=None)])


def _harness_load_can_log[**P](*_args: P.args, **_kwargs: P.kwargs) -> list[CANFrameTuple]:
    return []


def _harness_load_checks[**P](*_args: P.args, **_kwargs: P.kwargs) -> list[CheckResult]:
    return []


def _harness_load_checks_from_excel[**P](*_args: P.args, **_kwargs: P.kwargs) -> list[CheckResult]:
    return []


def _harness_load_dbc_from_excel[**P](*_args: P.args, **_kwargs: P.kwargs) -> DBCDefinition:
    return _doc_dbc()


def _harness_create_template[**P](*_args: P.args, **_kwargs: P.kwargs) -> None:
    return None


class _DocGlobals(TypedDict):
    """Exact name -> type map of the namespace injected into every doc fence.

    Naming each entry (rather than ``dict[str, object]``) keeps the harness
    self-documenting and lets the type checker verify the construction in
    :func:`_make_globals`.  The empty scratch lists carry the element type
    fences are expected to append.
    """

    # The colliding names (AletheiaClient/Signal/Predicate/Property/...) are
    # both TypedDict field names AND types referenced in the annotations, so
    # they are written ``aletheia.X`` (module-qualified) to resolve to the
    # re-exported type rather than the class-scoped field.
    AletheiaClient: type[aletheia.AletheiaClient]
    Signal: type[aletheia.Signal]
    Predicate: type[aletheia.Predicate]
    Property: type[aletheia.Property]
    AletheiaError: type[aletheia.AletheiaError]
    ProtocolError: type[aletheia.ProtocolError]
    ValidationError: type[aletheia.ValidationError]
    BatchError: type[aletheia.BatchError]
    FrameResponse: TypeAliasType
    infinitely_often: Callable[[aletheia.Property | aletheia.Predicate], aletheia.Property]
    eventually_always: Callable[[aletheia.Property | aletheia.Predicate], aletheia.Property]
    never: Callable[[aletheia.Property | aletheia.Predicate], aletheia.Property]
    dbc_to_json: Callable[..., DBCDefinition]
    convert_dbc_file: Callable[..., str]
    iter_can_log: Callable[..., Iterator[CANFrameTuple]]
    load_can_log: Callable[..., list[CANFrameTuple]]
    load_checks: Callable[..., list[CheckResult]]
    load_checks_from_excel: Callable[..., list[CheckResult]]
    load_dbc_from_excel: Callable[..., DBCDefinition]
    create_template: Callable[..., None]
    dbc: DBCDefinition
    dbc_json: DBCDefinition
    client: aletheia.AletheiaClient
    frames: list[CANFrameTuple]
    trace: list[CANFrameTuple]
    checks: ModuleType
    check_list: list[CheckResult]
    properties: list[aletheia.Property]
    safety_checks: list[CheckResult]
    session_checks: list[CheckResult]
    can_trace: list[CANFrameTuple]
    frame_bytes: bytes
    property: aletheia.Property
    brake_pressed: aletheia.Predicate
    ts: int
    can_id: int
    dlc: int
    data: bytes


def _make_globals() -> _DocGlobals:
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
        "AletheiaError": AletheiaError,
        "ProtocolError": ProtocolError,
        "ValidationError": ValidationError,
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
        "checks": aletheia.checks,
        "check_list": [],
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


def pytest_markdown_docs_globals() -> _DocGlobals:
    """pytest-markdown-docs hook — globals merged into every fence's namespace."""
    return _make_globals()


@pytest.fixture(autouse=True)
def sandbox_cwd(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Run every doc fence with cwd redirected to a per-test ``tmp_path``.

    Defense-in-depth: even though ``pytest_sessionstart`` patches
    ``create_template`` (and the other loader entry points) to no-op
    fakes, the patches only fire when this conftest is loaded.  Running
    pytest with a non-repo rootdir bypasses the conftest, lets the real
    ``create_template`` execute, and lands ``vehicle_checks.xlsx`` in the
    invoking shell's cwd.  Pinning cwd to ``tmp_path`` per test means any
    file write — patched or not — goes to a sandboxed dir that pytest
    auto-cleans, so the repo tree stays clean regardless of how the
    harness was invoked.  Doc fences do not depend on cwd: the loader
    fakes (``load_checks`` / ``iter_can_log`` / etc.) ignore their path
    args entirely, so the chdir is invisible to fence behaviour.
    """
    monkeypatch.chdir(tmp_path)
