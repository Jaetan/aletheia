"""Engine-layer driver for :func:`run_checks` and its result types.

Streams a CAN log through :class:`AletheiaClient`, builds enriched
violations from the per-frame and end-of-stream responses, and returns
a :class:`CheckRunResult`.  CLI presentation lives in :mod:`aletheia.cli`;
this module deliberately contains no ``print`` / ``sys.exit`` calls so
it can be reused by ``aletheia.testing`` and external harnesses without
the CLI's exit-code coupling.

Failures (DBC parse, add-checks, start-stream, end-stream, missing
logfile) raise :class:`AletheiaError`; the CLI catches and routes those
to its ``_die`` exit-code path.
"""

from __future__ import annotations

import importlib
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import TYPE_CHECKING, TypedDict, cast

from .checks import CheckResult
from .client import AletheiaClient, AletheiaError
from .protocols import (
    DBCDefinition,
    PropertyResultEntry,
    PropertyViolationResponse,
    RationalNumber,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator

    from .client import CANFrameTuple


class Violation(TypedDict):
    """Single violation record produced by ``run_checks``.

    Stable wire shape consumed by the CLI's text/JSON output formatters,
    by ``aletheia.testing`` re-exports, and by benchmark harnesses that
    measure the full CLI pipeline.  Every field is required — no
    ``NotRequired`` keys — so consumers can index without guarding.
    """

    check_index: int
    check_name: str
    severity: str
    timestamp_us: int
    reason: str
    signal_name: str
    actual_value: Fraction | None
    condition: str


@dataclass(frozen=True, slots=True)
class CheckRunResult:
    """Aggregate result of a :func:`run_checks` invocation.

    ``unresolved`` carries end-of-stream finalization results whose three-valued
    Kleene verdict was Unknown (``status="unresolved"``), e.g. ``Always(p)``
    where ``p``'s signal was never observed — distinct from ``violations``,
    where the property was proved to fail.
    """
    violations:   list[Violation]
    unresolved:   list[Violation]
    total_frames: int


def rational_to_int(r: RationalNumber) -> int:
    """Convert a RationalNumber {numerator, denominator} to int."""
    denom = r["denominator"]
    if denom == 0:
        raise ValueError(f"Invalid rational: denominator is zero ({r!r})")
    return r["numerator"] // denom


def _lazy_iter_can_log() -> Callable[[str | Path], Iterator[CANFrameTuple]]:
    mod = importlib.import_module(".can_log", __package__)
    return cast(
        "Callable[[str | Path], Iterator[CANFrameTuple]]", mod.iter_can_log
    )


def _check_meta(
    prop_index: int, checks: list[CheckResult],
) -> tuple[str, str]:
    """Look up check name and severity by property index."""
    if 0 <= prop_index < len(checks):
        name = checks[prop_index].name or f"Check #{prop_index}"
        sev = checks[prop_index].check_severity or ""
        return name, sev
    return f"Check #{prop_index}", ""


def _build_violation(
    response: PropertyViolationResponse, checks: list[CheckResult],
) -> Violation:
    """Extract violation details from an (already enriched) violation response."""
    prop_index = rational_to_int(response["property_index"])
    check_name, severity = _check_meta(prop_index, checks)

    enrichment = response.get("enrichment")
    if enrichment is not None:
        reason = enrichment["enriched_reason"]
        signals = enrichment["signals"]
        condition = enrichment["formula_desc"]
    else:
        reason = response.get("reason", "")
        signals = {}
        condition = ""
    signal_name = ""
    actual_value: Fraction | None = None
    if signals:
        sig = next(iter(signals))
        signal_name = sig
        actual_value = signals[sig]

    return {
        "check_index": prop_index,
        "check_name": check_name,
        "severity": severity,
        "timestamp_us": rational_to_int(response["timestamp"]),
        "reason": reason,
        "signal_name": signal_name,
        "actual_value": actual_value,
        "condition": condition,
    }


def _build_eos_violation(
    result: PropertyResultEntry, checks: list[CheckResult],
) -> Violation:
    """Extract violation details from an end-of-stream finalization result."""
    prop_index = rational_to_int(result["property_index"])
    check_name, severity = _check_meta(prop_index, checks)

    enrichment = result.get("enrichment")
    if enrichment is not None:
        reason = enrichment["enriched_reason"] or "end-of-stream violation"
        condition = enrichment["formula_desc"]
    else:
        reason = result.get("reason", "end-of-stream violation")
        condition = ""

    return {
        "check_index": prop_index,
        "check_name": check_name,
        "severity": severity,
        "timestamp_us": 0,
        "reason": reason,
        "signal_name": "",
        "actual_value": None,
        "condition": condition,
    }


def run_checks(  # pylint: disable=too-many-locals
    dbc: DBCDefinition,
    checks: list[CheckResult],
    logfile: str,
    default_checks: list[CheckResult] | None = None,
) -> CheckRunResult:
    """Stream a CAN log through the Aletheia engine.

    Returns a :class:`CheckRunResult` carrying the collected violations,
    end-of-stream unresolved results (three-valued Kleene Unknown), and
    the total frame count.

    Raises:
        FileNotFoundError: ``logfile`` does not exist.
        AletheiaError:     DBC parse, add-checks, start-stream, or
            end-stream failed at the FFI boundary.
    """
    all_checks = (default_checks or []) + checks
    if not Path(logfile).exists():
        raise FileNotFoundError(f"log file not found: {logfile}")
    with AletheiaClient(default_checks=default_checks) as client:
        resp = client.parse_dbc(dbc)
        if resp["status"] != "success":
            raise AletheiaError(f"DBC parse failed: {resp['message']}")

        resp = client.add_checks(checks)
        if resp["status"] != "success":
            raise AletheiaError(f"set properties failed: {resp['message']}")

        resp = client.start_stream()
        if resp["status"] != "success":
            raise AletheiaError(f"start stream failed: {resp['message']}")

        violations:   list[Violation] = []
        unresolved:   list[Violation] = []
        total_frames = 0

        for frame in _lazy_iter_can_log()(logfile):
            total_frames += 1
            response = client.send_frame(
                frame.timestamp, frame.can_id, frame.dlc, frame.data,
                extended=frame.extended, brs=frame.brs, esi=frame.esi,
            )
            if response["status"] == "fails":
                violations.append(_build_violation(response, all_checks))

        end_resp = client.end_stream()
        if end_resp["status"] == "error":
            raise AletheiaError(f"end stream failed: {end_resp['message']}")
        for result in end_resp["results"]:
            if result["status"] == "fails":
                violations.append(_build_eos_violation(result, all_checks))
            elif result["status"] == "unresolved":
                unresolved.append(_build_eos_violation(result, all_checks))

    return CheckRunResult(violations, unresolved, total_frames)


__all__ = [
    "CheckRunResult",
    "Violation",
    "rational_to_int",
    "run_checks",
]
