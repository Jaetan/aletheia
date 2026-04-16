"""Command-line interface for Aletheia CAN signal verification

Subcommands:
    check     — run LTL checks against a CAN log file
    extract   — decode signals from a single CAN frame
    signals   — list all signals defined in a DBC file
    validate  — validate a DBC definition for structural issues
    mux-query — inspect multiplexor structure of a DBC message

Usage:
    python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
    python -m aletheia extract --dbc vehicle.dbc 0x100 401F7D0000000000
    python -m aletheia signals --dbc vehicle.dbc
    python -m aletheia mux-query --dbc vehicle.dbc 0x100
    python -m aletheia mux-query --dbc vehicle.dbc 0x100 --mux Mode --value 5
"""

from __future__ import annotations

import argparse
import importlib
import sys
from fractions import Fraction
from pathlib import Path
from typing import TYPE_CHECKING, NoReturn, TypedDict, cast

from . import __version__
from .checks import CheckResult
from .client import (
    AletheiaClient,
    AletheiaError,
    SignalExtractionResult,
    dlc_to_bytes,
    dump_json,
)
from .dbc_queries import (
    is_multiplexed,
    message_by_id,
    message_by_name,
    multiplexor_names,
    mux_values,
    signals_for_mux_value,
)
from .protocols import (
    DBCDefinition,
    DBCMessage,
    DBCSignal,
    IssueSeverity,
    PropertyResultEntry,
    PropertyViolationResponse,
    RationalNumber,
    ValidationIssue,
)

if TYPE_CHECKING:
    # Type-only imports for the lazy helpers below — these are not available
    # at runtime when the corresponding optional dependency is not installed.
    from collections.abc import Callable, Iterator

    from .client import CANFrameTuple


# Optional-dependency loaders: each CLI helper resolves its target via
# ``importlib.import_module`` at the point of use so that subcommands whose
# code paths don't need a given optional package (e.g. ``aletheia signals
# --dbc foo.json`` needs neither cantools nor python-can) can still run
# without the corresponding extras installed. Using ``importlib`` (rather
# than a function-scoped ``from .X import Y``) keeps pylint's
# ``import-outside-toplevel`` check happy without suppressions.
def _lazy_dbc_to_json() -> Callable[[str | Path], DBCDefinition]:
    mod = importlib.import_module(".dbc_converter", __package__)
    return cast("Callable[[str | Path], DBCDefinition]", mod.dbc_to_json)


def _lazy_load_dbc_from_excel() -> Callable[[str | Path], DBCDefinition]:
    mod = importlib.import_module(".excel_loader", __package__)
    return cast("Callable[[str | Path], DBCDefinition]", mod.load_dbc_from_excel)


def _lazy_load_checks_from_excel() -> Callable[[str | Path], list[CheckResult]]:
    mod = importlib.import_module(".excel_loader", __package__)
    return cast(
        "Callable[[str | Path], list[CheckResult]]", mod.load_checks_from_excel
    )


def _lazy_load_yaml_checks() -> Callable[[str | Path], list[CheckResult]]:
    mod = importlib.import_module(".yaml_loader", __package__)
    return cast("Callable[[str | Path], list[CheckResult]]", mod.load_checks)


def _lazy_iter_can_log() -> Callable[[str | Path], Iterator[CANFrameTuple]]:
    mod = importlib.import_module(".can_log", __package__)
    return cast(
        "Callable[[str | Path], Iterator[CANFrameTuple]]", mod.iter_can_log
    )


# ============================================================================
# Exit codes
# ============================================================================

_EXIT_OK = 0
_EXIT_VIOLATIONS = 1
_EXIT_ERROR = 2

class _Violation(TypedDict):
    check_index: int
    check_name: str
    severity: str
    timestamp_us: int
    reason: str
    signal_name: str
    actual_value: Fraction | None
    condition: str


# ============================================================================
# Helpers
# ============================================================================

def _die(msg: str) -> NoReturn:
    """Print error to stderr and exit with code 2."""
    print(f"Error: {msg}", file=sys.stderr)
    sys.exit(_EXIT_ERROR)


def parse_can_id(s: str) -> int:
    """Parse a CAN ID from hex (0x100) or decimal (256) string.

    Raises:
        ValueError: If *s* is not a valid integer.
    """
    s = s.strip()
    try:
        if s.lower().startswith("0x"):
            return int(s, 16)
        return int(s)
    except ValueError as exc:
        raise ValueError(f"Invalid CAN ID: {s!r}") from exc


def parse_hex_data(s: str) -> bytearray:
    """Parse hex data string into a bytearray.

    Accepts:
        "401F7D0000000000"
        "40 1F 7D 00 00 00 00 00"
        "40:1F:7D:00:00:00:00:00"

    Raises:
        ValueError: If *s* contains non-hex characters or has odd length.
    """
    cleaned = s.replace(" ", "").replace(":", "")
    if cleaned.lower().startswith("0x"):
        cleaned = cleaned[2:]
    if len(cleaned) % 2 != 0:
        raise ValueError(f"Hex data has odd number of characters: {s!r}")
    try:
        return bytearray.fromhex(cleaned)
    except ValueError as exc:
        raise ValueError(f"Invalid hex data: {s!r}") from exc


def rational_to_int(r: RationalNumber) -> int:
    """Convert a RationalNumber {numerator, denominator} to int."""
    denom = r["denominator"]
    if denom == 0:
        raise ValueError(f"Invalid rational: denominator is zero ({r!r})")
    return r["numerator"] // denom


def format_timestamp(us: int) -> str:
    """Format microseconds as a human-readable timestamp.

    Returns "1234.500ms" for 1234500 us.
    """
    ms = us / 1000.0
    return f"{ms:.3f}ms"


def _load_dbc(args: argparse.Namespace) -> DBCDefinition:
    """Load DBC definition from --dbc or --excel flag."""
    dbc_path: str | None = getattr(args, "dbc", None)
    excel_path: str | None = getattr(args, "excel", None)

    if dbc_path is not None:
        p = Path(dbc_path)
        if not p.exists():
            _die(f"DBC file not found: {dbc_path}")
        if p.suffix == ".xlsx":
            return _lazy_load_dbc_from_excel()(p)
        return _lazy_dbc_to_json()(p)

    if excel_path is not None:
        p = Path(excel_path)
        if not p.exists():
            _die(f"Excel file not found: {excel_path}")
        return _lazy_load_dbc_from_excel()(p)

    _die("no DBC source specified (use --dbc or --excel)")


def _load_checks_from_args(args: argparse.Namespace) -> list[CheckResult]:
    """Load checks from --checks or --excel flag."""
    checks_path: str | None = getattr(args, "checks", None)
    excel_path: str | None = getattr(args, "excel", None)

    results: list[CheckResult] = []

    if checks_path is not None:
        p = Path(checks_path)
        if not p.exists():
            _die(f"checks file not found: {checks_path}")
        if p.suffix == ".xlsx":
            results.extend(_lazy_load_checks_from_excel()(p))
        else:
            results.extend(_lazy_load_yaml_checks()(p))

    if excel_path is not None and checks_path is None:
        p = Path(excel_path)
        if not p.exists():
            _die(f"Excel file not found: {excel_path}")
        results.extend(_lazy_load_checks_from_excel()(p))

    if not results:
        _die("no checks specified (use --checks or --excel)")

    return results


def _find_message(
    dbc: DBCDefinition, can_id: int, extended: bool = False,
) -> DBCMessage | None:
    """Find a message by CAN ID + extended flag in a DBC definition.

    Delegates to ``message_by_id`` from ``dbc_queries``.
    """
    return message_by_id(dbc, can_id, extended=extended)


def _signal_units(msg: DBCMessage) -> dict[str, str]:
    """Extract signal name → unit mapping from a DBC message."""
    return {sig["name"]: sig["unit"] for sig in msg["signals"]}


# ============================================================================
# Subcommand: signals
# ============================================================================

def _format_signal_line(sig: DBCSignal) -> str:
    """Format a single signal as a one-line summary."""
    name = sig["name"]
    start = sig["startBit"]
    length = sig["length"]
    order = "LE" if sig["byteOrder"] == "little_endian" else "BE"
    sign = "signed" if sig["signed"] else "unsigned"
    factor = sig["factor"]
    offset = sig["offset"]
    unit = sig["unit"]
    minimum = sig["minimum"]
    maximum = sig["maximum"]

    offset_str = f"+{offset:g}" if offset >= 0 else f"{offset:g}"
    range_str = f"[{minimum:g}, {maximum:g}]" if minimum != 0 or maximum != 0 else ""

    return (
        f"  {name:<20s} bits[{start}:{length}]"
        + f"   {order}  {sign:<10s}"
        + f"  x{factor:g} {offset_str}"
        + f"  {unit:>6s}  {range_str}"
    )


def _print_signals_text(dbc: DBCDefinition) -> None:
    """Print DBC signals in human-readable text format."""
    messages = dbc["messages"]
    total_signals = 0

    for msg in messages:
        sender = msg["sender"]
        sender_part = f", sender {sender}" if sender else ""
        print(f"Message 0x{msg['id']:X} {msg['name']} (DLC {msg['dlc']}{sender_part})")

        for sig in msg["signals"]:
            total_signals += 1
            print(_format_signal_line(sig))

        print()

    print(f"{len(messages)} messages, {total_signals} signals")


def _cmd_signals(args: argparse.Namespace) -> int:
    """List signals defined in a DBC file."""
    dbc = _load_dbc(args)

    if getattr(args, "json", False):
        print(dump_json(dbc, indent=2))
    else:
        _print_signals_text(dbc)

    return _EXIT_OK


# ============================================================================
# Subcommand: validate
# ============================================================================

def _print_validation_text(issues: list[ValidationIssue], has_errors: bool) -> None:
    """Print validation issues in human-readable text format."""
    if not issues:
        print("Validation passed: no issues found")
        return

    errors = [i for i in issues if i["severity"] == IssueSeverity.ERROR]
    warnings = [i for i in issues if i["severity"] == IssueSeverity.WARNING]

    if has_errors:
        print(f"Validation FAILED: {len(errors)} errors, {len(warnings)} warnings")
    else:
        print(f"Validation passed with {len(warnings)} warnings")
    print()

    for i, issue in enumerate(issues, 1):
        sev = issue["severity"].upper()
        code = issue["code"]
        detail = issue["detail"]
        print(f"  {i}. [{sev}] {code}: {detail}")

    print()


def _cmd_validate(args: argparse.Namespace) -> int:
    """Validate a DBC definition for structural issues."""
    dbc = _load_dbc(args)

    with AletheiaClient() as client:
        result = client.validate_dbc(dbc)

    issues = result["issues"]
    has_errors = result["has_errors"]

    if getattr(args, "json", False):
        out = {
            "status": "fail" if has_errors else "pass",
            "has_errors": has_errors,
            "total_issues": len(issues),
            "issues": issues,
        }
        print(dump_json(out, indent=2))
    else:
        _print_validation_text(issues, has_errors)

    return _EXIT_VIOLATIONS if has_errors else _EXIT_OK


# ============================================================================
# Subcommand: extract
# ============================================================================

def _print_extract_text(
    can_id: int, dbc: DBCDefinition, result: SignalExtractionResult,
) -> None:
    """Print extraction results in human-readable text format."""
    msg = _find_message(dbc, can_id)
    units = _signal_units(msg) if msg is not None else {}

    name_part = f" ({msg['name']})" if msg is not None else ""
    print(f"CAN ID 0x{can_id:X}{name_part}:")
    print()

    if result.values:
        for name, value in result.values.items():
            unit = units.get(name, "")
            unit_part = f" {unit}" if unit else ""
            print(f"  {name:<20s} = {value:g}{unit_part}")
    else:
        print("  (no signals)")

    print()
    _print_extract_errors(result)


def _print_extract_errors(result: SignalExtractionResult) -> None:
    """Print extraction error/absent sections."""
    if result.errors:
        print("Errors:")
        for name, err in result.errors.items():
            print(f"  {name}: {err}")
    else:
        print("Errors: none")

    if result.absent:
        print(f"Absent: {', '.join(result.absent)}")
    else:
        print("Absent: none")


def _cmd_extract(args: argparse.Namespace) -> int:
    """Decode signals from a single CAN frame."""
    dbc = _load_dbc(args)
    can_id = parse_can_id(args.can_id)
    data = parse_hex_data(args.data)
    extended: bool = getattr(args, "extended", False)

    # Look up expected DLC from the DBC message definition
    msg = _find_message(dbc, can_id, extended=extended)
    if msg is None:
        id_kind = "extended" if extended else "standard"
        _die(f"CAN ID 0x{can_id:X} ({id_kind}) not found in DBC")
    expected_bytes = dlc_to_bytes(msg["dlc"])
    if len(data) != expected_bytes:
        _die(
            f"data length ({len(data)} bytes) does not match "
            + f"DBC message DLC ({msg['dlc']} → {expected_bytes} bytes)"
        )

    with AletheiaClient() as client:
        resp = client.parse_dbc(dbc)
        if resp["status"] != "success":
            _die(f"DBC parse failed: {resp.get('message', 'unknown error')}")
        result = client.extract_signals(
            can_id=can_id, dlc=msg["dlc"], data=data, extended=extended,
        )

    if getattr(args, "json", False):
        out = {
            "can_id": can_id,
            "extended": extended,
            "values": dict(result.values),
            "errors": dict(result.errors),
            "absent": result.absent,
        }
        print(dump_json(out, indent=2))
    else:
        _print_extract_text(can_id, dbc, result)

    return _EXIT_OK


# ============================================================================
# Subcommand: check
# ============================================================================

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
) -> _Violation:
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
    # Pick first signal for single-line violation display
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
) -> _Violation:
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
        "timestamp_us": 0,  # End-of-stream has no specific timestamp
        "reason": reason,
        "signal_name": "",
        "actual_value": None,
        "condition": condition,
    }


def _run_checks(  # pylint: disable=too-many-locals
    dbc: DBCDefinition,
    checks: list[CheckResult],
    logfile: str,
    default_checks: list[CheckResult] | None = None,
) -> tuple[list[_Violation], list[_Violation], int]:
    """Stream a CAN log through the Aletheia engine.

    Returns (violations, unresolved, total_frames). ``unresolved`` contains
    end-of-stream finalization results whose three-valued Kleene verdict was
    Unknown (``status="unresolved"``), e.g. ``Always(p)`` where ``p``'s
    signal was never observed. These are distinct from violations: the
    property was neither proved to hold nor proved to fail.
    """
    all_checks = (default_checks or []) + checks
    with AletheiaClient(default_checks=default_checks) as client:
        resp = client.parse_dbc(dbc)
        if resp["status"] != "success":
            _die(f"DBC parse failed: {resp['message']}")

        resp = client.add_checks(checks)
        if resp["status"] != "success":
            _die(f"set properties failed: {resp['message']}")

        resp = client.start_stream()
        if resp["status"] != "success":
            _die(f"start stream failed: {resp['message']}")

        violations: list[_Violation] = []
        unresolved: list[_Violation] = []
        total_frames = 0

        for ts, can_id, dlc, data, ext in _lazy_iter_can_log()(logfile):
            total_frames += 1
            response = client.send_frame(ts, can_id, dlc, data, extended=ext)
            if response["status"] == "fails":
                violations.append(_build_violation(response, all_checks))

        end_resp = client.end_stream()
        if end_resp["status"] == "error":
            _die(f"end stream failed: {end_resp['message']}")
        # Collect end-of-stream results from finalization
        for result in end_resp["results"]:
            if result["status"] == "fails":
                violations.append(_build_eos_violation(result, all_checks))
            elif result["status"] == "unresolved":
                unresolved.append(_build_eos_violation(result, all_checks))

    return violations, unresolved, total_frames


def _print_check_results(
    violations: list[_Violation],
    unresolved: list[_Violation],
    total_frames: int,
    num_checks: int,
) -> None:
    """Print check results in human-readable text format."""
    print(f"Streaming {total_frames} frames...")
    print()

    if violations:
        print(f"RESULT: {len(violations)} violations found")
        print()
        for i, v in enumerate(violations, 1):
            _print_violation(i, v)
    elif unresolved:
        print(f"RESULT: no violations, {len(unresolved)} unresolved")
        print()
    else:
        print("RESULT: all checks passed")
        print()

    if unresolved:
        print(f"Unresolved ({len(unresolved)} — signal never observed or verdict Unknown):")
        for i, v in enumerate(unresolved, 1):
            _print_violation(i, v)

    print(
        f"Summary: {len(violations)} violations, {len(unresolved)} unresolved "
        + f"in {num_checks} checks, {total_frames} frames processed"
    )


def _print_violation(index: int, v: _Violation) -> None:
    """Print a single violation entry."""
    sev_part = f" ({v['severity']})" if v["severity"] else ""
    ts_str = format_timestamp(v["timestamp_us"])
    print(f"  {index}. [t={ts_str}] {v['check_name']}{sev_part}")
    if v["reason"]:
        print(f"     {v['reason']}")
    print()


def _load_defaults(args: argparse.Namespace) -> list[CheckResult]:
    """Load default checks from --defaults flag, if provided."""
    defaults_path: str | None = getattr(args, "defaults", None)
    if defaults_path is None:
        return []
    p = Path(defaults_path)
    if not p.exists():
        _die(f"defaults file not found: {defaults_path}")
    if p.suffix == ".xlsx":
        return _lazy_load_checks_from_excel()(p)
    return _lazy_load_yaml_checks()(p)


def _cmd_check(args: argparse.Namespace) -> int:
    """Run LTL checks against a CAN log file."""
    dbc = _load_dbc(args)
    checks = _load_checks_from_args(args)
    default_checks = _load_defaults(args)
    logfile: str = args.logfile

    if not Path(logfile).exists():
        _die(f"log file not found: {logfile}")

    violations, unresolved, total_frames = _run_checks(
        dbc, checks, logfile, default_checks
    )

    if getattr(args, "json", False):
        if violations:
            status = "violations"
        elif unresolved:
            status = "unresolved"
        else:
            status = "pass"
        out = {
            "status": status,
            "total_frames": total_frames,
            "total_violations": len(violations),
            "total_unresolved": len(unresolved),
            "violations": violations,
            "unresolved": unresolved,
        }
        print(dump_json(out, indent=2))
    else:
        dbc_label = getattr(args, "dbc", None) or getattr(args, "excel", None) or "?"
        checks_label = getattr(args, "checks", None) or getattr(args, "excel", None) or "?"
        total_checks = len(default_checks) + len(checks)
        print("Aletheia — CAN Signal Verification")
        print()
        print(f"DBC:    {dbc_label}")
        if default_checks:
            print(
                f"Checks: {checks_label} ({len(checks)} checks"
                + f" + {len(default_checks)} defaults)"
            )
        else:
            print(f"Checks: {checks_label} ({len(checks)} checks)")
        print(f"Log:    {logfile}")
        print()
        _print_check_results(violations, unresolved, total_frames, total_checks)

    return _EXIT_VIOLATIONS if violations else _EXIT_OK


# ============================================================================
# Subcommand: mux-query
# ============================================================================

def _resolve_mux_message(args: argparse.Namespace, dbc: DBCDefinition) -> DBCMessage:
    """Resolve the target DBC message for ``mux-query`` from positional args.

    The positional argument accepts either a numeric CAN ID (hex ``0x100`` or
    decimal ``256``) or a message name. Hex is tried first, then decimal, and
    finally a name lookup, so plain hex like ``0x100`` never collides with a
    message that happens to be named ``0x100``.
    """
    ident: str = args.message
    extended: bool = getattr(args, "extended", False)

    try:
        can_id = parse_can_id(ident)
    except ValueError:
        msg = message_by_name(dbc, ident)
        if msg is None:
            _die(f"message not found by id or name: {ident!r}")
        return msg

    by_id = message_by_id(dbc, can_id, extended=extended)
    if by_id is not None:
        return by_id

    id_kind = "extended" if extended else "standard"
    _die(f"CAN ID 0x{can_id:X} ({id_kind}) not found in DBC")


def _print_mux_summary_text(msg: DBCMessage) -> None:
    """Print the multiplex structure of a message in human-readable form."""
    print(f"Message 0x{msg['id']:X} {msg['name']} (DLC {msg['dlc']})")
    print()

    if not is_multiplexed(msg):
        print("  Not multiplexed — all signals are always present.")
        total = len(msg["signals"])
        print(f"  Signals: {total}")
        return

    names = multiplexor_names(msg)
    print(f"  Multiplexors: {', '.join(names) if names else '(none)'}")
    print()

    for mux_name in names:
        values = mux_values(msg, mux_name)
        print(f"  {mux_name}:")
        for v in values:
            sigs = [s["name"] for s in signals_for_mux_value(msg, mux_name, v)]
            print(f"    value {v}: {len(sigs)} signals ({', '.join(sigs)})")
        print()


def _print_mux_selection_text(
    msg: DBCMessage, mux_name: str, value: int, sigs: list[DBCSignal],
) -> None:
    """Print signals active for a specific ``(multiplexor, value)`` selector."""
    print(f"Message 0x{msg['id']:X} {msg['name']} (DLC {msg['dlc']})")
    print(f"Multiplexor {mux_name} = {value}: {len(sigs)} signals present")
    print()
    for sig in sigs:
        print(_format_signal_line(sig))


def _cmd_mux_query(args: argparse.Namespace) -> int:
    """Inspect multiplexor structure of a DBC message."""
    dbc = _load_dbc(args)
    msg = _resolve_mux_message(args, dbc)

    mux_name: str | None = getattr(args, "mux", None)
    value: int | None = getattr(args, "value", None)
    as_json: bool = getattr(args, "json", False)

    if (mux_name is None) != (value is None):
        _die("--mux and --value must be provided together")

    if mux_name is not None and value is not None:
        if mux_name not in multiplexor_names(msg):
            _die(
                f"multiplexor {mux_name!r} not found in message "
                + f"{msg['name']!r} (have: {', '.join(multiplexor_names(msg)) or 'none'})"
            )
        sigs = signals_for_mux_value(msg, mux_name, value)
        if as_json:
            out = {
                "message_id": msg["id"],
                "message_name": msg["name"],
                "multiplexor": mux_name,
                "value": value,
                "signals": [s["name"] for s in sigs],
            }
            print(dump_json(out, indent=2))
        else:
            _print_mux_selection_text(msg, mux_name, value, sigs)
        return _EXIT_OK

    if as_json:
        out = {
            "message_id": msg["id"],
            "message_name": msg["name"],
            "is_multiplexed": is_multiplexed(msg),
            "multiplexors": [
                {
                    "name": name,
                    "values": [
                        {
                            "value": v,
                            "signals": [
                                s["name"]
                                for s in signals_for_mux_value(msg, name, v)
                            ],
                        }
                        for v in mux_values(msg, name)
                    ],
                }
                for name in multiplexor_names(msg)
            ],
        }
        print(dump_json(out, indent=2))
    else:
        _print_mux_summary_text(msg)
    return _EXIT_OK


# ============================================================================
# Argument parser
# ============================================================================

def _build_parser() -> argparse.ArgumentParser:
    """Build the top-level argument parser with subcommands."""
    parser = argparse.ArgumentParser(
        prog="aletheia",
        description="Formally verified CAN signal analysis",
    )
    parser.add_argument(
        "--version", action="version", version=f"%(prog)s {__version__}",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    # -- check ---------------------------------------------------------------
    p_check = subparsers.add_parser(
        "check",
        help="run LTL checks against a CAN log file",
    )
    p_check.add_argument("logfile", help="CAN log file (.asc, .blf, .csv, .db, .log, .mf4, .trc)")
    p_check.add_argument("--dbc", help=".dbc file for signal definitions")
    p_check.add_argument("--checks", help=".yaml or .xlsx file with check definitions")
    p_check.add_argument("--defaults", help=".yaml or .xlsx file with default checks (prepended)")
    p_check.add_argument("--excel", help=".xlsx workbook with DBC + Checks sheets")
    p_check.add_argument("--json", action="store_true", help="output as JSON")

    # -- validate ------------------------------------------------------------
    p_validate = subparsers.add_parser(
        "validate",
        help="validate a DBC definition for structural issues",
    )
    p_validate.add_argument("--dbc", help=".dbc file for signal definitions")
    p_validate.add_argument("--excel", help=".xlsx workbook with DBC sheet")
    p_validate.add_argument("--json", action="store_true", help="output as JSON")

    # -- extract -------------------------------------------------------------
    p_extract = subparsers.add_parser(
        "extract",
        help="decode signals from a single CAN frame",
    )
    p_extract.add_argument("can_id", help="CAN ID (hex 0x100 or decimal 256)")
    p_extract.add_argument("data", help="frame data as hex bytes")
    p_extract.add_argument("--dbc", required=True, help=".dbc or .xlsx file")
    p_extract.add_argument(
        "--extended",
        action="store_true",
        help="treat CAN ID as 29-bit extended (default: 11-bit standard)",
    )
    p_extract.add_argument("--json", action="store_true", help="output as JSON")

    # -- signals -------------------------------------------------------------
    p_signals = subparsers.add_parser(
        "signals",
        help="list signals defined in a DBC file",
    )
    p_signals.add_argument("--dbc", help=".dbc file")
    p_signals.add_argument("--excel", help=".xlsx workbook with DBC sheet")
    p_signals.add_argument("--json", action="store_true", help="output as JSON")

    # -- mux-query -----------------------------------------------------------
    p_mux = subparsers.add_parser(
        "mux-query",
        help="inspect multiplexor structure of a DBC message",
    )
    p_mux.add_argument(
        "message",
        help="message CAN ID (hex 0x100 or decimal 256) or message name",
    )
    p_mux.add_argument("--dbc", help=".dbc file")
    p_mux.add_argument("--excel", help=".xlsx workbook with DBC sheet")
    p_mux.add_argument(
        "--extended",
        action="store_true",
        help="treat CAN ID as 29-bit extended (default: 11-bit standard)",
    )
    p_mux.add_argument(
        "--mux",
        help="multiplexor signal name (used with --value to list active signals)",
    )
    p_mux.add_argument(
        "--value",
        type=int,
        help="multiplexor value (used with --mux to list active signals)",
    )
    p_mux.add_argument("--json", action="store_true", help="output as JSON")

    return parser


# ============================================================================
# Entry point
# ============================================================================

_COMMANDS = {
    "check": _cmd_check,
    "extract": _cmd_extract,
    "mux-query": _cmd_mux_query,
    "signals": _cmd_signals,
    "validate": _cmd_validate,
}


def main(argv: list[str] | None = None) -> int:
    """CLI entry point. Returns exit code."""
    parser = _build_parser()

    try:
        args = parser.parse_args(argv)
        handler = _COMMANDS[args.command]
        return handler(args)
    except SystemExit as e:
        return e.code if isinstance(e.code, int) else _EXIT_ERROR
    except (AletheiaError, FileNotFoundError, ValueError) as e:
        print(f"Error: {e}", file=sys.stderr)
        return _EXIT_ERROR
