"""Command-line interface for Aletheia CAN signal verification

Subcommands:
    check    — run LTL checks against a CAN log file
    extract  — decode signals from a single CAN frame
    signals  — list all signals defined in a DBC file
    validate — validate a DBC definition for structural issues

Usage:
    python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
    python -m aletheia extract --dbc vehicle.dbc 0x100 401F7D0000000000
    python -m aletheia signals --dbc vehicle.dbc
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import NoReturn, TypedDict

from .can_log import iter_can_log
from .checks import CheckResult
from .client import AletheiaClient, AletheiaError, SignalExtractionResult
from .dbc_converter import dbc_to_json
from .excel_loader import load_checks_from_excel, load_dbc_from_excel
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
from .yaml_loader import load_checks


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
    actual_value: float | None
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
        raise ValueError(f"invalid CAN ID: {s!r}") from exc


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
        raise ValueError(f"hex data has odd number of characters: {s!r}")
    try:
        return bytearray.fromhex(cleaned)
    except ValueError as exc:
        raise ValueError(f"invalid hex data: {s!r}") from exc


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
            return load_dbc_from_excel(p)
        return dbc_to_json(p)

    if excel_path is not None:
        p = Path(excel_path)
        if not p.exists():
            _die(f"Excel file not found: {excel_path}")
        return load_dbc_from_excel(p)

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
            results.extend(load_checks_from_excel(p))
        else:
            results.extend(load_checks(p))

    if excel_path is not None and checks_path is None:
        p = Path(excel_path)
        if not p.exists():
            _die(f"Excel file not found: {excel_path}")
        results.extend(load_checks_from_excel(p))

    if not results:
        _die("no checks specified (use --checks or --excel)")

    return results


def _find_message(dbc: DBCDefinition, can_id: int) -> DBCMessage | None:
    """Find a message by CAN ID in a DBC definition."""
    for msg in dbc["messages"]:
        if msg["id"] == can_id:
            return msg
    return None


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

    offset_str = f"+{offset}" if offset >= 0 else str(offset)
    range_str = f"[{minimum}, {maximum}]" if minimum != 0 or maximum != 0 else ""

    return (
        f"  {name:<20s} bits[{start}:{length}]"
        + f"   {order}  {sign:<10s}"
        + f"  x{factor} {offset_str}"
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
        print(json.dumps(dbc, indent=2))
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
        print(json.dumps(out, indent=2))
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
            print(f"  {name:<20s} = {value}{unit_part}")
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

    # Look up expected DLC from the DBC message definition
    msg = _find_message(dbc, can_id)
    if msg is None:
        _die(f"CAN ID 0x{can_id:X} not found in DBC")
    if len(data) != msg["dlc"]:
        _die(
            f"data length ({len(data)} bytes) does not match "
            + f"DBC message DLC ({msg['dlc']} bytes)"
        )

    with AletheiaClient() as client:
        resp = client.parse_dbc(dbc)
        if resp["status"] != "success":
            _die(f"DBC parse failed: {resp.get('message', 'unknown error')}")
        result = client.extract_signals(can_id=can_id, dlc=msg["dlc"], data=data)

    if getattr(args, "json", False):
        out = {
            "can_id": can_id,
            "values": result.values,
            "errors": result.errors,
            "absent": result.absent,
        }
        print(json.dumps(out, indent=2))
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

    reason = response.get("enriched_reason", response.get("reason", ""))
    signals = response.get("signals", {})
    # Pick first signal for single-line violation display
    signal_name = ""
    actual_value: float | None = None
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
        "condition": response.get("formula", ""),
    }


def _build_eos_violation(
    result: PropertyResultEntry, checks: list[CheckResult],
) -> _Violation:
    """Extract violation details from an end-of-stream finalization result."""
    prop_index = rational_to_int(result["property_index"])
    check_name, severity = _check_meta(prop_index, checks)

    reason = result.get("enriched_reason", result.get("reason", "end-of-stream violation"))

    return {
        "check_index": prop_index,
        "check_name": check_name,
        "severity": severity,
        "timestamp_us": 0,  # End-of-stream has no specific timestamp
        "reason": reason,
        "signal_name": "",
        "actual_value": None,
        "condition": result.get("formula", ""),
    }


def _run_checks(  # pylint: disable=too-many-locals
    dbc: DBCDefinition,
    checks: list[CheckResult],
    logfile: str,
    default_checks: list[CheckResult] | None = None,
) -> tuple[list[_Violation], int]:
    """Stream a CAN log through the Aletheia engine.

    Returns (violations, total_frames).
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
        total_frames = 0

        for ts, can_id, dlc, data in iter_can_log(logfile):
            total_frames += 1
            response = client.send_frame(ts, can_id, dlc, data)
            if response["status"] == "fails":
                violations.append(_build_violation(response, all_checks))

        end_resp = client.end_stream()
        if end_resp["status"] == "error":
            _die(f"end stream failed: {end_resp['message']}")
        # Collect end-of-stream violations from finalization
        for result in end_resp["results"]:
            if result["status"] == "fails":
                violations.append(_build_eos_violation(result, all_checks))

    return violations, total_frames


def _print_check_results(
    violations: list[_Violation],
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
    else:
        print("RESULT: all checks passed")
        print()

    print(
        f"Summary: {len(violations)} violations in {num_checks} checks, "
        + f"{total_frames} frames processed"
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
        return load_checks_from_excel(p)
    return load_checks(p)


def _cmd_check(args: argparse.Namespace) -> int:
    """Run LTL checks against a CAN log file."""
    dbc = _load_dbc(args)
    checks = _load_checks_from_args(args)
    default_checks = _load_defaults(args)
    logfile: str = args.logfile

    if not Path(logfile).exists():
        _die(f"log file not found: {logfile}")

    violations, total_frames = _run_checks(dbc, checks, logfile, default_checks)

    if getattr(args, "json", False):
        status = "pass" if not violations else "violations"
        out = {
            "status": status,
            "total_frames": total_frames,
            "total_violations": len(violations),
            "violations": violations,
        }
        print(json.dumps(out, indent=2))
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
        _print_check_results(violations, total_frames, total_checks)

    return _EXIT_VIOLATIONS if violations else _EXIT_OK


# ============================================================================
# Argument parser
# ============================================================================

def _build_parser() -> argparse.ArgumentParser:
    """Build the top-level argument parser with subcommands."""
    parser = argparse.ArgumentParser(
        prog="aletheia",
        description="Formally verified CAN signal analysis",
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
    p_extract.add_argument("--json", action="store_true", help="output as JSON")

    # -- signals -------------------------------------------------------------
    p_signals = subparsers.add_parser(
        "signals",
        help="list signals defined in a DBC file",
    )
    p_signals.add_argument("--dbc", help=".dbc file")
    p_signals.add_argument("--excel", help=".xlsx workbook with DBC sheet")
    p_signals.add_argument("--json", action="store_true", help="output as JSON")

    return parser


# ============================================================================
# Entry point
# ============================================================================

_COMMANDS = {
    "check": _cmd_check,
    "extract": _cmd_extract,
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
