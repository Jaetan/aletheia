# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Command-line interface for Aletheia CAN signal verification.

Subcommands:
    check      — run LTL checks against a CAN log file
    validate   — validate a DBC definition for structural issues
    extract    — decode signals from a single CAN frame
    signals    — list all signals defined in a DBC file
    format-dbc — re-export a DBC as canonical JSON via the Agda core
    mux-query  — inspect multiplexor structure of a DBC message

Usage:
    python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
    python -m aletheia extract --dbc vehicle.dbc 0x100 401F7D0000000000
    python -m aletheia signals --dbc vehicle.dbc
    python -m aletheia format-dbc --dbc vehicle.dbc
    python -m aletheia mux-query --dbc vehicle.dbc 0x100
    python -m aletheia mux-query --dbc vehicle.dbc 0x100 --mux Mode --value 5
"""

from __future__ import annotations

import argparse
import importlib
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NoReturn, cast

from aletheia import __version__
from aletheia._time_units import MICROSECONDS_PER_MILLISECOND
from aletheia.checks_runner import CheckRunResult, Violation, run_checks
from aletheia.client._client import AletheiaClient
from aletheia.client._types import (
    AletheiaError,
    SignalExtractionResult,
    ValidationError,
    bytes_to_dlc,
)
from aletheia.dbc import (
    is_multiplexed,
    message_by_id,
    message_by_name,
    multiplexor_names,
    mux_values,
    signals_for_mux_value,
)
from aletheia.issue_codes import IssueSeverity, ValidationIssue
from aletheia.protocols import (
    DBCDefinition,
    DBCMessage,
    DBCSignal,
    dump_json,
)

if TYPE_CHECKING:
    # Type-only imports for the lazy helpers below — these are not available
    # at runtime when the corresponding optional dependency is not installed.
    from collections.abc import Callable

    from aletheia.checks import CheckResult


# Optional-dependency loaders: each CLI helper resolves its target via
# ``importlib.import_module`` at the point of use so that subcommands whose
# code paths don't need a given optional package (e.g. ``aletheia signals
# --dbc foo.json`` needs no python-can) can still run without the
# corresponding extras installed. Using ``importlib`` (rather than a
# function-scoped ``from .X import Y``) keeps pylint's
# ``import-outside-toplevel`` check happy without suppressions.
def _lazy_dbc_to_json() -> Callable[[str | Path], DBCDefinition]:
    mod = importlib.import_module(".dbc", __package__)
    return cast("Callable[[str | Path], DBCDefinition]", mod.dbc_to_json)


def _lazy_load_dbc_from_excel() -> Callable[[str | Path], DBCDefinition]:
    mod = importlib.import_module(".excel_loader", __package__)
    return cast("Callable[[str | Path], DBCDefinition]", mod.load_dbc_from_excel)


def _lazy_load_checks_from_excel() -> Callable[[str | Path], list[CheckResult]]:
    mod = importlib.import_module(".excel_loader", __package__)
    return cast("Callable[[str | Path], list[CheckResult]]", mod.load_checks_from_excel)


def _lazy_load_yaml_checks() -> Callable[[str | Path], list[CheckResult]]:
    mod = importlib.import_module(".yaml_loader", __package__)
    return cast("Callable[[str | Path], list[CheckResult]]", mod.load_checks)


# ============================================================================
# Exit codes
# ============================================================================

_EXIT_OK = 0
_EXIT_VIOLATIONS = 1
_EXIT_ERROR = 2


# ============================================================================
# Helpers
# ============================================================================


def _emit(text: str = "") -> None:
    """Write a single line to stdout (CLI text output channel).

    Routes through ``sys.stdout.write`` so the static gate (ruff T201)
    treats this as the single sanctioned text-output entry-point.  All
    human-readable CLI output flows through this helper.
    """
    sys.stdout.write(f"{text}\n")


def _die(msg: str) -> NoReturn:
    """Write an error to stderr and exit with code 2.

    CLI-layer only: library callers must catch the underlying exception
    (``AletheiaError`` and its subclasses) and decide their own exit
    behaviour.  Call this strictly from ``cli.py`` argv-handling code,
    never from ``python/aletheia/`` library modules — the CLI sits on
    top of the library, not the other way round.
    """
    sys.stderr.write(f"Error: {msg}\n")
    sys.exit(_EXIT_ERROR)


def _require_existing_path(p: Path, label: str, source: str) -> None:
    """Exit with code 2 if path *p* does not exist."""
    if not p.exists():
        _die(f"{label} not found: {source}")


def parse_can_id(s: str) -> int:
    """Parse a CAN ID from hex (0x100) or decimal (256) string.

    Raises:
        ValidationError: If *s* is not a valid integer.

    """
    s = s.strip()
    try:
        if s.lower().startswith("0x"):
            return int(s, 16)
        return int(s)
    except ValueError as exc:
        msg = f"Invalid CAN ID: {s!r}"
        raise ValidationError(msg) from exc


def parse_hex_data(s: str) -> bytearray:
    """Parse hex data string into a bytearray.

    Accepts:
        "401F7D0000000000"
        "40 1F 7D 00 00 00 00 00"
        "40:1F:7D:00:00:00:00:00"

    Raises:
        ValidationError: If *s* contains non-hex characters or has odd length.

    """
    cleaned = s.replace(" ", "").replace(":", "")
    if cleaned.lower().startswith("0x"):
        cleaned = cleaned[2:]
    if len(cleaned) % 2 != 0:
        msg = f"Hex data has odd number of characters: {s!r}"
        raise ValidationError(msg)
    try:
        return bytearray.fromhex(cleaned)
    except ValueError as exc:
        msg = f"Invalid hex data: {s!r}"
        raise ValidationError(msg) from exc


def format_timestamp(us: int) -> str:
    """Format microseconds as a human-readable timestamp.

    Returns "1234.500ms" for 1234500 us.
    """
    ms = us / MICROSECONDS_PER_MILLISECOND
    return f"{ms:.3f}ms"


def _load_dbc(args: argparse.Namespace) -> DBCDefinition:
    """Load a DBC definition from the parsed CLI namespace.

    Dispatches on which of ``--dbc`` / ``--excel`` is set.  Excel
    workbooks are routed through :func:`load_dbc_from_excel`; ``.dbc``
    text files are parsed by :func:`dbc_to_json`.  Calls :func:`_die`
    (exit code 2) when neither flag is set or the named path does not
    exist — no exception escapes back to the caller.
    """
    dbc_path: str | None = getattr(args, "dbc", None)
    excel_path: str | None = getattr(args, "excel", None)

    if dbc_path is not None:
        p = Path(dbc_path)
        _require_existing_path(p, "DBC file", dbc_path)
        if p.suffix == ".xlsx":
            return _lazy_load_dbc_from_excel()(p)
        return _lazy_dbc_to_json()(p)

    if excel_path is not None:
        p = Path(excel_path)
        _require_existing_path(p, "Excel file", excel_path)
        return _lazy_load_dbc_from_excel()(p)

    _die("no DBC source specified (use --dbc or --excel)")


def _load_checks_from_args(args: argparse.Namespace) -> list[CheckResult]:
    """Load checks from --checks or --excel flag."""
    checks_path: str | None = getattr(args, "checks", None)
    excel_path: str | None = getattr(args, "excel", None)

    results: list[CheckResult] = []

    if checks_path is not None:
        p = Path(checks_path)
        _require_existing_path(p, "checks file", checks_path)
        if p.suffix == ".xlsx":
            results.extend(_lazy_load_checks_from_excel()(p))
        else:
            results.extend(_lazy_load_yaml_checks()(p))

    if excel_path is not None and checks_path is None:
        p = Path(excel_path)
        _require_existing_path(p, "Excel file", excel_path)
        results.extend(_lazy_load_checks_from_excel()(p))

    if not results:
        _die("no checks specified (use --checks or --excel)")

    return results


def _find_message(
    dbc: DBCDefinition,
    can_id: int,
    *,
    extended: bool = False,
) -> DBCMessage | None:
    """Find a message by CAN ID + extended flag in a DBC definition.

    Delegates to ``message_by_id`` from ``aletheia.dbc``.
    """
    return message_by_id(dbc, can_id, extended=extended)


def _signal_units(msg: DBCMessage) -> dict[str, str]:
    """Extract signal name → unit mapping from a DBC message."""
    return {sig["name"]: sig["unit"] for sig in msg["signals"]}


# ============================================================================
# Subcommand —signals
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
        _emit(f"Message 0x{msg['id']:X} {msg['name']} (DLC {msg['dlc']}{sender_part})")

        for sig in msg["signals"]:
            total_signals += 1
            _emit(_format_signal_line(sig))

        _emit()

    _emit(f"{len(messages)} messages, {total_signals} signals")


def _cmd_signals(args: argparse.Namespace) -> int:
    """List signals defined in a DBC file."""
    dbc = _load_dbc(args)

    if getattr(args, "json", False):
        _emit(dump_json(dbc, indent=2))
    else:
        _print_signals_text(dbc)

    return _EXIT_OK


# ============================================================================
# Subcommand —validate
# ============================================================================


def _print_validation_text(issues: list[ValidationIssue], *, has_errors: bool) -> None:
    """Print validation issues in human-readable text format."""
    if not issues:
        _emit("Validation passed: no issues found")
        return

    errors = [i for i in issues if i["severity"] == IssueSeverity.ERROR]
    warnings = [i for i in issues if i["severity"] == IssueSeverity.WARNING]

    if has_errors:
        _emit(f"Validation FAILED: {len(errors)} errors, {len(warnings)} warnings")
    else:
        _emit(f"Validation passed with {len(warnings)} warnings")
    _emit()

    for i, issue in enumerate(issues, 1):
        sev = issue["severity"].upper()
        code = issue["code"]
        detail = issue["detail"]
        _emit(f"  {i}. [{sev}] {code}: {detail}")

    _emit()


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
        _emit(dump_json(out, indent=2))
    else:
        _print_validation_text(issues, has_errors=has_errors)

    return _EXIT_VIOLATIONS if has_errors else _EXIT_OK


# ============================================================================
# Subcommand —extract
# ============================================================================


def _print_extract_text(
    can_id: int,
    dbc: DBCDefinition,
    result: SignalExtractionResult,
) -> None:
    """Print extraction results in human-readable text format."""
    msg = _find_message(dbc, can_id)
    units = _signal_units(msg) if msg is not None else {}

    name_part = f" ({msg['name']})" if msg is not None else ""
    _emit(f"CAN ID 0x{can_id:X}{name_part}:")
    _emit()

    if result.values:
        for name, value in result.values.items():
            unit = units.get(name, "")
            unit_part = f" {unit}" if unit else ""
            _emit(f"  {name:<20s} = {value:g}{unit_part}")
    else:
        _emit("  (no signals)")

    _emit()
    _print_extract_errors(result)


def _print_extract_errors(result: SignalExtractionResult) -> None:
    """Print extraction error/absent sections."""
    if result.errors:
        _emit("Errors:")
        for name, err in result.errors.items():
            _emit(f"  {name}: {err}")
    else:
        _emit("Errors: none")

    if result.absent:
        _emit(f"Absent: {', '.join(result.absent)}")
    else:
        _emit("Absent: none")


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
    # ``msg["dlc"]`` is the payload byte count (DBC convention), not the
    # raw DLC code — no conversion needed.  Going through
    # ``dlc_to_bytes(byte_count)`` would raise ``ValueError`` for CAN-FD
    # byte counts > 8, since 12/16/... are not valid DLC codes.
    expected_bytes = msg["dlc"]
    if len(data) != expected_bytes:
        _die(
            f"data length ({len(data)} bytes) does not match "
            + f"DBC message DLC ({msg['dlc']} bytes)"
        )

    with AletheiaClient() as client:
        resp = client.parse_dbc(dbc)
        if resp["status"] != "success":
            _die(f"DBC parse failed: {resp.get('message', 'unknown error')}")
        # ``extract_signals`` takes the DLC code (CAN frame wire convention),
        # not the byte count; convert via ``bytes_to_dlc``.
        result = client.extract_signals(
            can_id=can_id,
            dlc=bytes_to_dlc(msg["dlc"]),
            data=data,
            extended=extended,
        )

    if getattr(args, "json", False):
        out = {
            "can_id": can_id,
            "extended": extended,
            "values": dict(result.values),
            "errors": dict(result.errors),
            "absent": result.absent,
        }
        _emit(dump_json(out, indent=2))
    else:
        _print_extract_text(can_id, dbc, result)

    return _EXIT_OK


# ============================================================================
# Subcommand —check
# ============================================================================


def _print_check_results(result: CheckRunResult, num_checks: int) -> None:
    """Print check results in human-readable text format."""
    violations = result.violations
    unresolved = result.unresolved
    total_frames = result.total_frames
    _emit(f"Streaming {total_frames} frames...")
    _emit()

    if violations:
        _emit(f"RESULT: {len(violations)} violations found")
        _emit()
        for i, v in enumerate(violations, 1):
            _print_violation(i, v)
    elif unresolved:
        _emit(f"RESULT: no violations, {len(unresolved)} unresolved")
        _emit()
    else:
        _emit("RESULT: all checks passed")
        _emit()

    if unresolved:
        _emit(f"Unresolved ({len(unresolved)} — signal never observed or verdict Unknown):")
        for i, v in enumerate(unresolved, 1):
            _print_violation(i, v)

    _emit(
        f"Summary: {len(violations)} violations, {len(unresolved)} unresolved "
        + f"in {num_checks} checks, {total_frames} frames processed"
    )


def _print_violation(index: int, v: Violation) -> None:
    """Print a single violation entry."""
    sev_part = f" ({v['severity']})" if v["severity"] else ""
    ts_str = format_timestamp(v["timestamp_us"])
    _emit(f"  {index}. [t={ts_str}] {v['check_name']}{sev_part}")
    if v["reason"]:
        _emit(f"     {v['reason']}")
    _emit()


def _load_defaults(args: argparse.Namespace) -> list[CheckResult]:
    """Load default checks from --defaults flag, if provided."""
    defaults_path: str | None = getattr(args, "defaults", None)
    if defaults_path is None:
        return []
    p = Path(defaults_path)
    _require_existing_path(p, "defaults file", defaults_path)
    if p.suffix == ".xlsx":
        return _lazy_load_checks_from_excel()(p)
    return _lazy_load_yaml_checks()(p)


def _cmd_check(args: argparse.Namespace) -> int:
    """Run LTL checks against a CAN log file."""
    dbc = _load_dbc(args)
    checks = _load_checks_from_args(args)
    default_checks = _load_defaults(args)
    logfile: str = args.logfile

    try:
        result = run_checks(dbc, checks, logfile, default_checks)
    except (FileNotFoundError, AletheiaError) as exc:
        _die(str(exc))

    violations = result.violations
    unresolved = result.unresolved
    total_frames = result.total_frames

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
        _emit(dump_json(out, indent=2))
    else:
        dbc_label = getattr(args, "dbc", None) or getattr(args, "excel", None) or "?"
        checks_label = getattr(args, "checks", None) or getattr(args, "excel", None) or "?"
        total_checks = len(default_checks) + len(checks)
        _emit("Aletheia — CAN Signal Verification")
        _emit()
        _emit(f"DBC:    {dbc_label}")
        if default_checks:
            _emit(
                f"Checks: {checks_label} ({len(checks)} checks"
                + f" + {len(default_checks)} defaults)"
            )
        else:
            _emit(f"Checks: {checks_label} ({len(checks)} checks)")
        _emit(f"Log:    {logfile}")
        _emit()
        _print_check_results(result, total_checks)

    return _EXIT_VIOLATIONS if violations else _EXIT_OK


# ============================================================================
# Subcommand —mux-query
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
    except ValidationError:
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
    _emit(f"Message 0x{msg['id']:X} {msg['name']} (DLC {msg['dlc']})")
    _emit()

    if not is_multiplexed(msg):
        _emit("  Not multiplexed — all signals are always present.")
        total = len(msg["signals"])
        _emit(f"  Signals: {total}")
        return

    names = multiplexor_names(msg)
    _emit(f"  Multiplexors: {', '.join(names) if names else '(none)'}")
    _emit()

    for mux_name in names:
        values = mux_values(msg, mux_name)
        _emit(f"  {mux_name}:")
        for v in values:
            sigs = [s["name"] for s in signals_for_mux_value(msg, mux_name, v)]
            _emit(f"    value {v}: {len(sigs)} signals ({', '.join(sigs)})")
        _emit()


def _print_mux_selection_text(
    msg: DBCMessage,
    mux_name: str,
    value: int,
    sigs: list[DBCSignal],
) -> None:
    """Print signals active for a specific ``(multiplexor, value)`` selector."""
    _emit(f"Message 0x{msg['id']:X} {msg['name']} (DLC {msg['dlc']})")
    _emit(f"Multiplexor {mux_name} = {value}: {len(sigs)} signals present")
    _emit()
    for sig in sigs:
        _emit(_format_signal_line(sig))


def _cmd_format_dbc(args: argparse.Namespace) -> int:
    """Round-trip a DBC through the Agda core and emit the canonical JSON form.

    Equivalent to ``AletheiaClient.format_dbc()``: loads the DBC from the
    requested source (``--dbc`` or ``--excel``), parses it through the
    FFI, then re-exports it via ``aletheia_format_dbc``. This produces a
    normalized DBC JSON where numeric fields are exact rationals
    matching the Agda core's representation.
    """
    dbc = _load_dbc(args)
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        canonical = client.format_dbc()
    _emit(dump_json(canonical, indent=2))
    return _EXIT_OK


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
            _emit(dump_json(out, indent=2))
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
                            "signals": [s["name"] for s in signals_for_mux_value(msg, name, v)],
                        }
                        for v in mux_values(msg, name)
                    ],
                }
                for name in multiplexor_names(msg)
            ],
        }
        _emit(dump_json(out, indent=2))
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
        "--version",
        action="version",
        version=f"%(prog)s {__version__}",
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

    # -- format-dbc ----------------------------------------------------------
    p_format = subparsers.add_parser(
        "format-dbc",
        help="re-export a DBC as canonical JSON via the Agda core",
    )
    p_format.add_argument("--dbc", help=".dbc file")
    p_format.add_argument("--excel", help=".xlsx workbook with DBC sheet")

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
    "format-dbc": _cmd_format_dbc,
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
        sys.stderr.write(f"Error: {e}\n")
        return _EXIT_ERROR
