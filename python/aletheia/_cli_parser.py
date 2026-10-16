# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The command line's grammar: the ``aletheia`` parser and one subparser per subcommand.

``aletheia.cli`` parses with it and dispatches; nothing here reads a file or a library.
"""

from __future__ import annotations

import argparse

from aletheia import __version__


def build_parser() -> argparse.ArgumentParser:
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

    # -- template ------------------------------------------------------------
    p_template = subparsers.add_parser(
        "template",
        help="write a blank Excel workbook to fill in with a DBC and checks",
    )
    p_template.add_argument("path", help=".xlsx file to create; an existing file is refused")

    return parser
