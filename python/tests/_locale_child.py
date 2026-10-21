# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The child process ``test_ffi_strings`` runs under the C locale.

The GHC runtime reads the locale once, when it starts, so the claim that the
kernel's strings do not depend on it is checked in a process of its own.  The
parent sets ``LC_ALL=C``, the one setting Python does not coerce to UTF-8
(PEP 538); this child refuses to vouch for anything unless its ``LC_CTYPE`` is
``C``, then sends non-ASCII text through the kernel in both directions and
prints the sentinel last, so the parent can tell a child that ran every check
from one that stopped early.
"""

from __future__ import annotations

import argparse
import json
import locale
import sys

from aletheia import AletheiaClient, FFIBackend, ValidationError, from_decimal
from aletheia.codes import ErrorCode
from aletheia.common_types import ExitStatus, Prose

SENTINEL = "ALETHEIA_LOCALE_OK"

# One message whose signal has the unit "°C": the text reaches the kernel as
# UTF-8, and the kernel refuses the degree sign, outside the DBC character
# set, at its line and column.
DBC_TEXT = (
    'VERSION "1.0"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n'
    'BO_ 256 M: 8 ECU\n SG_ T : 0|16@1+ (1,0) [0|65535] "°C" Vector__XXX\n'
)

# A message whose type is the two characters "°C": the kernel echoes them
# whole in its refusal, so non-ASCII text crosses the kernel both ways.
RAW_COMMAND = b'{"type": "\xc2\xb0C"}'


def _failures() -> list[Prose]:
    """Run the checks, answering what went wrong, each as one line."""
    ctype = locale.setlocale(locale.LC_CTYPE)
    if ctype != "C":
        return [Prose(f"the child runs under LC_CTYPE {ctype!r}, not C, so it proves nothing")]
    failures: list[Prose] = []
    with AletheiaClient() as client:
        # The euro sign reaches the kernel as UTF-8, so the kernel reads it and
        # stops in front of it: a trailing-input refusal, not a UTF-8 one.
        try:
            value = from_decimal("1.5€")
        except ValidationError as exc:
            if exc.code != ErrorCode.TEXT_TRAILING_INPUT:
                failures.append(Prose(f"from_decimal refused 1.5 and a euro sign as {exc.code}"))
        else:
            failures.append(Prose(f"from_decimal accepted 1.5 and a euro sign as {value}"))
        response = client.parse_dbc_text(DBC_TEXT)
        if (
            response["status"] != "error"
            or response["code"] != ErrorCode.DBC_INVALID_CHARACTER
            or "line 10, column 35 (code point 176)" not in response["message"]
        ):
            failures.append(Prose(f"parse_dbc_text answered the degree sign with {response}"))
    backend = FFIBackend()
    state = backend.init()
    try:
        echoed = json.loads(backend.process(state, RAW_COMMAND))
    finally:
        backend.close(state)
    if echoed["message"] != "unknown message type '°C'":
        failures.append(Prose(f"the degree sign came back as {echoed}"))
    return failures


def main() -> ExitStatus:
    """Print each failure, or the sentinel when there is none."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    failures = _failures()
    for line in failures:
        sys.stdout.write(f"{line}\n")
    if failures:
        return ExitStatus(1)
    sys.stdout.write(f"{SENTINEL}\n")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())
