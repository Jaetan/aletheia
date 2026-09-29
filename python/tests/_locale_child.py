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

import locale
import sys

from aletheia import AletheiaClient, ValidationError, from_decimal
from aletheia.common_types import ExitStatus, Prose

SENTINEL = "ALETHEIA_LOCALE_OK"

# One message whose signal has the unit "°C": the text reaches the kernel as
# UTF-8 and the unit comes back in the kernel's response.
DBC_TEXT = (
    'VERSION "1.0"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n'
    'BO_ 256 M: 8 ECU\n SG_ T : 0|16@1+ (1,0) [0|65535] "°C" Vector__XXX\n'
)


def _failures() -> list[Prose]:
    """Run the checks, answering what went wrong, each as one line."""
    ctype = locale.setlocale(locale.LC_CTYPE)
    if ctype != "C":
        return [Prose(f"the child runs under LC_CTYPE {ctype!r}, not C, so it proves nothing")]
    failures: list[Prose] = []
    with AletheiaClient() as client:
        try:
            value = from_decimal("1.5€")
        except ValidationError:
            pass
        else:
            failures.append(Prose(f"from_decimal accepted 1.5 and a euro sign as {value}"))
        response = client.parse_dbc_text(DBC_TEXT)
        if response["status"] != "success":
            failures.append(Prose(f"parse_dbc_text refused the DBC: {response}"))
        elif (unit := response["dbc"]["messages"][0]["signals"][0]["unit"]) != "°C":
            failures.append(Prose(f"the unit came back as {unit!r}"))
    return failures


def main() -> ExitStatus:
    """Print each failure, or the sentinel when there is none."""
    failures = _failures()
    for line in failures:
        sys.stdout.write(f"{line}\n")
    if failures:
        return ExitStatus(1)
    sys.stdout.write(f"{SENTINEL}\n")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())
