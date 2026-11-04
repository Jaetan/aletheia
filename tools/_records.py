# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Where run records live: the one reading every tool, test and probe takes of the place.

A sweep's logs, a probe run's logs and every other record a run keeps lie in
one place outside the checkout, where no gate that lists the tree reads them
and no clean of the tree removes them.  ``ALETHEIA_CI_OUTPUT`` names the place
when it is set, and must name it by an absolute path outside the checkout: a
relative one would name a different directory from each place a tool runs in,
and one inside the checkout would be listed with the tree, so either is
refused.  Unset, the place is ``aletheia-ci-output`` beside the checkout, shared
by every checkout in the same parent directory.  Each checkout's probe runs keep
their record in ``probes/<the checkout directory's name>`` there, a folder of
their own among checkouts of distinct directory names.

Usage::

    python/.venv/bin/python -m tools._records           # this checkout's records directory
    python/.venv/bin/python -m tools._records probes    # the folder of its probe records

Exit 0 with the path on stdout, or 2 with the reason on stderr and nothing on
stdout, when git names no checkout or the variable names a relative path or
a place inside the checkout.
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Literal, cast

from tools._common import EnvName, EnvValue, emit, git_toplevel

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Mapping

# The variable naming the records directory, and the directory's name beside
# the checkout when it is unset.
RECORDS_ENV = EnvName("ALETHEIA_CI_OUTPUT")
_BESIDE_THE_CHECKOUT = "aletheia-ci-output"
# The folder in it holding a folder of probe records per checkout, and the word
# the command takes to print the checkout's folder.
_PROBES = "probes"
_Word = Literal["probes"]

PRINTED, UNNAMED = ExitStatus(0), ExitStatus(2)


class UnusableRecordsDirError(ValueError):
    """``ALETHEIA_CI_OUTPUT`` names a relative path or a place inside the checkout."""


def environment() -> dict[EnvName, EnvValue]:
    """Return this process's environment, each name and value typed as one."""
    return {EnvName(name): EnvValue(value) for name, value in os.environ.items()}


def records_dir(repo: Path, environ: Mapping[EnvName, EnvValue]) -> Path:
    """Return the directory run records of the checkout at ``repo`` live in.

    ``repo`` is the checkout's absolute root.  Raises ``UnusableRecordsDirError``
    when ``environ`` sets ``ALETHEIA_CI_OUTPUT`` to a relative path, the empty
    one included, or to a place inside the checkout, the checkout itself
    included, as the place resolves through links and ``..``.
    """
    value = environ.get(RECORDS_ENV)
    if value is None:
        return repo.parent / _BESIDE_THE_CHECKOUT
    place = Path(value)
    if not place.is_absolute():
        message = f"{RECORDS_ENV} names {value!r}, a relative path; it must name an absolute one"
        raise UnusableRecordsDirError(message)
    if place.resolve().is_relative_to(repo.resolve()):
        message = (
            f"{RECORDS_ENV} names {value!r}, inside the checkout {repo};"
            + " it must name a place outside it"
        )
        raise UnusableRecordsDirError(message)
    return place


def probe_records(repo: Path, environ: Mapping[EnvName, EnvValue]) -> Path:
    """Return the folder the probe runs of the checkout at ``repo`` keep their record in.

    It is ``probes/<the checkout directory's name>`` under the records directory, so
    checkouts of distinct directory names sharing it keep apart records.  Raises as
    ``records_dir`` does.
    """
    return records_dir(repo, environ) / _PROBES / repo.name


def main() -> ExitStatus:
    """Print the records directory of the checkout this runs in, or its probe records folder."""
    parser = argparse.ArgumentParser(description="Print where this checkout's run records live.")
    _ = parser.add_argument(
        "what",
        nargs="?",
        choices=(_PROBES,),
        help="probes: print the folder this checkout's probe runs keep their record in",
    )
    what = cast("_Word | None", parser.parse_args().what)
    name = records_dir if what is None else probe_records
    try:
        place = name(git_toplevel(Path.cwd()), environment())
    except (RuntimeError, UnusableRecordsDirError) as exc:
        _ = sys.stderr.write(f"records: {exc}\n")
        return UNNAMED
    emit(str(place))
    return PRINTED


if __name__ == "__main__":
    sys.exit(main())
