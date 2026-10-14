# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the runtime image to carrying the licence text of every third-party package it ships.

The image is redistributed whole, so each package in it owes its notice there:

* every installed Debian package, its ``/usr/share/doc/<package>/copyright``;
* every installed Python distribution, a licence file among its files (PEP 639
  puts it under its ``.dist-info/licenses/``; older ones ship a ``LICENSE``,
  ``COPYING`` or ``NOTICE`` file in their ``.dist-info``);
* CPython, the ``LICENSE.txt`` of its standard library directory;
* the bundle, a licence text under ``/opt/aletheia/licenses/`` (which texts, the
  dist rule's ``check-bundle`` holds).

It runs inside the image, in the Dockerfile's ``verify-licences`` stage, with
the image's own python3, so it imports the standard library and the image's
installed ``aletheia`` package, nothing from ``tools/``.

Exit 0 when every package carries its text; 1 when one does not, each named;
2 when the Debian package list cannot be read.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import sysconfig
from importlib.metadata import Distribution, distributions
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, NewType

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Iterable

HELD, FOUND, UNCHECKED = ExitStatus(0), ExitStatus(1), ExitStatus(2)

DOC = Path("/usr/share/doc")
BUNDLE_LICENCES = Path("/opt/aletheia/licenses")
DPKG_QUERY = Path("/usr/bin/dpkg-query")

# A Debian package's name, its architecture qualifier aside.
DebPackage = NewType("DebPackage", str)

_LICENCE_FILE = re.compile(r"(?i)^(licen[cs]e|copying|notice)")


def installed(listing: Prose) -> list[DebPackage]:
    """Return the packages a ``dpkg-query`` listing of name and status marks installed (``ii``)."""
    out: list[DebPackage] = []
    for line in listing.splitlines():
        name, _, status = line.partition("\t")
        if status.startswith("ii"):
            out.append(DebPackage(name.split(":")[0]))
    return out


def debian_findings(packages: Iterable[DebPackage], doc: Path) -> list[Prose]:
    """Return a finding per package without its copyright file under ``doc``."""
    return [
        Prose(f"debian package {package}: no {doc / package / 'copyright'}")
        for package in packages
        if not (doc / package / "copyright").is_file()
    ]


def carries_licence(distribution: Distribution) -> bool:
    """Say whether ``distribution`` lists a licence file in its ``.dist-info``."""
    for file in distribution.files or []:
        parts = PurePosixPath(file).parts
        in_info = [i for i, part in enumerate(parts) if part.endswith(".dist-info")]
        if in_info and len(parts) > in_info[0] + 1:
            inner = parts[in_info[0] + 1 :]
            if inner[0] == "licenses" or _LICENCE_FILE.match(inner[-1]):
                return True
    return False


def python_findings(found: Iterable[Distribution]) -> list[Prose]:
    """Return a finding per distribution that lists no licence file."""
    return [
        Prose(f"python distribution {dist.metadata['Name']} {dist.version}: no licence file")
        for dist in found
        if not carries_licence(dist)
    ]


def file_findings(cpython: Path, bundle: Path) -> list[Prose]:
    """Return a finding when CPython's licence or the bundle's licence texts are absent."""
    out: list[Prose] = []
    if not cpython.is_file():
        out.append(Prose(f"cpython: no {cpython}"))
    if not (bundle.is_dir() and any(path.is_file() for path in bundle.glob("*/*"))):
        out.append(Prose(f"bundle: no licence text under {bundle}"))
    return out


def main() -> ExitStatus:
    """Report every package the image ships without its licence text."""
    _ = argparse.ArgumentParser(
        description="Hold the runtime image to carrying every package's licence text."
    ).parse_args()
    read = subprocess.run(
        [str(DPKG_QUERY), "-W", "-f", "${Package}\t${db:Status-Abbrev}\n"],
        capture_output=True,
        text=True,
        check=False,
    )
    if read.returncode != 0:
        _ = sys.stdout.write(f"image-licences: dpkg-query failed: {read.stderr.strip()}\n")
        return UNCHECKED
    packages = installed(Prose(read.stdout))
    found = [
        *debian_findings(packages, DOC),
        *python_findings(distributions()),
        *file_findings(Path(sysconfig.get_path("stdlib")) / "LICENSE.txt", BUNDLE_LICENCES),
    ]
    for finding in found:
        _ = sys.stdout.write(f"image-licences: {finding}\n")
    if found:
        return FOUND
    _ = sys.stdout.write(
        f"image-licences: each of {len(packages)} Debian packages, every Python "
        + "distribution, CPython and the bundle carries its licence text\n"
    )
    return HELD


if __name__ == "__main__":
    sys.exit(main())
