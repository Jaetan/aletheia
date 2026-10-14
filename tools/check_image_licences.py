# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the runtime image to carrying the licence text of every third-party package it ships.

The image is redistributed whole, so each package in it owes its notice there:

* every Debian package with its files on disk (any state but not-installed and
  config-files), its ``/usr/share/doc/<package>/copyright``;
* every installed Python distribution, a non-empty licence file in its
  ``.dist-info`` (PEP 639 puts them under ``licenses/``; older ones ship a
  ``LICENSE`` or ``COPYING`` there; a ``NOTICE`` alone is no licence), and one
  for each package it vendors under a ``_vendor/`` directory, which pip lists
  under its ``licenses/src/pip/_vendor/<package>/`` and setuptools keeps in the
  vendored package's own ``.dist-info`` beside it;
* CPython, the ``LICENSE.txt`` of its standard library directory, and the
  notices of the software it compiles in (the incorporated-software section of
  its licence document, and HACL*'s notice) under
  ``/usr/local/share/licenses/cpython-<version>/``, which the image copies from
  the tree for its CPython version;
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
import platform
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
    from importlib.metadata import PackagePath

HELD, FOUND, UNCHECKED = ExitStatus(0), ExitStatus(1), ExitStatus(2)

DOC = Path("/usr/share/doc")
BUNDLE_LICENCES = Path("/opt/aletheia/licenses")
CPYTHON_NOTICES = Path("/usr/local/share/licenses")
# The texts ``CPYTHON_NOTICES/cpython-<version>/`` holds: the incorporated-software
# section of CPython's licence document, and HACL*'s notice, which it omits.
CPYTHON_TEXTS = (Path("incorporated-software.rst"), Path("LICENSE-hacl-star"))
DPKG_QUERY = Path("/usr/bin/dpkg-query")

# A Debian package's name, its architecture qualifier aside.
DebPackage = NewType("DebPackage", str)
# A package a distribution vendors, by its import name: ``urllib3``.
VendoredPackage = NewType("VendoredPackage", str)
# A CPython version as ``platform.python_version`` gives it: ``3.14.6``.
PythonVersion = NewType("PythonVersion", str)

_LICENCE_FILE = re.compile(r"(?i)^(licen[cs]e|copying)")
_VENDOR = "_vendor"
# How deep a vendored package's ``__init__.py`` sits below ``_vendor/``: ``<package>/__init__.py``.
_PACKAGE_FILE_DEPTH = 2
# The second letter of a dpkg status abbreviation for a package whose files are
# not on disk: not installed, or only its configuration files left.
_FILES_GONE = frozenset({"n", "c"})


def installed(listing: Prose) -> list[DebPackage]:
    """Return the packages a ``dpkg-query`` listing of name and status leaves files of on disk.

    Every state but not-installed and config-files keeps the package's files:
    held, unpacked, half-configured and trigger-pending packages owe their
    copyright as an installed one does.
    """
    out: list[DebPackage] = []
    for line in listing.splitlines():
        name, _, status = line.partition("\t")
        state = status[1:2]
        if state and state not in _FILES_GONE:
            out.append(DebPackage(name.split(":")[0]))
    return out


def debian_findings(packages: Iterable[DebPackage], doc: Path) -> list[Prose]:
    """Return a finding per package without its copyright file under ``doc``."""
    return [
        Prose(f"debian package {package}: no {doc / package / 'copyright'}")
        for package in packages
        if not (doc / package / "copyright").is_file()
    ]


def _is_licence(inner: PurePosixPath, file: PackagePath) -> bool:
    """Say whether ``inner``, a path inside a ``.dist-info``, is a licence file holding a byte."""
    named = inner.parts[:1] == ("licenses",) or _LICENCE_FILE.match(inner.name) is not None
    return named and Path(str(file.locate())).stat().st_size > 0


def licence_files(distribution: Distribution) -> list[PurePosixPath]:
    """Return each licence file in ``distribution``'s own ``.dist-info``, from inside it."""
    out: list[PurePosixPath] = []
    for file in distribution.files or []:
        path = PurePosixPath(file)
        if path.parts[0].endswith(".dist-info"):
            inner = path.relative_to(path.parts[0])
            if _is_licence(inner, file):
                out.append(inner)
    return out


def carries_licence(distribution: Distribution) -> bool:
    """Say whether ``distribution`` lists a non-empty licence file in its ``.dist-info``."""
    return bool(licence_files(distribution))


def _after_vendor(path: PurePosixPath) -> PurePosixPath | None:
    """Return the part of ``path`` below its ``_vendor`` directory, or None."""
    parts = path.parts
    if _VENDOR not in parts:
        return None
    return PurePosixPath(*parts[parts.index(_VENDOR) + 1 :])


def unlicensed_vendored(distribution: Distribution) -> list[VendoredPackage]:
    """Return each package ``distribution`` vendors whose licence it does not carry.

    A vendored package is a directory under ``_vendor/`` holding an
    ``__init__.py``.  Its licence is either a file under the distribution's own
    ``.dist-info/licenses/`` whose path passes through ``_vendor/<package>/``
    (pip's layout), or a licence file in a ``.dist-info`` of its own under
    ``_vendor/`` (setuptools' layout), whose distribution name's first dotted
    part, ``-`` read as ``_``, is the package's name (``backports.tarfile``
    covers ``backports``).
    """
    vendored: set[VendoredPackage] = set()
    licensed: set[VendoredPackage] = set()
    for file in distribution.files or []:
        below = _after_vendor(PurePosixPath(file))
        if below is None or len(below.parts) < _PACKAGE_FILE_DEPTH:
            continue
        top = below.parts[0]
        if below.name == "__init__.py" and len(below.parts) == _PACKAGE_FILE_DEPTH:
            vendored.add(VendoredPackage(top))
        elif top.endswith(".dist-info") and _is_licence(below.relative_to(top), file):
            name = top.removesuffix(".dist-info").rsplit("-", 1)[0].replace("-", "_")
            licensed.add(VendoredPackage(name.split(".")[0]))
    for path in licence_files(distribution):
        below = _after_vendor(path) if path.parts[0] == "licenses" else None
        if below is not None and below.parent.parts:
            licensed.add(VendoredPackage(below.parts[0]))
    return sorted(vendored - licensed)


def python_findings(found: Iterable[Distribution]) -> list[Prose]:
    """Return a finding per distribution, or package it vendors, without its licence file."""
    out: list[Prose] = []
    for dist in found:
        name = f"python distribution {dist.metadata['Name']} {dist.version}"
        if not carries_licence(dist):
            out.append(Prose(f"{name}: no licence file"))
        out.extend(
            Prose(f"{name}: vendors {package} without its licence")
            for package in unlicensed_vendored(dist)
        )
    return out


def _has_text(path: Path) -> bool:
    """Say whether ``path`` is a file holding at least one byte."""
    return path.is_file() and path.stat().st_size > 0


def file_findings(
    cpython: Path, version: PythonVersion, notices: Path, bundle: Path
) -> list[Prose]:
    """Return a finding when CPython's licence or notices, or the bundle's texts, are absent."""
    out: list[Prose] = []
    if not cpython.is_file():
        out.append(Prose(f"cpython: no {cpython}"))
    folder = notices / f"cpython-{version}"
    out.extend(
        Prose(f"cpython {version}: no {folder / text}")
        for text in CPYTHON_TEXTS
        if not _has_text(folder / text)
    )
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
        *file_findings(
            Path(sysconfig.get_path("stdlib")) / "LICENSE.txt",
            PythonVersion(platform.python_version()),
            CPYTHON_NOTICES,
            BUNDLE_LICENCES,
        ),
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
