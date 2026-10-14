# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_image_licences``, the runtime image's licence check.

A Debian package is installed when its status reads ``ii``, its architecture
qualifier aside, and owes its copyright file; a Python distribution owes a
licence file in its ``.dist-info`` (under ``licenses/``, or a ``LICENSE``,
``COPYING`` or ``NOTICE`` file there); CPython owes its ``LICENSE.txt`` and the
bundle a licence text under its folder.  The command line answers 0, 1 or 2 as
its docstring says.  ``dpkg-query`` is answered by a stand-in, so no test
starts a process.
"""

from __future__ import annotations

import io
import subprocess
from importlib.metadata import Distribution, PathDistribution
from pathlib import Path
from typing import Literal, NamedTuple

import pytest
from _processes import CommandWord

from tools.check_image_licences import (
    BUNDLE_LICENCES,
    DOC,
    FOUND,
    HELD,
    UNCHECKED,
    DebPackage,
    carries_licence,
    debian_findings,
    file_findings,
    installed,
    main,
    python_findings,
)

from aletheia.common_types import ExitStatus, Prose

type Answer = subprocess.CompletedProcess[Prose]


class _Ran(NamedTuple):
    """What one run of the command line did: its status and what it wrote."""

    status: ExitStatus
    said: Prose


_DPKG_ASKED = [
    CommandWord(word)
    for word in ("/usr/bin/dpkg-query", "-W", "-f", "${Package}\t${db:Status-Abbrev}\n")
]


def _distribution(site: Path, name: Prose, files: list[Prose]) -> Distribution:
    """Return a distribution ``name`` 1.0 installed under ``site``, listing ``files``.

    Each listed file is written under ``site``, since a distribution's files
    leave out the ones missing on disk.
    """
    info = site / f"{name}-1.0.dist-info"
    info.mkdir(parents=True)
    _ = (info / "METADATA").write_text(f"Name: {name}\nVersion: 1.0\n", encoding="utf-8")
    _ = (info / "RECORD").write_text("".join(f"{file},,\n" for file in files), encoding="utf-8")
    for file in files:
        (site / file).parent.mkdir(parents=True, exist_ok=True)
        if not (site / file).exists():
            _ = (site / file).write_text("Copyright\n", encoding="utf-8")
    return PathDistribution(info)


def test_installed_lists_the_packages_dpkg_marks_installed() -> None:
    """Only an ``ii`` status is installed; an architecture qualifier is dropped."""
    listing = Prose("libc6:amd64\tii \nlibgmp10\tii \ngone\trc \nhalf\tiU \n")
    assert installed(listing) == [DebPackage("libc6"), DebPackage("libgmp10")]


def test_debian_findings_names_a_package_without_its_copyright(tmp_path: Path) -> None:
    """A package with a copyright file holds; one without, or with a folder there, is named."""
    for package in ("libc6", "odd"):
        (tmp_path / package).mkdir()
    _ = (tmp_path / "libc6" / "copyright").write_text("Copyright\n", encoding="utf-8")
    (tmp_path / "odd" / "copyright").mkdir()
    packages = [DebPackage("libc6"), DebPackage("odd"), DebPackage("libgmp10")]
    assert debian_findings(packages, tmp_path) == [
        Prose(f"debian package odd: no {tmp_path / 'odd' / 'copyright'}"),
        Prose(f"debian package libgmp10: no {tmp_path / 'libgmp10' / 'copyright'}"),
    ]


@pytest.mark.parametrize(
    "files",
    [
        [Prose("pip-1.0.dist-info/licenses/LICENSE.md")],
        [Prose("pip-1.0.dist-info/licenses/vendor/AUTHORS")],
        [Prose("pip-1.0.dist-info/LICENSE.txt")],
        [Prose("pip-1.0.dist-info/COPYING")],
        [Prose("pip-1.0.dist-info/NOTICE")],
        [Prose("pip-1.0.dist-info/license")],
        [Prose("pip/__init__.py"), Prose("pip-1.0.dist-info/LICENCE")],
    ],
)
def test_carries_licence_finds_a_licence_file_in_the_dist_info(
    tmp_path: Path, files: list[Prose]
) -> None:
    """A licence file under ``licenses/`` or named as one in the ``.dist-info`` counts."""
    assert carries_licence(_distribution(tmp_path, Prose("pip"), files)) is True


@pytest.mark.parametrize(
    "files",
    [
        [],
        [Prose("pip/__init__.py"), Prose("pip-1.0.dist-info/METADATA")],
        [Prose("pip/LICENSE"), Prose("pip/_vendor/COPYING")],
        [Prose("pip-1.0.dist-info")],
        [Prose("pip-1.0.dist-info/RECORD"), Prose("pip-1.0.dist-info/licensing.json")],
    ],
)
def test_carries_licence_is_false_without_one_in_the_dist_info(
    tmp_path: Path, files: list[Prose]
) -> None:
    """A licence file outside the ``.dist-info``, or none, does not count."""
    assert carries_licence(_distribution(tmp_path, Prose("pip"), files)) is False


def test_python_findings_names_each_distribution_without_a_licence(tmp_path: Path) -> None:
    """Each distribution lacking a licence file is named with its version."""
    found = [
        _distribution(tmp_path, Prose("pip"), [Prose("pip-1.0.dist-info/licenses/LICENSE.txt")]),
        _distribution(tmp_path, Prose("aletheia"), [Prose("aletheia/__init__.py")]),
    ]
    assert python_findings(found) == [Prose("python distribution aletheia 1.0: no licence file")]


def test_file_findings_holds_cpythons_licence_and_the_bundles_texts(tmp_path: Path) -> None:
    """CPython's LICENSE.txt and a text in a bundle folder: no finding."""
    cpython = tmp_path / "LICENSE.txt"
    _ = cpython.write_text("PSF\n", encoding="utf-8")
    (tmp_path / "licenses" / "text-2.1.1").mkdir(parents=True)
    _ = (tmp_path / "licenses" / "text-2.1.1" / "LICENSE").write_text("BSD\n", encoding="utf-8")
    assert not file_findings(cpython, tmp_path / "licenses")


@pytest.mark.parametrize("bundle", ["absent", "empty", "folders only", "file at top"])
def test_file_findings_names_what_is_missing(
    tmp_path: Path, bundle: Literal["absent", "empty", "folders only", "file at top"]
) -> None:
    """No CPython licence, and a bundle folder holding no text in a library folder, are named."""
    licences = tmp_path / "licenses"
    if bundle != "absent":
        licences.mkdir()
    if bundle == "folders only":
        (licences / "text-2.1.1").mkdir()
    if bundle == "file at top":
        _ = (licences / "LICENSE").write_text("BSD\n", encoding="utf-8")
    assert file_findings(tmp_path / "LICENSE.txt", licences) == [
        Prose(f"cpython: no {tmp_path / 'LICENSE.txt'}"),
        Prose(f"bundle: no licence text under {licences}"),
    ]


def _run_main(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, listing: Answer, found: list[Distribution]
) -> _Ran:
    """Run the command line over a planted image under ``tmp_path``; return what it did."""
    doc, licences = tmp_path / "doc", tmp_path / "licenses"
    (doc / "libgmp10").mkdir(parents=True)
    _ = (doc / "libgmp10" / "copyright").write_text("LGPL\n", encoding="utf-8")
    (licences / "gmp").mkdir(parents=True)
    _ = (licences / "gmp" / "LICENSE").write_text("BSD\n", encoding="utf-8")
    _ = (tmp_path / "LICENSE.txt").write_text("PSF\n", encoding="utf-8")
    asked: list[list[CommandWord]] = []
    said = io.StringIO()

    def answer(cmd: list[CommandWord], *, capture_output: bool, text: bool, check: bool) -> Answer:
        """Record ``cmd`` and answer it as ``dpkg-query`` would."""
        assert (capture_output, text, check) == (True, True, False)
        asked.append(cmd)
        return listing

    def stdlib(name: Prose) -> Prose:
        """Answer the standard library path the image's python3 has."""
        assert name == "stdlib"
        return Prose(str(tmp_path))

    monkeypatch.setattr("tools.check_image_licences.subprocess.run", answer)
    monkeypatch.setattr("tools.check_image_licences.DOC", doc)
    monkeypatch.setattr("tools.check_image_licences.BUNDLE_LICENCES", licences)
    monkeypatch.setattr("tools.check_image_licences.distributions", lambda: found)
    monkeypatch.setattr("tools.check_image_licences.sysconfig.get_path", stdlib)
    monkeypatch.setattr("sys.stdout", said)
    monkeypatch.setattr("sys.argv", ["check_image_licences"])
    status = main()
    assert asked == [_DPKG_ASKED]
    return _Ran(status, Prose(said.getvalue()))


def _listing(out: Prose, status: ExitStatus = HELD) -> Answer:
    """Return what ``dpkg-query`` answers: ``out`` with ``status``."""
    return subprocess.CompletedProcess(_DPKG_ASKED, status, out, Prose("dpkg-query: broken\n"))


def test_main_holds_an_image_whose_every_package_carries_its_licence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Every package with its text exits 0, counting the Debian packages."""
    pip = _distribution(tmp_path / "site", Prose("pip"), [Prose("pip-1.0.dist-info/LICENSE.txt")])
    assert _run_main(monkeypatch, tmp_path, _listing(Prose("libgmp10\tii \n")), [pip]) == _Ran(
        HELD,
        Prose(
            "image-licences: each of 1 Debian packages, every Python distribution, CPython and "
            + "the bundle carries its licence text\n"
        ),
    )


def test_main_names_each_package_without_its_licence_and_exits_one(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A Debian package and a distribution each lacking a text exit 1, each named."""
    ours = _distribution(tmp_path / "site", Prose("aletheia"), [Prose("aletheia/__init__.py")])
    listing = _listing(Prose("libgmp10\tii \nzlib1g\tii \n"))
    assert _run_main(monkeypatch, tmp_path, listing, [ours]) == _Ran(
        FOUND,
        Prose(
            "image-licences: debian package zlib1g: "
            + f"no {tmp_path / 'doc' / 'zlib1g' / 'copyright'}\n"
            + "image-licences: python distribution aletheia 1.0: no licence file\n"
        ),
    )


def test_main_is_unchecked_when_dpkg_query_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A dpkg-query that fails exits 2 with its message, never a pass."""
    assert _run_main(monkeypatch, tmp_path, _listing(Prose("libgmp10\tii \n"), FOUND), []) == _Ran(
        UNCHECKED, Prose("image-licences: dpkg-query failed: dpkg-query: broken\n")
    )


def test_main_refuses_an_argument(monkeypatch: pytest.MonkeyPatch) -> None:
    """The check takes no argument; one given is refused."""
    monkeypatch.setattr("sys.argv", ["check_image_licences", "--all"])
    with pytest.raises(SystemExit) as refused:
        _ = main()
    assert refused.value.code == ExitStatus(2)


def test_the_paths_read_are_debians_and_the_images() -> None:
    """The copyright files are Debian's, the licence folder the bundle's in the image.

    Debian installs a package's copyright as ``/usr/share/doc/<package>/copyright``; the
    bundle's licence folder is ``licenses/`` where ``Dockerfile.runtime`` copies the bundle.
    """
    dockerfile = Path(__file__).resolve().parents[2] / "Dockerfile.runtime"
    copy = next(
        line.split()
        for line in dockerfile.read_text(encoding="utf-8").splitlines()
        if line.startswith("COPY dist/aletheia ")
    )
    assert Path(copy[-1]) / "licenses" == BUNDLE_LICENCES
    assert Path("/usr/share/doc") == DOC


def test_the_exit_statuses_are_the_ones_the_usage_states() -> None:
    """Held, found and unchecked exit 0, 1 and 2, as the module's usage says."""
    assert (ExitStatus(0), ExitStatus(1), ExitStatus(2)) == (HELD, FOUND, UNCHECKED)
