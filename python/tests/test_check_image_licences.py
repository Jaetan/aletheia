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

import hashlib
import io
import subprocess
from importlib.metadata import Distribution, PathDistribution
from pathlib import Path
from typing import Literal, NamedTuple, TypedDict, cast

import pytest
import yaml
from _processes import CommandWord

from tools.check_image_licences import (
    BUNDLE_LICENCES,
    CPYTHON_NOTICES,
    CPYTHON_TEXTS,
    DOC,
    FOUND,
    HELD,
    UNCHECKED,
    DebPackage,
    PythonVersion,
    VendoredPackage,
    carries_licence,
    debian_findings,
    file_findings,
    installed,
    main,
    python_findings,
    unlicensed_vendored,
)

from aletheia.common_types import ExitStatus, Prose

type Answer = subprocess.CompletedProcess[Prose]

_REPO = Path(__file__).resolve().parents[2]


class _Text(TypedDict):
    sha256: Prose


class CpythonRecord(TypedDict):
    """What ``packaging/image-licenses/sources.yaml`` records: the CPython and its texts."""

    cpython: PythonVersion
    texts: dict[Prose, _Text]


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


def test_installed_lists_the_packages_whose_files_dpkg_leaves_on_disk() -> None:
    """Every state but not-installed and config-files keeps files; the qualifier is dropped."""
    listing = Prose(
        "libc6:amd64\tii \nheld\thi \nhalf\tiU \nfailed\tiF \nwaiting\tiW \n"
        + "gone\trc \npurged\tpn \nnever\tun \nreinst\tiiR\nshort\ti\n"
    )
    assert installed(listing) == [
        DebPackage(name) for name in ("libc6", "held", "half", "failed", "waiting", "reinst")
    ]


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
        [Prose("pip-1.0.dist-info/NOTICE")],
    ],
)
def test_carries_licence_is_false_without_one_in_the_dist_info(
    tmp_path: Path, files: list[Prose]
) -> None:
    """A licence file outside the ``.dist-info``, or none, does not count."""
    assert carries_licence(_distribution(tmp_path, Prose("pip"), files)) is False


@pytest.mark.parametrize(("held", "carried"), [("", False), ("x", True)])
def test_carries_licence_needs_a_byte_in_the_licence_file(
    tmp_path: Path, held: Literal["", "x"], *, carried: bool
) -> None:
    """A licence file holding nothing carries no licence; one byte is enough to read."""
    found = _distribution(tmp_path, Prose("pip"), [Prose("pip-1.0.dist-info/LICENSE")])
    _ = (tmp_path / "pip-1.0.dist-info" / "LICENSE").write_text(held, encoding="utf-8")
    assert carries_licence(found) is carried


def test_unlicensed_vendored_names_each_vendored_package_without_its_licence(
    tmp_path: Path,
) -> None:
    """A package under ``_vendor/`` owes a licence under ``licenses/.../_vendor/<package>/``."""
    files = [
        Prose("pip/_vendor/__init__.py"),
        Prose("pip/_vendor/vendor.txt"),
        Prose("pip/_vendor/certifi/__init__.py"),
        Prose("pip/_vendor/certifi/core.py"),
        Prose("pip/_vendor/idna/__init__.py"),
        Prose("pip/_vendor/idna/sub/__init__.py"),
        Prose("pip/_vendor/rich/__init__.py"),
        Prose("pip-1.0.dist-info/licenses/LICENSE.txt"),
        Prose("pip-1.0.dist-info/licenses/src/pip/_vendor/certifi/LICENSE"),
        Prose("pip-1.0.dist-info/licenses/src/pip/_vendor/LICENSE"),
    ]
    found = _distribution(tmp_path, Prose("pip"), files)
    assert unlicensed_vendored(found) == [VendoredPackage("idna"), VendoredPackage("rich")]
    assert python_findings([found]) == [
        Prose("python distribution pip 1.0: vendors idna without its licence"),
        Prose("python distribution pip 1.0: vendors rich without its licence"),
    ]


def test_unlicensed_vendored_reads_a_vendored_packages_own_dist_info(tmp_path: Path) -> None:
    """A licence in a ``.dist-info`` of its own under ``_vendor/`` covers the package it names."""
    files = [
        Prose("setuptools/_vendor/zipp/__init__.py"),
        Prose("setuptools/_vendor/zipp-3.23.0.dist-info/licenses/LICENSE"),
        Prose("setuptools/_vendor/backports/__init__.py"),
        Prose("setuptools/_vendor/backports.tarfile-1.2.0.dist-info/LICENSE"),
        Prose("setuptools/_vendor/more_itertools/__init__.py"),
        Prose("setuptools/_vendor/more-itertools-10.8.0.dist-info/LICENSE"),
        Prose("setuptools/_vendor/tomli/__init__.py"),
        Prose("setuptools/_vendor/tomli-2.4.0.dist-info/METADATA"),
        Prose("setuptools-84.0.0.dist-info/licenses/LICENSE"),
    ]
    found = _distribution(tmp_path, Prose("setuptools"), files)
    assert unlicensed_vendored(found) == [VendoredPackage("tomli")]


def test_carries_licence_reads_only_the_distributions_own_dist_info(tmp_path: Path) -> None:
    """A vendored package's licence is not the distribution's own."""
    files = [
        Prose("setuptools/_vendor/zipp/__init__.py"),
        Prose("setuptools/_vendor/zipp-3.23.0.dist-info/licenses/LICENSE"),
        Prose("setuptools-84.0.0.dist-info/METADATA"),
    ]
    assert carries_licence(_distribution(tmp_path, Prose("setuptools"), files)) is False


def test_python_findings_names_each_distribution_without_a_licence(tmp_path: Path) -> None:
    """Each distribution lacking a licence file is named with its version."""
    found = [
        _distribution(tmp_path, Prose("pip"), [Prose("pip-1.0.dist-info/licenses/LICENSE.txt")]),
        _distribution(tmp_path, Prose("aletheia"), [Prose("aletheia/__init__.py")]),
    ]
    assert python_findings(found) == [Prose("python distribution aletheia 1.0: no licence file")]


_VERSION = PythonVersion("3.14.6")


def _cpython_notices(root: Path, texts: tuple[Path, ...] = CPYTHON_TEXTS) -> Path:
    """Write CPython 3.14.6's notice texts named ``texts`` under ``root``; return ``root``."""
    (root / "cpython-3.14.6").mkdir(parents=True)
    for text in texts:
        _ = (root / "cpython-3.14.6" / text).write_text("M", encoding="utf-8")
    return root


def test_file_findings_holds_cpythons_licence_and_notices_and_the_bundles_texts(
    tmp_path: Path,
) -> None:
    """CPython's LICENSE.txt and notices for its version, and a text in a bundle folder."""
    cpython = tmp_path / "LICENSE.txt"
    _ = cpython.write_text("PSF\n", encoding="utf-8")
    (tmp_path / "licenses" / "text-2.1.1").mkdir(parents=True)
    _ = (tmp_path / "licenses" / "text-2.1.1" / "LICENSE").write_text("BSD\n", encoding="utf-8")
    notices = _cpython_notices(tmp_path / "notices")
    assert not file_findings(cpython, _VERSION, notices, tmp_path / "licenses")


@pytest.mark.parametrize("kept", ["none", "other version", "one empty"])
def test_file_findings_names_each_cpython_notice_missing_for_its_version(
    tmp_path: Path, kept: Literal["none", "other version", "one empty"]
) -> None:
    """Notices for another version, none, or an empty text leave CPython's texts unshipped."""
    cpython = tmp_path / "LICENSE.txt"
    _ = cpython.write_text("PSF\n", encoding="utf-8")
    (tmp_path / "licenses" / "text-2.1.1").mkdir(parents=True)
    _ = (tmp_path / "licenses" / "text-2.1.1" / "LICENSE").write_text("BSD\n", encoding="utf-8")
    notices = tmp_path / "notices"
    missing = list(CPYTHON_TEXTS)
    if kept == "other version":
        _ = _cpython_notices(notices)
        version = PythonVersion("3.14.7")
    else:
        version = _VERSION
        if kept == "one empty":
            _ = _cpython_notices(notices, CPYTHON_TEXTS[1:])
            (notices / "cpython-3.14.6" / CPYTHON_TEXTS[0]).touch()
            missing = [CPYTHON_TEXTS[0]]
    folder = notices / f"cpython-{version}"
    assert file_findings(cpython, version, notices, tmp_path / "licenses") == [
        Prose(f"cpython {version}: no {folder / text}") for text in missing
    ]


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
    notices = _cpython_notices(tmp_path / "notices")
    assert file_findings(tmp_path / "LICENSE.txt", _VERSION, notices, licences) == [
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
    notices = _cpython_notices(tmp_path / "notices")
    monkeypatch.setattr("tools.check_image_licences.CPYTHON_NOTICES", notices)
    monkeypatch.setattr("tools.check_image_licences.platform.python_version", lambda: _VERSION)
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
    copy = _copy_line(Prose("COPY dist/aletheia "))
    assert Path(copy[-1]) / "licenses" == BUNDLE_LICENCES
    assert Path("/usr/share/doc") == DOC


def _copy_line(start: Prose) -> list[Prose]:
    """Return the words of the line of ``Dockerfile.runtime`` that opens with ``start``."""
    dockerfile = _REPO / "Dockerfile.runtime"
    return next(
        [Prose(word) for word in line.split()]
        for line in dockerfile.read_text(encoding="utf-8").splitlines()
        if line.startswith(start)
    )


def test_the_kept_cpython_notices_are_the_recorded_ones_the_image_copies() -> None:
    """The tree keeps, for the record's CPython, exactly its texts, which the image copies."""
    kept = _REPO / "packaging" / "image-licenses"
    record = cast(
        "CpythonRecord", yaml.safe_load((kept / "sources.yaml").read_text(encoding="utf-8"))
    )
    folder = f"cpython-{record['cpython']}"
    on_disk = sorted(f"{folder}/{path.name}" for path in (kept / folder).iterdir())
    assert on_disk == sorted(record["texts"])
    assert sorted(Path(path).name for path in record["texts"]) == sorted(
        text.name for text in CPYTHON_TEXTS
    )
    for path, entry in record["texts"].items():
        assert hashlib.sha256((kept / path).read_bytes()).hexdigest() == entry["sha256"]
    copy = _copy_line(Prose("COPY packaging/image-licenses/"))
    assert copy[1:] == [
        Prose(f"packaging/image-licenses/{folder}"),
        Prose(str(CPYTHON_NOTICES / folder)),
    ]


def test_the_exit_statuses_are_the_ones_the_usage_states() -> None:
    """Held, found and unchecked exit 0, 1 and 2, as the module's usage says."""
    assert (ExitStatus(0), ExitStatus(1), ExitStatus(2)) == (HELD, FOUND, UNCHECKED)
