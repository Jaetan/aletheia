# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Stage the licence texts of the third-party libraries the release bundle carries, and hold them.

The bundle's ``lib/`` carries the kernel library, into which Agda compiles its
runtime support (``MAlonzo.RTE``, ``Agda.Builtin``) and the Agda libraries the
project depends on (``depend:`` in ``aletheia.agda-lib``), and beside it every
library ``ldd`` resolves under GHC's lib directory (``getGhcDeps`` in
``shake/Shared.hs``): the GHC packages, the runtime system and libffi.  Each
licence asks that its notice travel with a binary, and the obligation is
transitive.  GHC's install holds only GHC's own licence (a copy in each
package's documentation directory), which is the text of the runtime system
and ghc-boot-th and of no other library, so the texts are kept in the tree
under ``packaging/licenses/``, a folder ``<name>-<version>`` per work: for the
kernel, ``Agda-<version>`` (the Agda on the search path) and each Agda library
it depends on as ``depend:`` names it; for a GHC package, its name and version
as its library file names them, the runtime system's way (``_thr``) aside; for
libffi, the release named by the ``ffi.h`` of the GHC on the search path.
Each folder holds the licence the work declares (a package's
``license-file``; for the runtime system, which declares none, GHC's own) and
that of each work whose code is compiled into it, since GHC's install carries
none of those texts; where the work's source credits code to a work that
publishes no licence for it, a ``NOTICE`` names that code.
``packaging/licenses/sources.yaml`` records the GHC the texts were taken from,
its source tarball, any other upstream source a text was taken from (its
``sources:``, named by the text's ``source:``: a tarball, or the page a
licence is published on), and each text's SHA-256.  Which works a library
takes code from is found by ``tools/licence_audit.py``, whose verdicts
``packaging/licenses/audit.yaml`` holds.  In a folder of licence texts
anything but a regular file directly in a library's folder is a finding, the
record and the verdicts beside the kept folders apart.

The commands:

* ``check LIBRARY...`` holds the kept folders to the libraries given (the
  kernel among them), both ways, the record to the kept texts, both ways, each
  text naming a copyright, the record's upstream sources to the texts naming
  them, both ways, the record to the GHC on the search path, and the
  verdicts to the record and the kept texts: every tarball the audit reads
  scanned, every tarball scanned one the record names at the SHA-256 it
  records, and each verdict one kept text covering its hit or one reason it
  owes none.  The Shake target ``check-bundle-licences`` runs it over the
  libraries the dist rule bundles, and the dist rule needs that target.
* ``stage BUNDLE LIBRARY...`` writes each library's kept texts into a fresh
  ``BUNDLE/licenses/``, mode 0644, and writes nothing when a library has none,
  naming it, or when ``BUNDLE/licenses/`` is already there.
* ``check-bundle BUNDLE`` holds the staged bundle: ``BUNDLE/lib/`` holds only
  regular files and carries the kernel library, whose own licence is
  ``BUNDLE/LICENSE.md``, naming a copyright; every library there has its
  folders in ``BUNDLE/licenses/`` holding exactly the kept texts, every
  folder there belongs to a library in ``BUNDLE/lib/``, and every binding in
  ``BUNDLE/bindings/`` carries a copy of ``BUNDLE/LICENSE.md``, since each is
  redistributed on its own.

Exit 0 when held; 1 on a finding; 2 when it cannot check: the record, the
verdicts or ``aletheia.agda-lib`` cannot be read, ghc, ghc-pkg or agda is not on the search
path or names no version, no ``ffi.h`` among the runtime system's include
directories names a libffi release, or the bundle has no ``lib/``.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path
from typing import Literal, NamedTuple, NewType, NotRequired, TypedDict, cast

import yaml
from yaml.error import YAMLError

from tools._common import emit, find_executable, run_capture
from tools.check_haskell_ledger import library_name
from tools.sbom_generate import GhcVersion, ghc_library

from aletheia.common_types import ExitStatus, Prose

REPO = Path(__file__).resolve().parent.parent
HELD, FOUND, UNCHECKED = ExitStatus(0), ExitStatus(1), ExitStatus(2)

KEPT = Path("packaging/licenses")
RECORD = Path("sources.yaml")
AUDIT = Path("audit.yaml")
BUNDLED = Path("licenses")
KERNEL = "libaletheia-ffi.so"
KERNEL_LICENCE = "LICENSE.md"
BINDINGS = Path("bindings")

# A library's licence folder, ``<name>-<version>``.
Folder = NewType("Folder", str)
# A kept text's path from the folders' parent, ``<folder>/<file>``, and its bytes.
TextPath = NewType("TextPath", str)
LicenceText = NewType("LicenceText", bytes)
Digest = NewType("Digest", str)
LibffiRelease = NewType("LibffiRelease", str)
AgdaVersion = NewType("AgdaVersion", str)
# An Agda library as ``depend:`` names it: ``standard-library-2.4``.
AgdaLibrary = NewType("AgdaLibrary", str)
# An upstream source the record names, other than GHC's tarball: ``filepath-1.4.2.2``.
SourceName = NewType("SourceName", str)
# A tarball the audit reads: ``ghc`` for GHC's source tarball, else a source's name.
TarballName = NewType("TarballName", str)
# A file's path inside its tarball, the tarball's top directory left out.
SourcePath = NewType("SourcePath", str)
GHC_TARBALL = TarballName("ghc")
# The line a hit that is a licence file carries in place of a line of text.
LICENCE_FILE_LINE = Prose("(licence file)")
Command = Literal["check", "stage", "check-bundle"]

# The runtime system's library names its way after its version: ``libHSrts-1.0.2_thr``.
_WAY = re.compile(r"_[a-z_]+$")
# ``ffi.h`` opens on a comment whose first line names the release: ``libffi 3.4.6``.
_LIBFFI_RELEASE = re.compile(r"^\s*libffi (\d[\w.]*)", re.MULTILINE)
_COPYRIGHT = re.compile(r"copyright", re.IGNORECASE)
_DIGEST = re.compile(r"[0-9a-f]{64}")
_PRIMARY = re.compile(r"^LICEN[CS]E$")
_VERSION = re.compile(r"\d+(?:\.\d+)+")
_URL = re.compile(r"https://\S+")
# ``depend:`` and the indented lines continuing it, in an ``.agda-lib`` file.
_DEPEND = re.compile(r"^depend:(.*(?:\n[ \t]+.*)*)", re.MULTILINE)
AGDA_LIB = Path("aletheia.agda-lib")
_TEXT_MODE = 0o644
_HELD: dict[Command, Prose] = {
    "check": Prose("the kept licence texts hold for every library given"),
    "stage": Prose("each library's licence texts are staged"),
    "check-bundle": Prose("every library the bundle carries has its licence text"),
}


class _Text(TypedDict):
    sha256: Digest
    source: NotRequired[SourceName]


class _Source(TypedDict):
    url: Prose
    sha256: Digest


class Record(TypedDict):
    """What ``sources.yaml`` records: the GHC, the sources, and each kept text's digest.

    A text taken from a source other than GHC's tarball names it as its ``source``.
    """

    ghc: GhcVersion
    tarball: _Source
    sources: dict[SourceName, _Source]
    texts: dict[TextPath, _Text]


class Verdict(TypedDict):
    """The audit's verdict on one hit: the kept text covering it, or why it owes none."""

    tarball: TarballName
    path: SourcePath
    line: Prose
    covered_by: NotRequired[TextPath]
    dismissed: NotRequired[Prose]


class Audit(TypedDict):
    """What ``audit.yaml`` records: the tarballs scanned, and a verdict per hit."""

    tarballs: dict[TarballName, Digest]
    verdicts: list[Verdict]


class Versions(NamedTuple):
    """The releases a library's licence folder is named for, beyond its own file name."""

    libffi: LibffiRelease
    agda: AgdaVersion
    depends: list[AgdaLibrary]


class Claims(NamedTuple):
    """Each library's licence folder, and a finding per library the tree keeps no licence for."""

    folders: dict[Folder, Path]
    unknown: list[Prose]


class LicenceUnreadError(Exception):
    """The record, or a version the folders are named for, could not be read."""


def folders_of(library: Path, versions: Versions) -> list[Folder]:
    """Return the folders holding ``library``'s licences, none when the tree keeps none for it."""
    if library.name == KERNEL:
        return [Folder(f"Agda-{versions.agda}"), *(Folder(lib) for lib in versions.depends)]
    found = ghc_library(library)
    if found is not None:
        return [Folder(f"{found.package}-{_WAY.sub('', found.version)}")]
    return [Folder(f"libffi-{versions.libffi}")] if library_name(library) == "ffi" else []


def agda_depends(agda_lib: Prose) -> list[AgdaLibrary]:
    """Return the Agda libraries an ``.agda-lib`` file's ``depend:`` names, in its order."""
    return [AgdaLibrary(word) for found in _DEPEND.finditer(agda_lib) for word in found[1].split()]


def libffi_release(header: Prose) -> LibffiRelease | None:
    """Return the libffi release the text of ``ffi.h`` names, or None when it names none."""
    found = _LIBFFI_RELEASE.search(header)
    return None if found is None else LibffiRelease(found[1])


def read_record(text: Prose) -> Record:
    """Return the record ``text`` holds, raising ``LicenceUnreadError`` on a value not shaped."""
    record = cast("Record", yaml.safe_load(text))
    try:
        tarballs = [record["tarball"], *record["sources"].values()]
        shaped = [
            (Prose("a GHC version"), _VERSION, record["ghc"]),
            *((Prose("an https URL"), _URL, tarball["url"]) for tarball in tarballs),
            *((Prose("a SHA-256 digest"), _DIGEST, tarball["sha256"]) for tarball in tarballs),
            *((Prose("a SHA-256 digest"), _DIGEST, t["sha256"]) for t in record["texts"].values()),
        ]
        malformed = [
            f"{value!r} is not {kind}"
            for kind, shape, value in shaped
            if not shape.fullmatch(value)
        ]
    except KeyError as exc:
        message = f"{KEPT / RECORD} lacks the key {exc}"
        raise LicenceUnreadError(message) from exc
    except (TypeError, AttributeError) as exc:
        message = f"{KEPT / RECORD} is not shaped as a record: {exc}"
        raise LicenceUnreadError(message) from exc
    if malformed:
        message = f"{KEPT / RECORD}: {malformed[0]}"
        raise LicenceUnreadError(message)
    return record


def read_audit(text: Prose) -> Audit:
    """Return the audit ``text`` holds, raising ``LicenceUnreadError`` on a missing value."""
    audit = cast("Audit", yaml.safe_load(text))
    try:
        _ = [v["tarball"] + v["path"] + v["line"] for v in audit["verdicts"]]
        malformed = [d for d in audit["tarballs"].values() if not _DIGEST.fullmatch(d)]
    except KeyError as exc:
        message = f"{KEPT / AUDIT} lacks the key {exc}"
        raise LicenceUnreadError(message) from exc
    except (TypeError, AttributeError) as exc:
        message = f"{KEPT / AUDIT} is not shaped as an audit: {exc}"
        raise LicenceUnreadError(message) from exc
    if malformed:
        message = f"{KEPT / AUDIT}: {malformed[0]!r} is not a SHA-256 digest"
        raise LicenceUnreadError(message)
    return audit


def scanned_tarballs(record: Record) -> list[TarballName]:
    """Return each tarball a library's own licence text was taken from: the ones the audit reads."""
    return sorted(
        {
            GHC_TARBALL if "source" not in entry else TarballName(entry["source"])
            for path, entry in record["texts"].items()
            if _PRIMARY.match(path.partition("/")[2])
        }
    )


def audit_findings(record: Record, audit: Audit, kept: Path) -> list[Prose]:
    """Return every way the audit is stale or leaves a hit unjudged, reading no tarball."""
    wanted = {GHC_TARBALL: record["tarball"]["sha256"]} | {
        TarballName(name): source["sha256"] for name, source in record["sources"].items()
    }
    out = [
        Prose(f"{KEPT / AUDIT}: scanned {name} at a SHA-256 the record does not name")
        for name, digest in sorted(audit["tarballs"].items())
        if wanted.get(name) != digest
    ]
    out.extend(
        Prose(f"{KEPT / AUDIT}: scanned no {name}; scan it with tools.licence_audit")
        for name in scanned_tarballs(record)
        if name not in audit["tarballs"]
    )
    texts = _texts(kept)
    for verdict in audit["verdicts"]:
        where = f"{KEPT / AUDIT}: {verdict['tarball']}:{verdict['path']}"
        covered, dismissed = verdict.get("covered_by", ""), verdict.get("dismissed", "")
        if bool(covered) == bool(dismissed):
            out.append(
                Prose(f"{where}: its verdict needs one of covered_by and dismissed, not both")
            )
        elif covered and covered not in texts:
            out.append(Prose(f"{where}: covered by {covered}, which is not kept"))
    return out


def _is_folder(path: Path) -> bool:
    """Say whether ``path`` is a directory itself, not a link to one."""
    return path.is_dir() and not path.is_symlink()


def _is_text(path: Path) -> bool:
    """Say whether ``path`` is a regular file itself, not a link to one."""
    return path.is_file() and not path.is_symlink()


def _folders(root: Path) -> set[Folder]:
    """Return the name of every folder directly under ``root``."""
    return {Folder(path.name) for path in root.iterdir() if _is_folder(path)}


def _texts(root: Path) -> dict[TextPath, LicenceText]:
    """Return every text in ``root``'s folders by its path from ``root``, with its bytes."""
    return {
        TextPath(f"{folder}/{path.name}"): LicenceText(path.read_bytes())
        for folder in sorted(_folders(root))
        for path in sorted((root / folder).iterdir())
        if _is_text(path)
    }


def _strays(root: Path, *beside: Path) -> list[TextPath]:
    """Return every entry under ``root`` but its folders, their texts and the files ``beside``."""
    out: list[TextPath] = []
    for path in sorted(root.iterdir()):
        if _is_folder(path):
            out.extend(
                TextPath(f"{path.name}/{inner.name}")
                for inner in sorted(path.iterdir())
                if not _is_text(inner)
            )
        elif not (_is_text(path) and Path(path.name) in beside):
            out.append(TextPath(path.name))
    return out


def _in(folder: Folder, texts: dict[TextPath, LicenceText]) -> dict[TextPath, LicenceText]:
    """Return the texts of ``texts`` that ``folder`` holds."""
    return {path: text for path, text in texts.items() if path.startswith(f"{folder}/")}


def claims(libraries: list[Path], versions: Versions) -> Claims:
    """Return the library each folder covers, and a finding per library the tree keeps none for."""
    found = Claims({}, [])
    for library in libraries:
        folders = folders_of(library, versions)
        if not folders:
            found.unknown.append(Prose(f"{library.name}: no licence is kept for it"))
        found.folders.update(dict.fromkeys(folders, library))
    return found


def kept_findings(
    libraries: list[Path], versions: Versions, ghc: GhcVersion, kept: Path, record: Record
) -> list[Prose]:
    """Return every way the kept texts, their record, the libraries and the GHC disagree."""
    claimed = claims(libraries, versions)
    texts = _texts(kept)
    recorded = {path: entry["sha256"] for path, entry in record["texts"].items()}
    out = list(claimed.unknown)
    out.extend(
        Prose(f"{KEPT}/{path}: not a licence text in a library's folder")
        for path in _strays(kept, RECORD, AUDIT)
    )
    out.extend(
        Prose(f"{library.name}: {KEPT}/{folder}/ keeps no licence text")
        for folder, library in sorted(claimed.folders.items())
        if not _in(folder, texts)
    )
    out.extend(
        Prose(f"{KEPT}/{folder}/: kept for no library the bundle carries")
        for folder in sorted(_folders(kept) - claimed.folders.keys())
    )
    if record["ghc"] != ghc:
        out.append(
            Prose(f"{KEPT / RECORD}: records GHC {record['ghc']}, the search path's is {ghc}")
        )
    if not record["tarball"]["url"].endswith(f"/ghc-{record['ghc']}-src.tar.xz"):
        out.append(Prose(f"{KEPT / RECORD}: its tarball is not GHC {record['ghc']}'s source"))
    named = {path: entry["source"] for path, entry in record["texts"].items() if "source" in entry}
    out.extend(
        Prose(f"{KEPT / RECORD}: {path} names the source {source}, which it does not record")
        for path, source in sorted(named.items())
        if source not in record["sources"]
    )
    out.extend(
        Prose(f"{KEPT / RECORD}: records the source {source}, which no text names")
        for source in sorted(record["sources"].keys() - set(named.values()))
    )
    out.extend(
        Prose(f"{KEPT}/{path}: not in {KEPT / RECORD}") for path in sorted(texts.keys() - recorded)
    )
    out.extend(
        Prose(f"{KEPT / RECORD}: records {path}, which is not kept")
        for path in sorted(recorded.keys() - texts.keys())
    )
    out.extend(
        Prose(f"{KEPT}/{path}: its SHA-256 is not the one {KEPT / RECORD} records")
        for path in sorted(texts.keys() & recorded.keys())
        if hashlib.sha256(texts[path]).hexdigest() != recorded[path]
    )
    out.extend(
        Prose(f"{KEPT}/{path}: names no copyright")
        for path, text in sorted(texts.items())
        if _COPYRIGHT.search(text.decode("utf-8", errors="replace")) is None
    )
    return out


def stage(bundle: Path, libraries: list[Path], versions: Versions, kept: Path) -> list[Prose]:
    """Copy each library's kept texts into ``bundle``, or nothing and a finding per one without."""
    texts = _texts(kept)
    claimed = claims(libraries, versions)
    chosen: dict[TextPath, LicenceText] = {}
    missing = list(claimed.unknown)
    for folder, library in sorted(claimed.folders.items()):
        held = _in(folder, texts)
        if not held:
            missing.append(Prose(f"{library.name}: {KEPT}/{folder}/ keeps no licence text"))
        chosen |= held
    if missing:
        return missing
    if (bundle / BUNDLED).exists() or (bundle / BUNDLED).is_symlink():
        return [Prose(f"{BUNDLED}/: already in the bundle; stage writes it fresh")]
    for path, text in chosen.items():
        copied = bundle / BUNDLED / path
        copied.parent.mkdir(parents=True, exist_ok=True)
        _ = copied.write_bytes(text)
        copied.chmod(_TEXT_MODE)
    return []


def bundle_findings(bundle: Path, versions: Versions, kept: Path) -> list[Prose]:
    """Return each library ``bundle`` carries without its licence, and each unused licence."""
    staged = bundle / BUNDLED
    entries = sorted((bundle / "lib").iterdir())
    libraries = [path for path in entries if _is_text(path)]
    out = [Prose(f"lib/{path.name}: not a library file") for path in entries if not _is_text(path)]
    licence = bundle / KERNEL_LICENCE
    if all(library.name != KERNEL for library in libraries):
        out.append(Prose(f"lib/: the bundle carries no {KERNEL}"))
    elif not _is_text(licence):
        out.append(Prose(f"lib/{KERNEL}: the bundle carries no {KERNEL_LICENCE}"))
    elif _COPYRIGHT.search(licence.read_text(encoding="utf-8", errors="replace")) is None:
        out.append(Prose(f"lib/{KERNEL}: its {KERNEL_LICENCE} names no copyright"))
    claimed = claims(libraries, versions)
    out.extend(Prose(f"lib/{finding}") for finding in claimed.unknown)
    out.extend(_binding_findings(bundle))
    if staged.exists() and not _is_folder(staged):
        out.append(Prose(f"{BUNDLED}: not a folder"))
    elif staged.exists():
        out.extend(
            Prose(f"{BUNDLED}/{path}: not a licence text in a library's folder")
            for path in _strays(staged)
        )
    shipped = _texts(staged) if _is_folder(staged) else {}
    wanted = _texts(kept)
    for folder, library in sorted(claimed.folders.items()):
        here = _in(folder, shipped)
        if not here:
            out.append(Prose(f"lib/{library.name}: {BUNDLED}/{folder}/ holds no licence text"))
        elif here != _in(folder, wanted):
            out.append(Prose(f"lib/{library.name}: {BUNDLED}/{folder}/ is not {KEPT}/{folder}/"))
    out.extend(
        Prose(f"{BUNDLED}/{folder}/: the bundle's lib/ carries no library it covers")
        for folder in sorted(
            (_folders(staged) if _is_folder(staged) else set[Folder]()) - claimed.folders.keys()
        )
    )
    return out


def _binding_findings(bundle: Path) -> list[Prose]:
    """Return a finding per binding in ``bundle`` without a copy of its ``LICENSE.md``."""
    bindings = bundle / BINDINGS
    if not bindings.is_dir():
        return []
    licence = bundle / KERNEL_LICENCE
    own = licence.read_bytes() if _is_text(licence) else None
    out: list[Prose] = []
    for binding in sorted(path for path in bindings.iterdir() if path.is_dir()):
        copy = binding / KERNEL_LICENCE
        if not _is_text(copy):
            out.append(Prose(f"{BINDINGS}/{binding.name}: carries no {KERNEL_LICENCE}"))
        elif copy.read_bytes() != own:
            out.append(
                Prose(f"{BINDINGS}/{binding.name}: its {KERNEL_LICENCE} is not the bundle's")
            )
    return out


def ghc_version() -> GhcVersion:
    """Return the version of the GHC on the search path, raising when ghc names none."""
    read = run_capture([find_executable("ghc"), "--numeric-version"])
    if read.returncode != 0 or not read.stdout.strip():
        message = f"ghc --numeric-version names no version: {read.stderr.strip()}"
        raise LicenceUnreadError(message)
    return GhcVersion(read.stdout.strip())


def ghc_libffi() -> LibffiRelease:
    """Return the libffi release the GHC on the search path builds its runtime system with."""
    read = run_capture(
        [find_executable("ghc-pkg"), "field", "rts", "include-dirs", "--simple-output"]
    )
    directories = [Path(word) for word in read.stdout.split()] if read.returncode == 0 else []
    for directory in directories:
        header = directory / "ffi.h"
        if header.is_file():
            release = libffi_release(Prose(header.read_text(encoding="utf-8")))
            if release is not None:
                return release
    message = (
        f"no ffi.h naming a libffi release among the runtime's include directories {directories}"
    )
    raise LicenceUnreadError(message)


def agda_version() -> AgdaVersion:
    """Return the version of the Agda on the search path, raising when agda names none."""
    read = run_capture([find_executable("agda"), "--numeric-version"])
    if read.returncode != 0 or not read.stdout.strip():
        message = f"agda --numeric-version names no version: {read.stderr.strip()}"
        raise LicenceUnreadError(message)
    return AgdaVersion(read.stdout.strip())


def _arguments() -> argparse.Namespace:
    """Parse the command line."""
    parser = argparse.ArgumentParser(description="Stage and hold the bundle's licence texts.")
    commands = parser.add_subparsers(dest="command", required=True)
    check = commands.add_parser("check", help="hold the kept texts to the libraries")
    _ = check.add_argument("libraries", type=Path, nargs="+", help="the libraries bundled")
    staging = commands.add_parser("stage", help="copy each library's texts into a bundle")
    _ = staging.add_argument("bundle", type=Path, help="the bundle's root")
    _ = staging.add_argument("libraries", type=Path, nargs="+", help="the libraries bundled")
    bundle = commands.add_parser("check-bundle", help="hold a staged bundle's licence texts")
    _ = bundle.add_argument("bundle", type=Path, help="the bundle's root")
    return parser.parse_args()


def main() -> ExitStatus:
    """Run the command the command line names, reporting each finding."""
    args = _arguments()
    command = cast("Command", args.command)
    kept = REPO / KEPT
    try:
        depends = agda_depends(Prose((REPO / AGDA_LIB).read_text(encoding="utf-8")))
        versions = Versions(ghc_libffi(), agda_version(), depends)
        if command == "check":
            record = read_record(Prose((kept / RECORD).read_text(encoding="utf-8")))
            audit = read_audit(Prose((kept / AUDIT).read_text(encoding="utf-8")))
            libraries = cast("list[Path]", args.libraries)
            found = kept_findings(libraries, versions, ghc_version(), kept, record)
            found += audit_findings(record, audit, kept)
        elif command == "stage":
            bundle, libraries = cast("Path", args.bundle), cast("list[Path]", args.libraries)
            found = stage(bundle, libraries, versions, kept)
        else:
            found = bundle_findings(cast("Path", args.bundle), versions, kept)
    except (OSError, RuntimeError, YAMLError, LicenceUnreadError) as exc:
        emit(f"bundle-licences: {exc}; the licence texts are unchecked")
        return UNCHECKED
    for finding in found:
        emit(f"bundle-licences: {finding}")
    if found:
        return FOUND
    emit(f"bundle-licences: {_HELD[command]}")
    return HELD


if __name__ == "__main__":
    sys.exit(main())
