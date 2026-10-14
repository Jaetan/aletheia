# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Find the licence notices in the sources compiled into the bundle, and hold each to its verdict.

The bundle's libraries are compiled from the tarballs ``packaging/licenses/sources.yaml``
records: GHC's source tarball (the GHC packages, the runtime system, and the
libffi tarball it carries), Agda's (its runtime support, ``MAlonzo`` and
``Agda.Builtin``) and each Agda library's.  A library's own licence covers
what its authors wrote; code it takes from another work owes that work's
licence as well, the obligation being transitive.  The scan reads, in the
sources of each library the bundle carries, every licence file and every line
that grants a licence or says where code came from, and holds each such hit to
a verdict in ``packaging/licenses/audit.yaml``: the kept text that covers it,
or why it owes none.

A library's sources are found from the record: a folder's own licence text
(``LICENSE`` or ``LICENCE``) names its tarball (GHC's unless its ``source:``
names another), and the folder's name fixes the directories read: ``rts/`` for
the runtime system, the directory holding ``<package>.cabal`` for a GHC
package, ``src/`` and ``include/`` of the libffi tarball GHC carries,
``src/data/MAlonzo/`` and ``src/data/lib/prim/`` of Agda's, ``src/`` of an Agda
library's.  Tests, benchmarks, documentation, examples and build tools are not
compiled in and are not read, nor are package descriptions, whose licence field
is the package's own.

A line is a hit when it says where code came from (borrowed, vendored, taken,
copied, adapted, ported, lifted, stolen, ripped or cribbed from something;
derived from a named package, library, project or code; originally written or
contributed; based on someone's code; written based on; inspired by; a port
of; a version of someone's code; a ``Source:`` or ``From:`` URL; stolen), or
when it grants a licence (a licence's grant sentence, an SPDX identifier, a
``License:`` field, a work said to be under a licence or copyrighted by
someone), unless it points at the package's own licence file (``see the file
LICENSE``, not ``LICENSE-x``), is a BSD package's own ``License: BSD-style``
field, or, with the next two worded lines, restates the package's own licence
text, which contributors' files do.

``wanted DIR`` prints, per tarball, its URL and the path in DIR the scan reads
it from (``<name><suffix>``, ``ghc`` for GHC's), for a download to fill.
``scan DIR`` checks each against the record's SHA-256 and reports every hit
without a verdict and every verdict without a hit; ``--write`` rewrites the
verdict file instead, keeping each verdict whose hit remains, adding each new
hit with an empty verdict for a person to fill, and recording the tarballs
scanned.  The verdicts themselves are held by ``tools/bundle_licences.py``'s
``check``, which needs no tarball.

Exit 0 when every hit has its verdict; 1 when one has none or a verdict has
no hit; 2 when the record cannot be read or a tarball is absent or not the
one the record names.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import re
import sys
import tarfile
from contextlib import ExitStack
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, Literal, NamedTuple, cast

import yaml
from yaml.error import YAMLError

from tools._common import emit
from tools.bundle_licences import (
    AUDIT,
    GHC_TARBALL,
    KEPT,
    LICENCE_FILE_LINE,
    RECORD,
    REPO,
    Audit,
    Digest,
    Folder,
    LicenceUnreadError,
    Record,
    SourcePath,
    TarballName,
    TextPath,
    Verdict,
    read_audit,
    read_record,
    scanned_tarballs,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator

HELD, FOUND, UNCHECKED = ExitStatus(0), ExitStatus(1), ExitStatus(2)
AuditCommand = Literal["wanted", "scan"]

_SKIP = re.compile(r"/(tests?|testsuite|bench(mark)?s?|docs?|examples?|tools)/")
_LICENCE_NAME = re.compile(r"(?i)^(licen[cs]e|copying|notice|copyright)")
_PRIMARY = re.compile(r"^LICEN[CS]E$")
_SOURCE = re.compile(r"\.(hs|lhs|hsc|hs-boot|c|h|S|s|cmm|def|agda|lagda)$")
_GRANT = re.compile(
    r"(?i)(is hereby granted|permission is granted|redistribution and use in source"
    + r"|spdx-license-identifier|licen[cs]ed under|under the terms of|distributed under the"
    + r"|governed by an? .{0,40}licen|public domain|apache licen|mozilla public licen"
    + r"|general public licen|boost software licen|\bbsd[- ]?[23][- ]clause|\bmit licen"
    + r"|\b(bsd|mit|gpl|apache)-licen[cs]ed\b|copyrighted by|\bncsa\b|^\W*licen[cs]e\s*:)"
)
# A line pointing at the package's own licence file: ``see the file LICENSE``, not ``LICENSE-x``.
_OWN = re.compile(r"(?i)see (the )?(file )?(\S*/)?licen[cs]e(\.\w+)?(?![\w-])")
# A BSD package's header field naming its own licence: ``License : BSD-style``.
_OWN_BSD = re.compile(r"(?i)^\W*licen[cs]e\s*:\s*(bsd-?style|bsd3-style)\W*$")
# The words every BSD licence opens its conditions with, which mark a BSD package's own text.
_BSD_WORDS = Prose("redistribution and use in source and binary forms")
_PROVENANCE = re.compile(
    r"(?i)\b(borrowed|vendored|taken|copied|adapted|ported|lifted|stolen|ripped|cribbed) from\b"
    + r"|\bderived from (the )?[`'\"@]?[\w.-]+[`'\"@]? (package|library|project|code)\b"
    + r"|\boriginally (written|contributed)\b|\bbased on (the )?([\w.-]+ )?code\b"
    + r"|\bwritten based on\b|\binspired by\b|\ban? (\w+ )?port of\b"
    + r"|\bversion of the (\w+ ){0,3}code\b|^\W*(source|from)\s*:?\s*https?://|\(stolen\)"
)
_WORDS = re.compile(r"[^a-z0-9]+")
# A grant line and the worded lines after it, read together to see whether they restate a licence.
_WINDOW = 3
# The parts of Agda compiled into a program: its runtime support and its builtins.
_AGDA_ROOTS = [SourcePath("src/data/MAlonzo/"), SourcePath("src/data/lib/prim/")]
_PACKAGE = "<package>/"
# The verdict file opens on its licence header and what it is, ahead of what the scan writes.
HEADER = Prose(
    "# SPDX-FileCopyrightText: 2025 Nicolas Pelletier\n"
    + "# SPDX-License-Identifier: BSD-2-Clause\n"
    + "#\n"
    + "# The licence audit of the sources compiled into the bundle (tools/licence_audit.py):\n"
    + "# the tarballs scanned, and per hit (a licence file, or a line granting a licence or\n"
    + "# saying where code came from) the kept text that covers it or why it owes none.\n"
    + "# `python -m tools.licence_audit scan --write DIR` rewrites it, keeping each verdict\n"
    + "# whose hit remains; a new hit comes with an empty `covered_by:` to fill.\n"
)


class Hit(NamedTuple):
    """One licence notice in a tarball: where it is, and the line (or that it is a licence file)."""

    tarball: TarballName
    path: SourcePath
    line: Prose


class Target(NamedTuple):
    """The sources one bundled library is compiled from."""

    folder: Folder
    tarball: TarballName
    nested: SourcePath | None
    roots: list[SourcePath]


def _words(text: Prose) -> Prose:
    """Return ``text`` lowered to its words, one space apart, for comparing licence texts."""
    return Prose(_WORDS.sub(" ", text.lower()).strip())


def targets(record: Record) -> list[Target]:
    """Return the sources of each library the record keeps a licence folder for."""
    out: list[Target] = []
    for path, entry in sorted(record["texts"].items()):
        folder, _, name = path.partition("/")
        if not _PRIMARY.match(name):
            continue
        source = entry.get("source")
        tarball = GHC_TARBALL if source is None else TarballName(source)
        base = folder.rsplit("-", 1)[0]
        if tarball != GHC_TARBALL:
            roots = _AGDA_ROOTS if base == "Agda" else [SourcePath("src/")]
            out.append(Target(Folder(folder), tarball, None, roots))
        elif base == "rts":
            out.append(Target(Folder(folder), tarball, None, [SourcePath("rts/")]))
        elif base == "libffi":
            nested = SourcePath(f"libffi-tarballs/{folder}.tar.gz")
            roots = [SourcePath("src/"), SourcePath("include/")]
            out.append(Target(Folder(folder), tarball, nested, roots))
        else:
            out.append(Target(Folder(folder), tarball, None, [SourcePath(f"{_PACKAGE}{base}")]))
    return out


def _relative(member: tarfile.TarInfo) -> SourcePath:
    """Return a member's path without its tarball's top directory."""
    return SourcePath("/".join(PurePosixPath(member.name).parts[1:]))


def package_root(names: Iterable[SourcePath], package: Prose) -> SourcePath | None:
    """Return the shallowest directory under ``libraries/`` holding ``package``'s ``.cabal``."""
    cabal = {f"{package}.cabal", f"{package}.cabal.in"}
    found = sorted(
        (
            str(PurePosixPath(name).parent)
            for name in names
            if name.startswith("libraries/") and PurePosixPath(name).name in cabal
        ),
        key=len,
    )
    return SourcePath(f"{found[0]}/") if found else None


def restates(window: list[Prose], own: Prose) -> bool:
    """Say whether ``window``, a grant line and the lines after it, restates the licence ``own``.

    A window holding fewer than ``_WINDOW`` worded lines restates nothing: a lone
    grant line's few words fall inside any licence that opens the same way.
    """
    worded = [line for line in window if _words(line)][:_WINDOW]
    return len(worded) == _WINDOW and _words(Prose(" ".join(worded))) in own


def owns(line: Prose, own: Prose) -> bool:
    """Say whether ``line`` points at the package's own licence rather than granting another."""
    return bool(_OWN.search(line)) or (bool(_OWN_BSD.search(line)) and _BSD_WORDS in own)


def file_hits(text: Prose, own: Prose) -> Iterator[Prose]:
    """Yield each line of ``text`` that says where code came from or grants another licence."""
    lines = [Prose(line) for line in text.splitlines()]
    for at, line in enumerate(lines):
        if _PROVENANCE.search(line) or (
            _GRANT.search(line) and not owns(line, own) and not restates(lines[at:], own)
        ):
            yield Prose(" ".join(line.split()))


def tarball_hits(
    tar: tarfile.TarFile, name: TarballName, roots: list[SourcePath], own: Prose
) -> list[Hit]:
    """Return every hit in ``tar``'s files under ``roots``, tests and documentation aside."""
    out: list[Hit] = []
    for member in tar.getmembers():
        path = _relative(member)
        if not member.isfile() or not any(str(path).startswith(root) for root in roots):
            continue
        if _SKIP.search(path):
            continue
        if _LICENCE_NAME.match(PurePosixPath(path).name):
            out.append(Hit(name, path, LICENCE_FILE_LINE))
        elif _SOURCE.search(path):
            handle = tar.extractfile(member)
            text = Prose("" if handle is None else handle.read().decode("utf-8", errors="replace"))
            out.extend(Hit(name, path, line) for line in file_hits(text, own))
    return out


def _own_licence(record: Record, kept: Path, folder: Folder) -> Prose:
    """Return the words of ``folder``'s own licence text, as kept."""
    path = next(
        path
        for path in record["texts"]
        if path.startswith(f"{folder}/") and _PRIMARY.match(path.partition("/")[2])
    )
    return _words(Prose((kept / path).read_text(encoding="utf-8", errors="replace")))


def scan(tarballs: dict[TarballName, Path], record: Record, kept: Path) -> list[Hit]:
    """Return every hit in the sources of the libraries the record keeps licences for."""
    out: set[Hit] = set()
    with ExitStack() as stack:
        opened = {name: stack.enter_context(tarfile.open(path)) for name, path in tarballs.items()}
        for target in targets(record):
            out.update(
                _target_hits(
                    opened[target.tarball], target, _own_licence(record, kept, target.folder)
                )
            )
    return sorted(out)


def _target_hits(tar: tarfile.TarFile, target: Target, own: Prose) -> list[Hit]:
    """Return every hit in the sources of ``target``, read from its tarball ``tar``."""
    if target.nested is not None:
        inner = next(m for m in tar.getmembers() if _relative(m) == target.nested)
        handle = tar.extractfile(inner)
        data = io.BytesIO() if handle is None else io.BytesIO(handle.read())
        with tarfile.open(fileobj=data) as nested:
            found = tarball_hits(nested, target.tarball, target.roots, own)
        return [Hit(h.tarball, SourcePath(f"{target.nested}:{h.path}"), h.line) for h in found]
    roots = target.roots
    if roots[0].startswith(_PACKAGE):
        names = [_relative(m) for m in tar.getmembers()]
        root = package_root(names, Prose(roots[0].removeprefix(_PACKAGE)))
        roots = [] if root is None else [root]
    return tarball_hits(tar, target.tarball, roots, own)


def urls(record: Record) -> dict[TarballName, Prose]:
    """Return the URL the record names for each tarball."""
    return {GHC_TARBALL: record["tarball"]["url"]} | {
        TarballName(name): source["url"] for name, source in record["sources"].items()
    }


def digests(record: Record) -> dict[TarballName, Prose]:
    """Return the SHA-256 the record names for each tarball."""
    return {GHC_TARBALL: Prose(record["tarball"]["sha256"])} | {
        TarballName(name): Prose(source["sha256"]) for name, source in record["sources"].items()
    }


def tarball_files(record: Record, directory: Path) -> dict[TarballName, Path]:
    """Return where each scanned tarball sits in ``directory``: ``<name><suffix>``."""
    known = urls(record)
    wanted = scanned_tarballs(record)
    return {
        name: directory / f"{name}{'.tar.xz' if known[name].endswith('.tar.xz') else '.tar.gz'}"
        for name in wanted
    }


def check_digests(record: Record, files: dict[TarballName, Path]) -> None:
    """Raise ``LicenceUnreadError`` unless each tarball is the one the record names."""
    wanted = digests(record)
    for name, path in files.items():
        if not path.is_file():
            message = f"{path}: absent; download it from the URL `wanted` prints"
            raise LicenceUnreadError(message)
        if hashlib.sha256(path.read_bytes()).hexdigest() != wanted[name]:
            message = f"{path}: its SHA-256 is not the one {KEPT / RECORD} records"
            raise LicenceUnreadError(message)


def _hit(verdict: Verdict) -> Hit:
    """Return the hit ``verdict`` judges."""
    return Hit(verdict["tarball"], verdict["path"], verdict["line"])


def findings(found: list[Hit], verdicts: list[Verdict]) -> list[Prose]:
    """Return a finding per hit without a verdict, then per verdict without a hit."""
    judged = {_hit(verdict) for verdict in verdicts}
    return [
        *(
            Prose(f"{h.tarball}:{h.path}: no verdict for {h.line!r}")
            for h in found
            if h not in judged
        ),
        *(
            Prose(f"{h.tarball}:{h.path}: a verdict for {h.line!r}, which is no hit")
            for h in sorted(judged - set(found))
        ),
    ]


def written(found: list[Hit], verdicts: list[Verdict], record: Record) -> Audit:
    """Return the verdict file for ``found``: each standing verdict kept, each new hit unjudged."""
    standing = {_hit(verdict): verdict for verdict in verdicts}
    rows: list[Verdict] = []
    for hit in found:
        row = Verdict(tarball=hit.tarball, path=hit.path, line=hit.line)
        old = standing.get(hit)
        if old is not None and "dismissed" in old:
            row["dismissed"] = old["dismissed"]
        else:
            unjudged = TextPath("")
            row["covered_by"] = (
                old["covered_by"] if old is not None and "covered_by" in old else unjudged
            )
        rows.append(row)
    scanned = scanned_tarballs(record)
    return Audit(tarballs={name: Digest(digests(record)[name]) for name in scanned}, verdicts=rows)


def _arguments() -> argparse.Namespace:
    """Parse the command line."""
    parser = argparse.ArgumentParser(description="Audit the bundle's sources for licence notices.")
    commands = parser.add_subparsers(dest="command", required=True)
    for command, purpose in (
        ("wanted", "print each tarball's URL and path"),
        ("scan", "scan them"),
    ):
        sub = commands.add_parser(command, help=purpose)
        _ = sub.add_argument("directory", type=Path, help="where the tarballs are kept")
        if command == "scan":
            _ = sub.add_argument("--write", action="store_true", help="rewrite the verdict file")
    return parser.parse_args()


def _report(found: list[Hit], audit: Audit, record: Record, *, write: bool) -> ExitStatus:
    """Write the verdict file for ``found``, or report each hit and verdict out of step."""
    kept = REPO / KEPT
    if write:
        text = HEADER + yaml.safe_dump(written(found, audit["verdicts"], record), sort_keys=False)
        _ = (kept / AUDIT).write_text(text, encoding="utf-8")
        emit(f"licence-audit: wrote {KEPT / AUDIT}")
        return HELD
    problems = findings(found, audit["verdicts"])
    for problem in problems:
        emit(f"licence-audit: {problem}")
    if problems:
        return FOUND
    emit("licence-audit: every hit in the bundle's sources has its verdict")
    return HELD


def main() -> ExitStatus:
    """Print the tarballs wanted, or scan them and report or write the verdicts."""
    args = _arguments()
    kept = REPO / KEPT
    try:
        record = read_record(Prose((kept / RECORD).read_text(encoding="utf-8")))
        files = tarball_files(record, cast("Path", args.directory))
        if cast("AuditCommand", args.command) == "wanted":
            for name, path in files.items():
                emit(f"{urls(record)[name]}\t{path}")
            return HELD
        check_digests(record, files)
        found = scan(files, record, kept)
        audit = read_audit(Prose((kept / AUDIT).read_text(encoding="utf-8")))
    except (OSError, YAMLError, LicenceUnreadError, tarfile.TarError, StopIteration) as exc:
        emit(f"licence-audit: {exc}; the sources are unaudited")
        return UNCHECKED
    return _report(found, audit, record, write=cast("bool", args.write))


if __name__ == "__main__":
    sys.exit(main())
