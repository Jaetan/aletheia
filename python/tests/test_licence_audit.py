# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.licence_audit``, the scan of the bundle's sources for licence notices.

A library's sources are found from its own licence text in the record: GHC's
tarball's ``rts/``, a package's ``.cabal`` directory, the libffi tarball GHC
carries, Agda's runtime parts, an Agda library's ``src/``.  A hit is a licence
file, a line saying where code came from, or a line granting a licence that is
neither a pointer at the package's own licence nor a restatement of it; tests,
documentation, examples, build tools and package descriptions are not read.
The scan reports each hit without a verdict and each verdict without a hit, and
``--write`` keeps the standing verdicts and leaves each new hit unjudged.  The
command line answers 0, 1 or 2 as its docstring says.
"""

from __future__ import annotations

import hashlib
import io
import tarfile
from typing import TYPE_CHECKING, NamedTuple, NewType, cast

import pytest
import yaml

from tools.bundle_licences import (
    AUDIT,
    KEPT,
    RECORD,
    Audit,
    Digest,
    Folder,
    LicenceUnreadError,
    Record,
    SourceName,
    SourcePath,
    TarballName,
    TextPath,
    Verdict,
    read_audit,
    read_record,
)
from tools.licence_audit import (
    FOUND,
    GHC_TARBALL,
    HEADER,
    HELD,
    LICENCE_FILE_LINE,
    UNCHECKED,
    Hit,
    Target,
    check_digests,
    file_hits,
    findings,
    main,
    package_root,
    restates,
    scan,
    tarball_files,
    tarball_hits,
    targets,
    written,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

TarballBytes = NewType("TarballBytes", bytes)
type Members = dict[SourcePath, Prose]


class _Ran(NamedTuple):
    """What one run of the command line did: its status and the lines it wrote."""

    status: ExitStatus
    said: list[Prose]


_MIT = Prose(
    "Permission is hereby granted, free of charge, to any person obtaining\n"
    + "a copy of this software and associated documentation files (the\n"
    + '"Software"), to deal in the Software without restriction.\n'
)
_GHC_LICENCE = Prose("The Glasgow Haskell Compiler License\n\nCopyright 2002.\n")
_BASE_LICENCE = Prose("This library (libraries/base) is derived from code.\nCopyright Glasgow.\n")
_AGDA = TarballName("Agda-2.8.0")
_STDLIB = TarballName("agda-stdlib-2.4")
_KEPT: dict[TextPath, Prose] = {
    TextPath("rts-1.0.2/LICENSE"): _GHC_LICENCE,
    TextPath("rts-1.0.2/LICENSE-xxHash"): Prose("Copyright Yann Collet.\n"),
    TextPath("base-4.19.2.0/LICENSE"): _BASE_LICENCE,
    TextPath("libffi-3.4.6/LICENSE"): Prose(f"libffi - Copyright (c) Anthony Green.\n\n{_MIT}"),
    TextPath("Agda-2.8.0/LICENSE"): Prose(f"Copyright (c) Agda authors.\n\n{_MIT}"),
    TextPath("standard-library-2.4/LICENCE"): Prose(f"Copyright (c) stdlib authors.\n\n{_MIT}"),
}
_SOURCE_OF = {
    TextPath("Agda-2.8.0/LICENSE"): _AGDA,
    TextPath("standard-library-2.4/LICENCE"): _STDLIB,
}
_LIBFFI: Members = {
    SourcePath("src/x86/ffi64.c"): Prose(f"/* ffi64.c - Copyright (c) 2013 Someone\n\n{_MIT}*/\n"),
    SourcePath("src/dlmalloc.c"): Prose("Doug Lea, released to the public domain.\n"),
    SourcePath("testsuite/libffi.call/x.c"): Prose("/* borrowed from somewhere */\n"),
    SourcePath("LICENSE"): Prose("not read: outside src/ and include/\n"),
}
_GHC: Members = {
    SourcePath("LICENSE"): _GHC_LICENCE,
    SourcePath("rts/xxhash.h"): Prose("/* xxHash\n * BSD 2-Clause License (https://x)\n */\n"),
    SourcePath("rts/RtsUtils.c"): Prose("/* borrowed from the MUSL libc project */\nint x;\n"),
    SourcePath("rts/linker/ELFRelocs/LICENSE-LLVM.TXT"): Prose("Copyright UIUC\n"),
    SourcePath("rts/win32/notes.txt"): Prose("taken from nowhere: not a source file\n"),
    SourcePath("libraries/base/base.cabal"): Prose("license: BSD-3-Clause\n"),
    SourcePath("libraries/base/LICENSE"): _BASE_LICENCE,
    SourcePath("libraries/base/Data/Functor/Utils.hs"): Prose(
        "-- Copied from the transformers package\n"
    ),
    SourcePath("libraries/base/Data/Old.hs"): Prose(
        "-- License: BSD-style (see LICENSE)\n-- License : BSD-3-Clause\n"
    ),
    SourcePath("libraries/base/tests/T1.hs"): Prose("-- stolen from a test\n"),
    SourcePath("libraries/base/tools/ucd2haskell/LICENSE"): Prose("Copyright Composewell\n"),
    SourcePath("libraries/other/base/base.cabal"): Prose("license: BSD3\n"),
    SourcePath("libraries/other/base/X.hs"): Prose("-- stolen from a deeper directory\n"),
}
_AGDA_MEMBERS: Members = {
    SourcePath("src/data/MAlonzo/src/MAlonzo/RTE.hs"): Prose("-- adapted from GHC's coerce\n"),
    SourcePath("src/data/lib/prim/Agda/Builtin/Nat.agda"): Prose("-- no notice\n"),
    SourcePath("src/full/Agda/Main.hs"): Prose("-- copied from elsewhere, not in a program\n"),
}
_STDLIB_MEMBERS: Members = {
    SourcePath("src/Data/Nat/Base.agda"): Prose(
        '-- A comparison view. Taken from "View from the left"\n'
    ),
    SourcePath("README.md"): Prose("taken from a readme: outside src/\n"),
}


def _tar(
    top: Prose, members: Members, nested: dict[SourcePath, TarballBytes] | None = None
) -> TarballBytes:
    """Return a gzipped tarball of ``members`` and ``nested`` tarballs under ``top``."""
    data = io.BytesIO()
    entries = [(path, text.encode("utf-8")) for path, text in members.items()]
    entries += [(path, bytes(raw)) for path, raw in (nested or {}).items()]
    with tarfile.open(fileobj=data, mode="w:gz") as tar:
        for path, raw in entries:
            info = tarfile.TarInfo(f"{top}/{path}")
            info.size = len(raw)
            tar.addfile(info, io.BytesIO(raw))
    return TarballBytes(data.getvalue())


def _tarballs(tmp_path: Path) -> dict[TarballName, Path]:
    """Write the fixture tarballs under ``tmp_path``, GHC's carrying libffi's; return them."""
    libffi = _tar(Prose("libffi-3.4.6"), _LIBFFI)
    raw = {
        GHC_TARBALL: _tar(
            Prose("ghc-9.8.4"), _GHC, {SourcePath("libffi-tarballs/libffi-3.4.6.tar.gz"): libffi}
        ),
        _AGDA: _tar(Prose("Agda-2.8.0"), _AGDA_MEMBERS),
        _STDLIB: _tar(Prose("agda-stdlib-2.4"), _STDLIB_MEMBERS),
    }
    out: dict[TarballName, Path] = {}
    for name, data in raw.items():
        out[name] = tmp_path / f"{name}.tar.gz"
        _ = out[name].write_bytes(data)
    return out


def _record_text(files: dict[TarballName, Path]) -> Prose:
    """Return a record of the fixture's kept texts, each tarball named with its SHA-256."""
    sha = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in files.items()}
    rows = "".join(
        f"  {path}:\n"
        + (f"    source: {_SOURCE_OF[path]}\n" if path in _SOURCE_OF else "")
        + f'    from: x\n    sha256: "{hashlib.sha256(str(text).encode()).hexdigest()}"\n'
        for path, text in _KEPT.items()
    )
    sources = "".join(
        f'  {name}:\n    url: https://example.org/{name}.tar.gz\n    sha256: "{sha[name]}"\n'
        for name in (_AGDA, _STDLIB)
    )
    return Prose(
        'ghc: "9.8.4"\ntarball:\n'
        + "  url: https://downloads.haskell.org/~ghc/9.8.4/ghc-9.8.4-src.tar.xz\n"
        + f'  sha256: "{sha[GHC_TARBALL]}"\nsources:\n{sources}texts:\n{rows}'
    )


def _kept(root: Path) -> Path:
    """Write the fixture's kept texts under ``root``; return ``root``."""
    for path, text in _KEPT.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        _ = (root / path).write_text(text, encoding="utf-8")
    return root


def _record(tmp_path: Path) -> tuple[Record, dict[TarballName, Path]]:
    """Return the fixture's record and the tarballs it names."""
    files = _tarballs(tmp_path)
    return read_record(_record_text(files)), files


_EXPECTED = sorted(
    [
        Hit(
            _AGDA,
            SourcePath("src/data/MAlonzo/src/MAlonzo/RTE.hs"),
            Prose("-- adapted from GHC's coerce"),
        ),
        Hit(
            GHC_TARBALL,
            SourcePath("libffi-tarballs/libffi-3.4.6.tar.gz:src/dlmalloc.c"),
            Prose("Doug Lea, released to the public domain."),
        ),
        Hit(
            GHC_TARBALL,
            SourcePath("libraries/base/Data/Functor/Utils.hs"),
            Prose("-- Copied from the transformers package"),
        ),
        Hit(
            GHC_TARBALL,
            SourcePath("libraries/base/Data/Old.hs"),
            Prose("-- License : BSD-3-Clause"),
        ),
        Hit(GHC_TARBALL, SourcePath("libraries/base/LICENSE"), LICENCE_FILE_LINE),
        Hit(
            GHC_TARBALL,
            SourcePath("rts/RtsUtils.c"),
            Prose("/* borrowed from the MUSL libc project */"),
        ),
        Hit(GHC_TARBALL, SourcePath("rts/linker/ELFRelocs/LICENSE-LLVM.TXT"), LICENCE_FILE_LINE),
        Hit(GHC_TARBALL, SourcePath("rts/xxhash.h"), Prose("* BSD 2-Clause License (https://x)")),
        Hit(
            _STDLIB,
            SourcePath("src/Data/Nat/Base.agda"),
            Prose('-- A comparison view. Taken from "View from the left"'),
        ),
    ]
)


# targets and package_root


def test_targets_names_each_librarys_sources_from_its_own_licence(tmp_path: Path) -> None:
    """A folder's LICENSE or LICENCE names the tarball and the folder fixes the directories."""
    record, _ = _record(tmp_path)
    agda_roots = [SourcePath("src/data/MAlonzo/"), SourcePath("src/data/lib/prim/")]
    libffi_roots = [SourcePath("src/"), SourcePath("include/")]
    assert targets(record) == [
        Target(Folder("Agda-2.8.0"), _AGDA, None, agda_roots),
        Target(Folder("base-4.19.2.0"), GHC_TARBALL, None, [SourcePath("<package>/base")]),
        Target(
            Folder("libffi-3.4.6"),
            GHC_TARBALL,
            SourcePath("libffi-tarballs/libffi-3.4.6.tar.gz"),
            libffi_roots,
        ),
        Target(Folder("rts-1.0.2"), GHC_TARBALL, None, [SourcePath("rts/")]),
        Target(Folder("standard-library-2.4"), _STDLIB, None, [SourcePath("src/")]),
    ]


def test_targets_reads_a_hyphenated_package_name_whole() -> None:
    """``ghc-boot-th-9.8.4`` names the package ghc-boot-th, its version the last part."""
    record = read_record(
        Prose(
            'ghc: "9.8.4"\ntarball:\n  url: https://example.org/ghc-9.8.4-src.tar.xz\n'
            + f'  sha256: "{"1" * 64}"\nsources: {{}}\ntexts:\n  ghc-boot-th-9.8.4/LICENSE:\n'
            + f'    from: x\n    sha256: "{"2" * 64}"\n'
        )
    )
    package = [SourcePath("<package>/ghc-boot-th")]
    assert targets(record) == [Target(Folder("ghc-boot-th-9.8.4"), GHC_TARBALL, None, package)]


def test_package_root_is_the_shallowest_directory_holding_the_cabal() -> None:
    """The directory of ``<package>.cabal`` or ``.cabal.in`` under libraries/, the shallowest."""
    names = [
        SourcePath("libraries/other/base/base.cabal"),
        SourcePath("libraries/base/base.cabal"),
        SourcePath("libraries/ghc-prim/ghc-prim.cabal.in"),
        SourcePath("utils/text/text.cabal"),
    ]
    assert package_root(names, Prose("base")) == SourcePath("libraries/base/")
    assert package_root(names, Prose("ghc-prim")) == SourcePath("libraries/ghc-prim/")
    assert package_root(names, Prose("text")) is None


# file_hits and restates


def test_file_hits_reads_provenance_and_foreign_grants() -> None:
    """A line saying where code came from, or granting another licence, is a hit, spaces folded."""
    text = Prose(
        "-- Borrowed from the cereal package.\n"
        + "--   License:   BSD-3-Clause\n"
        + "-- Derived from @primitive@ package.\n"
        + "-- derived from the flags\n"
        + "-- License: BSD-style (see the file LICENSE)\n"
        + "// SPDX-License-Identifier: MIT\n"
        + "-- subject to the Mozilla Public License, v. 2.0\n"
        + "-- plain code\n"
    )
    assert list(file_hits(text, Prose(""))) == [
        Prose("-- Borrowed from the cereal package."),
        Prose("-- License: BSD-3-Clause"),
        Prose("-- Derived from @primitive@ package."),
        Prose("// SPDX-License-Identifier: MIT"),
        Prose("-- subject to the Mozilla Public License, v. 2.0"),
    ]


def test_file_hits_skips_a_restatement_of_the_packages_own_licence() -> None:
    """A grant whose following lines restate the package's own licence is the package's own."""
    own = Prose(
        "permission is hereby granted free of charge to any person obtaining a copy of this "
        + "software and associated documentation files the software to deal in the software "
        + "without restriction"
    )
    assert not list(file_hits(_MIT, own))
    assert list(file_hits(_MIT, Prose("another licence"))) == [
        Prose("Permission is hereby granted, free of charge, to any person obtaining")
    ]


def test_file_hits_reads_a_grant_with_the_two_lines_after_it() -> None:
    """A restatement is read three lines at a time: a fourth line of other words leaves it own."""
    own = Prose(
        "redistribution and use in source and binary forms with or without modification are "
        + "permitted provided that"
    )
    text = Prose(
        "Redistribution and use in source\nand binary forms, with or without\n"
        + "modification, are permitted.\n-- An unrelated note.\n"
    )
    assert not list(file_hits(text, own))


def test_restates_needs_words_in_the_window() -> None:
    """An empty window restates nothing; a window's words inside the licence restate it."""
    assert not restates([Prose("---"), Prose("")], Prose("a b"))
    assert restates([Prose("A,"), Prose("b!")], Prose("x a b y"))
    assert not restates([Prose("a c")], Prose("x a b y"))


# scan


def test_scan_reads_every_librarys_sources_and_nothing_else(tmp_path: Path) -> None:
    """Every hit in the sources compiled in; tests, tools, other directories and docs left out."""
    record, files = _record(tmp_path)
    assert scan(files, record, _kept(tmp_path / "kept")) == _EXPECTED


def test_scan_reads_bytes_utf8_cannot_decode(tmp_path: Path) -> None:
    """A kept licence or a source holding a byte UTF-8 cannot decode is read, the byte replaced."""
    record, files = _record(tmp_path)
    kept = _kept(tmp_path / "kept")
    _ = (kept / "rts-1.0.2" / "LICENSE").write_bytes(b"\xff" + str(_GHC_LICENCE).encode())
    assert scan(files, record, kept) == _EXPECTED
    bad = {SourcePath("rts/Bad.c"): TarballBytes(b"\xff /* stolen from x */\n")}
    _ = (tmp_path / "bad.tar.gz").write_bytes(_tar(Prose("ghc-9.8.4"), {}, bad))
    with tarfile.open(tmp_path / "bad.tar.gz") as tar:
        hits = tarball_hits(tar, GHC_TARBALL, [SourcePath("rts/")], Prose(""))
    assert hits == [Hit(GHC_TARBALL, SourcePath("rts/Bad.c"), Prose("\ufffd /* stolen from x */"))]


# tarball files and digests


def test_tarball_files_names_each_scanned_tarball_by_its_compression(tmp_path: Path) -> None:
    """GHC's is ``ghc.tar.xz``, a source's ``<name>.tar.gz``."""
    record, _ = _record(tmp_path)
    assert tarball_files(record, tmp_path) == {
        _AGDA: tmp_path / "Agda-2.8.0.tar.gz",
        _STDLIB: tmp_path / "agda-stdlib-2.4.tar.gz",
        GHC_TARBALL: tmp_path / "ghc.tar.xz",
    }


def test_check_digests_refuses_an_absent_or_altered_tarball(tmp_path: Path) -> None:
    """Each tarball must be there and hash as the record says."""
    record, files = _record(tmp_path)
    check_digests(record, files)
    _ = files[_AGDA].write_bytes(b"altered")
    with pytest.raises(LicenceUnreadError, match="its SHA-256 is not the one"):
        check_digests(record, files)
    files[_AGDA].unlink()
    with pytest.raises(LicenceUnreadError, match="absent; download it"):
        check_digests(record, files)


# findings and written


_HIT = Hit(
    GHC_TARBALL, SourcePath("rts/RtsUtils.c"), Prose("/* borrowed from the MUSL libc project */")
)
_OLD = Hit(GHC_TARBALL, SourcePath("rts/Gone.c"), Prose("-- taken from gone"))


def _covered(hit: Hit, text: TextPath) -> Verdict:
    """Return the verdict that ``text`` covers ``hit``."""
    return Verdict(tarball=hit.tarball, path=hit.path, line=hit.line, covered_by=text)


def _dismissed(hit: Hit, reason: Prose) -> Verdict:
    """Return the verdict that ``hit`` owes nothing, for ``reason``."""
    return Verdict(tarball=hit.tarball, path=hit.path, line=hit.line, dismissed=reason)


def test_findings_names_each_hit_without_a_verdict_and_each_verdict_without_a_hit() -> None:
    """Hits and verdicts are held both ways."""
    musl = _covered(_HIT, TextPath("rts-1.0.2/LICENSE-musl"))
    assert not findings([_HIT], [musl])
    stray = _dismissed(Hit(GHC_TARBALL, SourcePath("x.c"), Prose("y")), Prose("z"))
    assert findings([_HIT, _OLD], [musl, stray]) == [
        Prose("ghc:rts/Gone.c: no verdict for '-- taken from gone'"),
        Prose("ghc:x.c: a verdict for 'y', which is no hit"),
    ]


def test_written_keeps_standing_verdicts_and_leaves_new_hits_unjudged(tmp_path: Path) -> None:
    """A standing verdict is kept, a new hit gets an empty covered_by, the tarballs recorded."""
    record, _ = _record(tmp_path)
    standing = [_dismissed(_HIT, Prose("ruled")), _covered(_OLD, TextPath("rts-1.0.2/LICENSE"))]
    new = Hit(GHC_TARBALL, SourcePath("rts/New.c"), Prose("-- stolen from new"))
    kept = Hit(GHC_TARBALL, SourcePath("rts/Kept.c"), Prose("-- stolen from kept"))
    audit = written(
        [_HIT, new, kept], [*standing, _covered(kept, TextPath("rts-1.0.2/LICENSE"))], record
    )
    assert audit["verdicts"] == [
        _dismissed(_HIT, Prose("ruled")),
        _covered(new, TextPath("")),
        _covered(kept, TextPath("rts-1.0.2/LICENSE")),
    ]
    sources = record["sources"]
    assert audit["tarballs"] == {
        _AGDA: Digest(sources[SourceName(_AGDA)]["sha256"]),
        _STDLIB: Digest(sources[SourceName(_STDLIB)]["sha256"]),
        GHC_TARBALL: Digest(record["tarball"]["sha256"]),
    }


# main


def _repo(tmp_path: Path, audit: Audit) -> tuple[Path, Path]:
    """Plant a repository and its tarballs under ``tmp_path``, with ``audit``; return both."""
    store = tmp_path / "tarballs"
    store.mkdir()
    files = _tarballs(store)
    for name, path in files.items():
        _ = path.rename(store / f"{name}{'.tar.xz' if name == GHC_TARBALL else '.tar.gz'}")
    repo = tmp_path / "repo"
    kept = _kept(repo / KEPT)
    named = {
        name: store / f"{name}{'.tar.xz' if name == GHC_TARBALL else '.tar.gz'}" for name in files
    }
    _ = (kept / RECORD).write_text(_record_text(named), encoding="utf-8")
    _ = (kept / AUDIT).write_text(HEADER + yaml.safe_dump(audit, sort_keys=False), encoding="utf-8")
    return repo, store


def _run(monkeypatch: pytest.MonkeyPatch, repo: Path, argv: list[Prose]) -> _Ran:
    """Run the command line over ``repo``; return what it did."""
    said: list[Prose] = []
    monkeypatch.setattr("tools.licence_audit.REPO", repo)
    monkeypatch.setattr("tools.licence_audit.emit", said.append)
    monkeypatch.setattr("sys.argv", ["licence_audit", *argv])
    return _Ran(main(), said)


def _judged(hits: list[Hit]) -> list[Verdict]:
    """Return a verdict for each of ``hits``."""
    return [_dismissed(hit, Prose("judged")) for hit in hits]


def test_main_wanted_prints_each_tarballs_url_and_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``wanted`` prints a URL and a path per tarball, tab-separated, and exits 0."""
    repo, store = _repo(tmp_path, Audit(tarballs={}, verdicts=[]))
    assert _run(monkeypatch, repo, [Prose("wanted"), Prose(str(store))]) == _Ran(
        HELD,
        [
            Prose(f"https://example.org/Agda-2.8.0.tar.gz\t{store / 'Agda-2.8.0.tar.gz'}"),
            Prose(
                f"https://example.org/agda-stdlib-2.4.tar.gz\t{store / 'agda-stdlib-2.4.tar.gz'}"
            ),
            Prose(
                "https://downloads.haskell.org/~ghc/9.8.4/ghc-9.8.4-src.tar.xz\t"
                + f"{store / 'ghc.tar.xz'}"
            ),
        ],
    )


def test_main_scan_holds_sources_whose_every_hit_has_its_verdict(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Every hit judged and every verdict a hit: exit 0."""
    repo, store = _repo(tmp_path, Audit(tarballs={}, verdicts=_judged(_EXPECTED)))
    assert _run(monkeypatch, repo, [Prose("scan"), Prose(str(store))]) == _Ran(
        HELD, [Prose("licence-audit: every hit in the bundle's sources has its verdict")]
    )


def test_main_scan_names_a_hit_without_a_verdict_and_exits_one(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A hit left unjudged exits 1, naming it."""
    repo, store = _repo(tmp_path, Audit(tarballs={}, verdicts=_judged(_EXPECTED[1:])))
    first = _EXPECTED[0]
    assert _run(monkeypatch, repo, [Prose("scan"), Prose(str(store))]) == _Ran(
        FOUND,
        [Prose(f"licence-audit: {first.tarball}:{first.path}: no verdict for {first.line!r}")],
    )


def test_main_scan_is_unchecked_without_a_tarball(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An absent tarball exits 2, never a pass."""
    repo, store = _repo(tmp_path, Audit(tarballs={}, verdicts=[]))
    (store / "ghc.tar.xz").unlink()
    assert _run(monkeypatch, repo, [Prose("scan"), Prose(str(store))]) == _Ran(
        UNCHECKED,
        [
            Prose(
                f"licence-audit: {store / 'ghc.tar.xz'}: absent; download it from the URL "
                + "`wanted` prints; the sources are unaudited"
            )
        ],
    )


def test_main_scan_is_unchecked_on_a_tarball_the_record_does_not_name(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tarball that does not hash as the record says exits 2 before it is read."""
    repo, store = _repo(tmp_path, Audit(tarballs={}, verdicts=_judged(_EXPECTED)))
    _ = (store / "Agda-2.8.0.tar.gz").write_bytes(b"altered")
    assert _run(monkeypatch, repo, [Prose("scan"), Prose(str(store))]) == _Ran(
        UNCHECKED,
        [
            Prose(
                f"licence-audit: {store / 'Agda-2.8.0.tar.gz'}: its SHA-256 is not the one "
                + "packaging/licenses/sources.yaml records; the sources are unaudited"
            )
        ],
    )


def test_main_scan_names_a_licence_file_left_unjudged(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A licence file in the sources is a hit reported as a licence file."""
    base = Hit(GHC_TARBALL, SourcePath("libraries/base/LICENSE"), LICENCE_FILE_LINE)
    judged = _judged([hit for hit in _EXPECTED if hit != base])
    repo, store = _repo(tmp_path, Audit(tarballs={}, verdicts=judged))
    assert _run(monkeypatch, repo, [Prose("scan"), Prose(str(store))]) == _Ran(
        FOUND,
        [Prose("licence-audit: ghc:libraries/base/LICENSE: no verdict for '(licence file)'")],
    )


def test_main_scan_write_rewrites_the_verdict_file(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``--write`` keeps the standing verdicts, adds each new hit unjudged, under the header."""
    repo, store = _repo(tmp_path, Audit(tarballs={}, verdicts=_judged(_EXPECTED[1:])))
    ran = _run(monkeypatch, repo, [Prose("scan"), Prose("--write"), Prose(str(store))])
    assert ran == _Ran(HELD, [Prose(f"licence-audit: wrote {KEPT / AUDIT}")])
    text = (repo / KEPT / AUDIT).read_text(encoding="utf-8")
    assert text.startswith(HEADER)
    assert text.splitlines()[:2] == [
        "# SPDX-FileCopyrightText: 2025 Nicolas Pelletier",
        "# SPDX-License-Identifier: BSD-2-Clause",
    ]
    assert text.splitlines()[3].startswith("# The licence audit of the sources compiled into")
    first = _EXPECTED[0]
    assert read_audit(Prose(text))["verdicts"][0] == _covered(first, TextPath(""))
    rows = cast("Audit", yaml.safe_load(text))["verdicts"]
    assert list(rows[0]) == ["tarball", "path", "line", "covered_by"]


@pytest.mark.parametrize("argv", [[], ["scan"]])
def test_main_refuses_a_command_line_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch, argv: list[Prose]
) -> None:
    """A missing command or directory is refused."""
    monkeypatch.setattr("sys.argv", ["licence_audit", *argv])
    with pytest.raises(SystemExit) as refused:
        _ = main()
    assert refused.value.code == ExitStatus(2)


def test_the_exit_statuses_are_the_ones_the_usage_states() -> None:
    """Held, found and unchecked exit 0, 1 and 2, as the module's usage says."""
    assert (ExitStatus(0), ExitStatus(1), ExitStatus(2)) == (HELD, FOUND, UNCHECKED)
