# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.bundle_licences``: its reading, its tree check and its command line.

A bundled library's licence folder is its GHC package's name and version, the
runtime system's way aside, or ``libffi-<release>`` for libffi; any other
library has none.  The record holds a GHC version, an https URL and SHA-256
digests, or is unread.  The tree check holds the kept folders to the libraries
both ways, the record to the kept texts both ways and to the GHC, each text
naming a copyright, nothing else in the kept folders.  The command line answers
0, 1 or 2 as its docstring says.  Every process the tool would start is
answered by a stand-in, so no test starts one.  Staging and the bundle check
are in ``test_bundle_licences_staging.py``.
"""

from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path
from typing import Literal, NamedTuple

import pytest
from _licence_fixtures import (
    FFI,
    GMP,
    KEPT_TEXTS,
    KERNEL_LIBRARY,
    LIBFFI,
    LIBRARIES,
    NOTICE,
    RTS,
    SECOND_TEXT,
    STDLIB,
    TEXT,
    VERSIONS,
    Texts,
    make_bundle,
    plant,
    plant_strays,
    without,
)
from _processes import CommandWord

from tools.bundle_licences import (
    AGDA_LIB,
    AUDIT,
    BUNDLED,
    FOUND,
    HELD,
    KEPT,
    KERNEL,
    RECORD,
    UNCHECKED,
    AgdaLibrary,
    AgdaVersion,
    Folder,
    LibffiRelease,
    LicenceText,
    LicenceUnreadError,
    Record,
    SourceName,
    TextPath,
    Versions,
    agda_depends,
    agda_version,
    claims,
    folders_of,
    ghc_libffi,
    ghc_version,
    kept_findings,
    libffi_release,
    main,
    read_record,
)
from tools.sbom_generate import GhcVersion

from aletheia.common_types import ExitStatus, Prose

# One command line a stand-in process was asked to run, or the tool was given.
type Command = list[CommandWord]
type Answer = subprocess.CompletedProcess[Prose]


class _Ran(NamedTuple):
    """What one run of the command line did: its status and the lines it wrote."""

    status: ExitStatus
    said: list[Prose]


_GHC = GhcVersion("9.8.4")
_NO_SOURCES = Prose("sources: {}\n")
_FILEPATH = SourceName("filepath-1.4.2.2")
_FILEPATH_SOURCE = Prose(
    "sources:\n  filepath-1.4.2.2:\n"
    + "    url: https://hackage.haskell.org/package/filepath-1.4.2.2/filepath-1.4.2.2.tar.gz\n"
    + f'    sha256: "{"b" * 64}"\n'
)
_URL = Prose("https://downloads.haskell.org/~ghc/9.8.4/ghc-9.8.4-src.tar.xz")
_TARBALL_DIGEST = Prose("17e8188f3c8a5c2f73fb4e35d01032e8dc258835ec876d52c8ad8ee3d24b2fc5")
_NO_OUTPUT = Prose("")


def _header(release: LibffiRelease) -> Prose:
    """Return the opening of an ffi.h naming ``release``."""
    return Prose(
        "/* -----------------------------------------------------------------*-C-*-\n"
        + f"   libffi {release}\n"
        + "     - Copyright (c) 2011, 2014, 2019, 2021, 2022, 2024 Anthony Green\n"
    )


_HEADER = _header(LibffiRelease("3.4.6"))
_CHECK, _STAGE, _CHECK_BUNDLE = (
    CommandWord("check"),
    CommandWord("stage"),
    CommandWord("check-bundle"),
)
_WHERE = KEPT / RECORD


def _words(*words: CommandWord | Path) -> Command:
    """Return ``words`` as a command line."""
    return [CommandWord(str(word)) for word in words]


def _record_text(
    texts: Texts,
    ghc: GhcVersion = _GHC,
    url: Prose = _URL,
    sources: Prose = _NO_SOURCES,
    sourced: dict[TextPath, SourceName] | None = None,
) -> Prose:
    """Return a record of ``texts`` taken from GHC ``ghc``'s tarball at ``url``.

    ``sources`` is the record's ``sources:`` block, and ``sourced`` names the
    source of each text taken from one.
    """
    named = sourced or {}
    rows = "".join(
        f"  {path}:\n"
        + (f"    source: {named[path]}\n" if path in named else "")
        + f'    from: libraries/{path}\n    sha256: "{hashlib.sha256(text).hexdigest()}"\n'
        for path, text in texts.items()
    )
    return Prose(
        f'ghc: "{ghc}"\ntarball:\n  url: {url}\n  sha256: {_TARBALL_DIGEST}\n'
        + f"{sources}texts:\n{rows}"
    )


def _record(texts: Texts | None = None) -> Record:
    """Return the record of ``texts``, the kept ones by default, as the tree's record would read."""
    return read_record(_record_text(KEPT_TEXTS if texts is None else texts))


def _findings(
    tmp_path: Path,
    kept: Texts | None = None,
    record: Record | None = None,
    libraries: list[Path] | None = None,
    ghc: GhcVersion = _GHC,
) -> list[Prose]:
    """Return the tree check's findings for ``kept`` and its ``record``, the libraries and GHC.

    Each left out is the kept texts, their record and the fixture's libraries.
    """
    root = plant(tmp_path / "kept", KEPT_TEXTS if kept is None else kept)
    given = LIBRARIES if libraries is None else libraries
    return kept_findings(given, VERSIONS, ghc, root, _record() if record is None else record)


# folder_of, claims and libffi_release


@pytest.mark.parametrize(
    ("library", "folder"),
    [
        (TEXT, Folder("text-2.1.1")),
        (
            Path("/g/lib/x86_64-linux-ghc-9.8.4/libHSghc-boot-th-9.8.4-ea58-ghc9.8.4.so"),
            Folder("ghc-boot-th-9.8.4"),
        ),
        (RTS, Folder("rts-1.0.2")),
        (Path("libHSrts-1.0.2_thr_debug-ghc9.8.4.so"), Folder("rts-1.0.2")),
        (Path("libHSrts-1.0.2-ghc9.8.4.so"), Folder("rts-1.0.2")),
        (FFI, Folder("libffi-3.4.6")),
        (Path("libffi.so"), Folder("libffi-3.4.6")),
    ],
)
def test_folders_of_names_a_library_by_its_package_or_its_release(
    library: Path, folder: Folder
) -> None:
    """A package's folder is its name and version, the runtime's way aside; libffi's its release."""
    assert folders_of(library, VERSIONS) == [folder]


def test_folders_of_names_the_kernels_agda_and_each_agda_library_it_depends_on() -> None:
    """The kernel's folders are Agda's at its version, then each library depend: names."""
    versions = Versions(LIBFFI, AgdaVersion("2.9.1"), [STDLIB, AgdaLibrary("cubical-0.9")])
    assert folders_of(Path(f"/x/{KERNEL}"), versions) == [
        Folder("Agda-2.9.1"),
        Folder("standard-library-2.4"),
        Folder("cubical-0.9"),
    ]


@pytest.mark.parametrize(
    "library",
    [GMP, Path("libaletheia.so"), Path("libffix.so.1"), Path("ffi.so"), Path("libffi.sound.so")],
)
def test_folders_of_is_empty_for_a_library_the_tree_keeps_no_licence_for(library: Path) -> None:
    """A system library, a name only like the kernel's or libffi's has no kept folder."""
    assert folders_of(library, VERSIONS) == []


def test_claims_maps_each_folder_to_its_library_the_kernels_two_included() -> None:
    """The kernel claims both its folders."""
    assert claims([KERNEL_LIBRARY], VERSIONS).folders == {
        Folder("Agda-2.8.0"): KERNEL_LIBRARY,
        Folder("standard-library-2.4"): KERNEL_LIBRARY,
    }


@pytest.mark.parametrize(
    ("agda_lib", "depends"),
    [
        (
            Prose("name: aletheia\ndepend: standard-library-2.4\ninclude: src\n"),
            ["standard-library-2.4"],
        ),
        (Prose("depend: a-1 b-2\n  c-3\ninclude: src\n"), ["a-1", "b-2", "c-3"]),
        (Prose("name: x\ninclude: src\n"), []),
        (Prose("name: x\n  depend: a-1\n"), []),
    ],
)
def test_agda_depends_reads_every_library_depend_names(
    agda_lib: Prose, depends: list[Prose]
) -> None:
    """The libraries are the words of depend: and its indented continuations, in order."""
    assert agda_depends(agda_lib) == depends


def test_claims_maps_each_library_to_its_folder_and_names_the_rest() -> None:
    """Each library claims its folder; one with none is a finding naming it."""
    found = claims([TEXT, GMP, FFI], VERSIONS)
    assert found.folders == {Folder("text-2.1.1"): TEXT, Folder("libffi-3.4.6"): FFI}
    assert found.unknown == [Prose("libgmp.so.10: no licence is kept for it")]


def test_libffi_release_is_the_release_ffi_h_opens_on() -> None:
    """The release is the version the header's opening comment names."""
    assert libffi_release(_HEADER) == LibffiRelease("3.4.6")


@pytest.mark.parametrize(
    "header",
    [
        Prose("/* Building libffi.DLL with msvcc.sh */\n"),
        Prose("   Most of the API is documented in doc/libffi.texi.\n"),
        Prose("   xlibffi 3.4.6\n"),
        Prose("   libffi version 3\n"),
        Prose(""),
    ],
)
def test_libffi_release_is_none_when_the_header_names_no_release(header: Prose) -> None:
    """A header mentioning libffi with no release right after the name names none."""
    assert libffi_release(header) is None


# read_record


def test_read_record_reads_the_ghc_the_tarball_and_each_digest() -> None:
    """A record reads as its GHC, its tarball and each text's digest."""
    record = _record()
    assert (record["ghc"], record["tarball"]["url"]) == (_GHC, _URL)
    assert {path: entry["sha256"] for path, entry in record["texts"].items()} == {
        path: hashlib.sha256(text).hexdigest() for path, text in KEPT_TEXTS.items()
    }


_TARBALL = Prose(f"tarball:\n  url: {_URL}\n  sha256: {_TARBALL_DIGEST}\n{_NO_SOURCES}")
_GHC_LINE = Prose('ghc: "9.8.4"\n')
_ONE_SOURCE = Prose("sources:\n  x:\n    url: u\n")


@pytest.mark.parametrize(
    ("text", "reason"),
    [
        (Prose(f"{_TARBALL}texts: {{}}\n"), Prose("lacks the key 'ghc'")),
        (Prose(f"{_GHC_LINE}{_NO_SOURCES}texts: {{}}\n"), Prose("lacks the key 'tarball'")),
        (
            Prose(
                f"{_GHC_LINE}tarball:\n  url: {_URL}\n  sha256: {_TARBALL_DIGEST}\ntexts: {{}}\n"
            ),
            Prose("lacks the key 'sources'"),
        ),
        (
            Prose(f"{_GHC_LINE}tarball:\n  sha256: {_TARBALL_DIGEST}\n{_NO_SOURCES}texts: {{}}\n"),
            Prose("lacks the key 'url'"),
        ),
        (
            Prose(f"{_GHC_LINE}tarball:\n  url: {_URL}\n{_NO_SOURCES}texts: {{}}\n"),
            Prose("lacks the key 'sha256'"),
        ),
        (
            Prose(f"{_GHC_LINE}{_TARBALL}texts: {{}}\n".replace(_NO_SOURCES, _ONE_SOURCE)),
            Prose("lacks the key 'sha256'"),
        ),
        (Prose(f"{_GHC_LINE}{_TARBALL}"), Prose("lacks the key 'texts'")),
        (
            Prose(f"{_GHC_LINE}{_TARBALL}texts:\n  a/LICENSE:\n    from: x\n"),
            Prose("lacks the key 'sha256'"),
        ),
        (Prose(f"{_GHC_LINE}{_TARBALL}texts:\n"), Prose("is not shaped as a record: ")),
        (
            Prose(f"{_GHC_LINE}tarball:\n{_NO_SOURCES}texts: {{}}\n"),
            Prose("is not shaped as a record: "),
        ),
        (
            Prose(f"{_GHC_LINE}{_TARBALL}texts: {{}}\n".replace(_NO_SOURCES, "sources:\n")),
            Prose("is not shaped as a record: "),
        ),
        (
            Prose(f"ghc: 9.8.4\n{_TARBALL}texts: {{}}\n".replace(_TARBALL_DIGEST, "1234")),
            Prose("is not shaped as a record: "),
        ),
        (Prose("- a list\n"), Prose("is not shaped as a record: ")),
        (Prose(""), Prose("is not shaped as a record: ")),
    ],
)
def test_read_record_refuses_a_record_lacking_a_value(text: Prose, reason: Prose) -> None:
    """A record without one of its values, or not a mapping of mappings, is unread."""
    with pytest.raises(LicenceUnreadError, match=f"^{_WHERE} {reason}"):
        _ = read_record(text)


@pytest.mark.parametrize(
    ("field", "value", "kind"),
    [
        ("ghc", "9", "a GHC version"),
        ("ghc", "9.8.x", "a GHC version"),
        ("ghc", "v9.8.4", "a GHC version"),
        ("url", "http://downloads.haskell.org/ghc-9.8.4-src.tar.xz", "an https URL"),
        ("url", "https://", "an https URL"),
        ("url", "https://a b", "an https URL"),
        ("tarball", "0" * 63, "a SHA-256 digest"),
        ("tarball", "0" * 65, "a SHA-256 digest"),
        ("tarball", "A" * 64, "a SHA-256 digest"),
        ("tarball", "g" * 64, "a SHA-256 digest"),
        ("text", "", "a SHA-256 digest"),
        ("source_url", "ftp://example.org/x.tar.gz", "an https URL"),
        ("source_sha", "0" * 63, "a SHA-256 digest"),
    ],
)
def test_read_record_refuses_a_value_not_of_its_shape(
    field: Literal["ghc", "url", "tarball", "text", "source_url", "source_sha"],
    value: Prose,
    kind: Prose,
) -> None:
    """A GHC version, each https URL and each SHA-256 digest are refused unless of their shape."""
    shaped = {
        "ghc": "9.8.4",
        "url": _URL,
        "tarball": _TARBALL_DIGEST,
        "text": "0" * 64,
        "source_url": "https://example.org/x.tar.gz",
        "source_sha": "c" * 64,
    } | {field: value}
    text = Prose(
        f'ghc: "{shaped["ghc"]}"\ntarball:\n  url: "{shaped["url"]}"\n'
        + f'  sha256: "{shaped["tarball"]}"\n'
        + f'sources:\n  x:\n    url: "{shaped["source_url"]}"\n'
        + f'    sha256: "{shaped["source_sha"]}"\n'
        + f'texts:\n  a/LICENSE:\n    source: x\n    from: x\n    sha256: "{shaped["text"]}"\n'
    )
    with pytest.raises(LicenceUnreadError, match=f"^{_WHERE}: {value!r} is not {kind}$"):
        _ = read_record(text)


# kept_findings


def test_kept_findings_holds_texts_that_match_their_record_and_libraries(tmp_path: Path) -> None:
    """Every library with its folder, every folder claimed, every text recorded: no finding."""
    assert not _findings(tmp_path)


def test_kept_findings_names_a_library_the_tree_keeps_no_licence_for(tmp_path: Path) -> None:
    """A bundled library that is neither a GHC package nor libffi is a finding."""
    assert _findings(tmp_path, libraries=[*LIBRARIES, GMP]) == [
        Prose("libgmp.so.10: no licence is kept for it")
    ]


def test_kept_findings_names_a_library_whose_folder_is_absent(tmp_path: Path) -> None:
    """A library whose folder is not kept is a finding."""
    kept = without(Folder("text-2.1.1"))
    assert _findings(tmp_path, kept=kept, record=_record(kept)) == [
        Prose(f"{TEXT.name}: {KEPT}/text-2.1.1/ keeps no licence text")
    ]


def test_kept_findings_names_a_library_whose_folder_holds_no_text(tmp_path: Path) -> None:
    """A folder that is kept but holds no file keeps no licence text."""
    kept = without(Folder("text-2.1.1"))
    (tmp_path / "kept" / "text-2.1.1").mkdir(parents=True)
    assert _findings(tmp_path, kept=kept, record=_record(kept)) == [
        Prose(f"{TEXT.name}: {KEPT}/text-2.1.1/ keeps no licence text")
    ]


def test_kept_findings_names_a_folder_no_library_claims(tmp_path: Path) -> None:
    """A folder for a library the bundle does not carry is a finding."""
    kept = {**KEPT_TEXTS, TextPath("base-4.18.3.0/LICENSE"): NOTICE}
    assert _findings(tmp_path, kept=kept, record=_record(kept)) == [
        Prose(f"{KEPT}/base-4.18.3.0/: kept for no library the bundle carries")
    ]


def test_kept_findings_names_a_libffi_folder_for_another_release(tmp_path: Path) -> None:
    """A libffi folder for a release GHC does not build with fails both ways."""
    kept = {**without(Folder("libffi-3.4.6")), TextPath("libffi-3.4.5/LICENSE"): NOTICE}
    assert _findings(tmp_path, kept=kept, record=_record(kept)) == [
        Prose(f"{FFI.name}: {KEPT}/libffi-3.4.6/ keeps no licence text"),
        Prose(f"{KEPT}/libffi-3.4.5/: kept for no library the bundle carries"),
    ]


def test_kept_findings_names_a_record_of_another_ghc(tmp_path: Path) -> None:
    """A record of a GHC that is not the search path's is a finding."""
    assert _findings(tmp_path, ghc=GhcVersion("9.10.1")) == [
        Prose(f"{_WHERE}: records GHC {_GHC}, the search path's is 9.10.1")
    ]


@pytest.mark.parametrize(
    "url",
    [
        Prose("https://downloads.haskell.org/~ghc/9.8.3/ghc-9.8.3-src.tar.xz"),
        Prose("https://downloads.haskell.org/~ghc/9.8.4/ghc-9.8.4-testsuite.tar.xz"),
        Prose("https://downloads.haskell.org/~ghc/9.8.4/xghc-9.8.4-src.tar.xz"),
    ],
)
def test_kept_findings_names_a_tarball_that_is_not_the_recorded_ghcs(
    tmp_path: Path, url: Prose
) -> None:
    """The record's tarball is the source tarball of the GHC it records, or a finding."""
    record = read_record(_record_text(KEPT_TEXTS, url=url))
    assert _findings(tmp_path, record=record) == [
        Prose(f"{_WHERE}: its tarball is not GHC {_GHC}'s source")
    ]


def test_kept_findings_holds_a_text_taken_from_a_recorded_source(tmp_path: Path) -> None:
    """A text naming an upstream tarball the record names, used by it, holds."""
    sourced = {TextPath("text-2.1.1/LICENSE"): _FILEPATH}
    record = read_record(_record_text(KEPT_TEXTS, sources=_FILEPATH_SOURCE, sourced=sourced))
    assert not _findings(tmp_path, record=record)


def test_kept_findings_names_a_text_naming_a_source_not_recorded(tmp_path: Path) -> None:
    """A text naming an upstream tarball the record does not name is a finding, per text."""
    sourced = {TextPath("text-2.1.1/LICENSE"): _FILEPATH, SECOND_TEXT: _FILEPATH}
    record = read_record(_record_text(KEPT_TEXTS, sourced=sourced))
    assert _findings(tmp_path, record=record) == [
        Prose(f"{_WHERE}: {path} names the source {_FILEPATH}, which it does not record")
        for path in sorted(sourced)
    ]


def test_kept_findings_names_a_source_no_text_names(tmp_path: Path) -> None:
    """An upstream tarball the record names that no text was taken from is a finding."""
    record = read_record(_record_text(KEPT_TEXTS, sources=_FILEPATH_SOURCE))
    assert _findings(tmp_path, record=record) == [
        Prose(f"{_WHERE}: records the source {_FILEPATH}, which no text names")
    ]


def test_kept_findings_names_a_text_its_record_lacks(tmp_path: Path) -> None:
    """A kept text the record does not name is a finding."""
    kept = {**KEPT_TEXTS, TextPath("text-2.1.1/NOTICE"): NOTICE}
    assert _findings(tmp_path, kept=kept) == [Prose(f"{KEPT}/text-2.1.1/NOTICE: not in {_WHERE}")]


def test_kept_findings_names_a_recorded_text_not_kept(tmp_path: Path) -> None:
    """A text the record names that the tree does not keep is a finding."""
    kept = {path: text for path, text in KEPT_TEXTS.items() if path != SECOND_TEXT}
    assert _findings(tmp_path, kept=kept) == [
        Prose(f"{_WHERE}: records {SECOND_TEXT}, which is not kept")
    ]


def test_kept_findings_names_a_text_whose_digest_is_not_recorded(tmp_path: Path) -> None:
    """A kept text whose bytes moved since the record was taken is a finding."""
    kept = {**KEPT_TEXTS, TextPath("text-2.1.1/LICENSE"): LicenceText(NOTICE + b"\n")}
    assert _findings(tmp_path, kept=kept) == [
        Prose(f"{KEPT}/text-2.1.1/LICENSE: its SHA-256 is not the one {_WHERE} records")
    ]


@pytest.mark.parametrize(
    "text",
    [
        LicenceText(b"All rights reserved.\n"),
        LicenceText(b""),
        LicenceText(b"\xff\xfe copy right\n"),
    ],
)
def test_kept_findings_names_a_text_naming_no_copyright(tmp_path: Path, text: LicenceText) -> None:
    """A kept text with no copyright notice is a finding, whatever its bytes decode to."""
    kept = {**KEPT_TEXTS, TextPath("text-2.1.1/LICENSE"): text}
    assert _findings(tmp_path, kept=kept, record=_record(kept)) == [
        Prose(f"{KEPT}/text-2.1.1/LICENSE: names no copyright")
    ]


@pytest.mark.parametrize(
    "text", [LicenceText(b"COPYRIGHT 2008 Tom Harper\n"), LicenceText(b"\xff Copyright 2008\n")]
)
def test_kept_findings_reads_a_copyright_in_any_case_and_any_bytes(
    tmp_path: Path, text: LicenceText
) -> None:
    """A notice spelled COPYRIGHT, or beside bytes UTF-8 cannot decode, is a copyright notice."""
    kept = {**KEPT_TEXTS, TextPath("text-2.1.1/LICENSE"): text}
    assert not _findings(tmp_path, kept=kept, record=_record(kept))


def test_kept_findings_takes_the_record_and_the_audit_beside_the_folders(tmp_path: Path) -> None:
    """The record and the audit kept beside the folders are no strays."""
    root = plant(tmp_path / "kept", KEPT_TEXTS)
    _ = (root / RECORD).write_text(_record_text(KEPT_TEXTS), encoding="utf-8")
    _ = (root / AUDIT).write_text("verdicts: []\n", encoding="utf-8")
    assert not kept_findings(LIBRARIES, VERSIONS, _GHC, root, _record())


def test_kept_findings_names_every_stray_in_the_kept_folders(tmp_path: Path) -> None:
    """A nested folder, a file beside the folders, a link to a file or folder: each a finding."""
    root = plant(tmp_path / "kept", KEPT_TEXTS)
    outside = tmp_path / "outside"
    _ = outside.write_bytes(NOTICE)
    strays = plant_strays(root, outside)
    assert kept_findings(LIBRARIES, VERSIONS, _GHC, root, _record()) == [
        Prose(f"{KEPT}/{path}: not a licence text in a library's folder") for path in strays
    ]


# ghc_version and ghc_libffi


def _done(cmd: Command, status: ExitStatus, out: Prose, err: Prose = _NO_OUTPUT) -> Answer:
    """Return what a stand-in process answers: ``cmd``, its status and its two outputs."""
    return subprocess.CompletedProcess(cmd, status, out, err)


def _answering(
    monkeypatch: pytest.MonkeyPatch, answers: dict[CommandWord, Answer]
) -> list[Command]:
    """Answer each program by its canned answer; return the commands asked."""
    asked: list[Command] = []

    def answer(cmd: Command) -> Answer:
        """Record ``cmd`` and answer it as its program would."""
        asked.append(cmd)
        return answers[cmd[0]]

    def found(name: CommandWord) -> CommandWord:
        """Resolve ``name`` to itself, so the commands read as their program names."""
        return name

    monkeypatch.setattr("tools.bundle_licences.find_executable", found)
    monkeypatch.setattr("tools.bundle_licences.run_capture", answer)
    return asked


_GHC_ASKED = _words(CommandWord("ghc"), CommandWord("--numeric-version"))
_GHC_PKG_ASKED = [
    CommandWord(word) for word in ("ghc-pkg", "field", "rts", "include-dirs", "--simple-output")
]
_AGDA_ASKED = _words(CommandWord("agda"), CommandWord("--numeric-version"))
# The Agda library file the repository holds at its root, by the name it has there.
_AGDA_LIB = Path("aletheia.agda-lib")


def test_agda_version_is_what_agda_prints(monkeypatch: pytest.MonkeyPatch) -> None:
    """The version is agda's numeric version, stripped."""
    answer = _done(_AGDA_ASKED, HELD, Prose("2.8.0\n"))
    asked = _answering(monkeypatch, {CommandWord("agda"): answer})
    assert agda_version() == AgdaVersion("2.8.0")
    assert asked == [_AGDA_ASKED]


@pytest.mark.parametrize(
    ("status", "out"), [(FOUND, Prose("2.8.0\n")), (HELD, Prose("\n")), (HELD, Prose(""))]
)
def test_agda_version_refuses_an_agda_naming_no_version(
    monkeypatch: pytest.MonkeyPatch, status: ExitStatus, out: Prose
) -> None:
    """An agda that fails, or prints nothing, names no version."""
    answer = _done(_AGDA_ASKED, status, out, Prose("agda: broken\n"))
    _ = _answering(monkeypatch, {CommandWord("agda"): answer})
    with pytest.raises(
        LicenceUnreadError, match=r"^agda --numeric-version names no version: agda: broken$"
    ):
        _ = agda_version()


def test_ghc_version_is_what_ghc_prints(monkeypatch: pytest.MonkeyPatch) -> None:
    """The version is ghc's numeric version, stripped."""
    asked = _answering(monkeypatch, {CommandWord("ghc"): _done(_GHC_ASKED, HELD, Prose("9.8.4\n"))})
    assert ghc_version() == _GHC
    assert asked == [_GHC_ASKED]


@pytest.mark.parametrize(
    ("status", "out"), [(FOUND, Prose("9.8.4\n")), (HELD, Prose("\n")), (HELD, Prose(""))]
)
def test_ghc_version_refuses_a_ghc_naming_no_version(
    monkeypatch: pytest.MonkeyPatch, status: ExitStatus, out: Prose
) -> None:
    """A ghc that fails, or prints nothing, names no version."""
    answer = _done(_GHC_ASKED, status, out, Prose("ghc: broken\n"))
    _ = _answering(monkeypatch, {CommandWord("ghc"): answer})
    with pytest.raises(
        LicenceUnreadError, match=r"^ghc --numeric-version names no version: ghc: broken$"
    ):
        _ = ghc_version()


def test_ghc_libffi_reads_the_first_ffi_h_naming_a_release(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Of the runtime's include directories, the first whose ffi.h names a release answers."""
    none, unnamed, named, later = (
        tmp_path / name for name in ("none", "unnamed", "named", "later")
    )
    for directory in (none, unnamed, named, later):
        directory.mkdir()
    _ = (unnamed / "ffi.h").write_text("/* no release here */\n", encoding="utf-8")
    _ = (named / "ffi.h").write_text(_HEADER, encoding="utf-8")
    _ = (later / "ffi.h").write_text(_header(LibffiRelease("3.4.7")), encoding="utf-8")
    out = Prose(f"{none} {unnamed}\n{named}\n{later}\n")
    asked = _answering(monkeypatch, {CommandWord("ghc-pkg"): _done(_GHC_PKG_ASKED, HELD, out)})
    assert ghc_libffi() == LIBFFI
    assert asked == [_GHC_PKG_ASKED]


@pytest.mark.parametrize("status", [HELD, FOUND])
def test_ghc_libffi_refuses_include_directories_with_no_named_release(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, status: ExitStatus
) -> None:
    """No ffi.h naming a release, or a ghc-pkg that fails, leaves libffi's release unread."""
    header = _HEADER if status == FOUND else Prose("/* none */\n")
    _ = (tmp_path / "ffi.h").write_text(header, encoding="utf-8")
    answer = _done(_GHC_PKG_ASKED, status, Prose(f"{tmp_path}\n"))
    _ = _answering(monkeypatch, {CommandWord("ghc-pkg"): answer})
    with pytest.raises(LicenceUnreadError, match=r"^no ffi\.h naming a libffi release"):
        _ = ghc_libffi()


# main


def _prepare(
    monkeypatch: pytest.MonkeyPatch,
    repo: Path,
    argv: Command,
    ghc: Answer | None = None,
    agda: Answer | None = None,
) -> list[Prose]:
    """Set the command line ``argv`` over the tree under ``repo``; return the lines it writes."""
    said: list[Prose] = []

    def emit(message: Prose) -> None:
        """Record one line the tool writes."""
        said.append(message)

    include = repo / "include"
    include.mkdir(parents=True, exist_ok=True)
    _ = (include / "ffi.h").write_text(_HEADER, encoding="utf-8")
    if not (repo / _AGDA_LIB).exists():
        _ = (repo / _AGDA_LIB).write_text(f"depend: {STDLIB}\n", encoding="utf-8")
    _ = _answering(
        monkeypatch,
        {
            CommandWord("ghc"): ghc or _done(_GHC_ASKED, HELD, Prose("9.8.4\n")),
            CommandWord("ghc-pkg"): _done(_GHC_PKG_ASKED, HELD, Prose(f"{include}\n")),
            CommandWord("agda"): agda or _done(_AGDA_ASKED, HELD, Prose("2.8.0\n")),
        },
    )
    monkeypatch.setattr("tools.bundle_licences.emit", emit)
    monkeypatch.setattr("tools.bundle_licences.REPO", repo)
    monkeypatch.setattr("sys.argv", ["bundle_licences", *argv])
    return said


def _run_main(
    monkeypatch: pytest.MonkeyPatch, repo: Path, argv: Command, ghc: Answer | None = None
) -> _Ran:
    """Run the command line ``argv`` over the tree under ``repo``; return what it did."""
    said = _prepare(monkeypatch, repo, argv, ghc)
    return _Ran(main(), said)


def _plant_tree(repo: Path) -> Path:
    """Write the kept texts, their record and an audit of GHC's tarball under ``repo``.

    The audit's path is spelled as the tree holds it, so the module's name for it is held.
    """
    _ = plant(repo / KEPT, KEPT_TEXTS)
    _ = (repo / _WHERE).write_text(_record_text(KEPT_TEXTS), encoding="utf-8")
    audit = f'tarballs:\n  ghc: "{_TARBALL_DIGEST}"\nverdicts: []\n'
    _ = (repo / "packaging" / "licenses" / "audit.yaml").write_text(audit, encoding="utf-8")
    return repo


def test_main_check_holds_a_tree_that_keeps_every_licence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``check`` over a tree keeping every library's texts exits 0, saying so."""
    repo = _plant_tree(tmp_path)
    assert _run_main(monkeypatch, repo, _words(_CHECK, *LIBRARIES)) == _Ran(
        HELD, [Prose("bundle-licences: the kept licence texts hold for every library given")]
    )


def test_main_check_reports_each_finding_and_exits_one(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``check`` over a tree lacking a library's folder exits 1, naming it."""
    repo = _plant_tree(tmp_path)
    ran = _run_main(monkeypatch, repo, _words(_CHECK, *LIBRARIES, GMP))
    assert ran == _Ran(FOUND, [Prose("bundle-licences: libgmp.so.10: no licence is kept for it")])


def test_main_check_names_the_kernels_folder_for_the_agda_on_the_search_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``check`` asks agda its version, so another Agda's kernel folder fails both ways."""
    repo = _plant_tree(tmp_path)
    said = _prepare(
        monkeypatch,
        repo,
        _words(_CHECK, *LIBRARIES),
        agda=_done(_AGDA_ASKED, HELD, Prose("2.9.1\n")),
    )
    assert (main(), said) == (
        FOUND,
        [
            Prose(f"bundle-licences: {KERNEL}: {KEPT}/Agda-2.9.1/ keeps no licence text"),
            Prose(f"bundle-licences: {KEPT}/Agda-2.8.0/: kept for no library the bundle carries"),
        ],
    )


def test_main_check_reads_the_kernels_agda_libraries_from_aletheia_agda_lib(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``check`` reads depend: in aletheia.agda-lib, so another library's folder is asked for."""
    repo = _plant_tree(tmp_path)
    _ = (repo / _AGDA_LIB).write_text("depend: standard-library-2.5\n", encoding="utf-8")
    assert _run_main(monkeypatch, repo, _words(_CHECK, *LIBRARIES)) == _Ran(
        FOUND,
        [
            Prose(f"bundle-licences: {KERNEL}: {KEPT}/standard-library-2.5/ keeps no licence text"),
            Prose(
                f"bundle-licences: {KEPT}/standard-library-2.4/: "
                + "kept for no library the bundle carries"
            ),
        ],
    )


def test_main_is_unchecked_without_aletheia_agda_lib(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A repository without aletheia.agda-lib cannot say what the kernel compiles in: exit 2."""
    repo = _plant_tree(tmp_path)
    said = _prepare(monkeypatch, repo, _words(_CHECK, *LIBRARIES))
    (repo / _AGDA_LIB).unlink()
    assert main() == UNCHECKED
    assert said[0].endswith("; the licence texts are unchecked")
    assert str(AGDA_LIB) in said[0]


def test_main_check_holds_the_record_to_the_ghc_on_the_search_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``check`` asks ghc its version and finds a record of another GHC."""
    repo = _plant_tree(tmp_path)
    ghc = _done(_GHC_ASKED, HELD, Prose("9.10.1\n"))
    assert _run_main(monkeypatch, repo, _words(_CHECK, *LIBRARIES), ghc) == _Ran(
        FOUND, [Prose(f"bundle-licences: {_WHERE}: records GHC 9.8.4, the search path's is 9.10.1")]
    )


def test_main_check_reads_libffi_from_the_ghc_on_the_search_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``check`` reads libffi's release from GHC's ffi.h, so another release fails both ways."""
    repo = _plant_tree(tmp_path)
    said = _prepare(monkeypatch, repo, _words(_CHECK, *LIBRARIES))
    _ = (repo / "include" / "ffi.h").write_text(_header(LibffiRelease("3.4.7")), encoding="utf-8")
    assert (main(), said) == (
        FOUND,
        [
            Prose(f"bundle-licences: {FFI.name}: {KEPT}/libffi-3.4.7/ keeps no licence text"),
            Prose(f"bundle-licences: {KEPT}/libffi-3.4.6/: kept for no library the bundle carries"),
        ],
    )


def test_main_stage_then_check_bundle_hold_a_staged_bundle(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``stage`` copies the texts and ``check-bundle`` then holds the bundle, each exiting 0."""
    repo = _plant_tree(tmp_path / "repo")
    bundle = make_bundle(tmp_path, LIBRARIES, {}, kernel_licence=True)
    staged = _run_main(monkeypatch, repo, _words(_STAGE, bundle, *LIBRARIES))
    checked = _run_main(monkeypatch, repo, _words(_CHECK_BUNDLE, bundle))
    assert (staged, checked) == (
        _Ran(HELD, [Prose("bundle-licences: each library's licence texts are staged")]),
        _Ran(
            HELD, [Prose("bundle-licences: every library the bundle carries has its licence text")]
        ),
    )


def test_main_check_bundle_reports_a_library_without_its_licence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``check-bundle`` over a bundle staged without licences exits 1, naming each library."""
    repo = _plant_tree(tmp_path / "repo")
    bundle = make_bundle(tmp_path, [Path(KERNEL), FFI], {}, kernel_licence=True)
    assert _run_main(monkeypatch, repo, _words(_CHECK_BUNDLE, bundle)) == _Ran(
        FOUND,
        [
            Prose(f"bundle-licences: lib/{KERNEL}: {BUNDLED}/Agda-2.8.0/ holds no licence text"),
            Prose(
                f"bundle-licences: lib/{FFI.name}: {BUNDLED}/libffi-3.4.6/ holds no licence text"
            ),
            Prose(
                f"bundle-licences: lib/{KERNEL}: {BUNDLED}/standard-library-2.4/ "
                + "holds no licence text"
            ),
        ],
    )


def test_main_stage_reports_a_library_with_no_kept_text(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``stage`` for a library the tree keeps nothing for exits 1, naming it."""
    repo = _plant_tree(tmp_path / "repo")
    assert _run_main(monkeypatch, repo, _words(_STAGE, tmp_path / "bundle", GMP)) == _Ran(
        FOUND,
        [Prose(f"bundle-licences: {GMP.name}: no licence is kept for it")],
    )


def test_main_check_bundle_is_unchecked_without_lib(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A bundle without lib/ cannot be checked: exit 2, never a pass."""
    repo = _plant_tree(tmp_path / "repo")
    (tmp_path / "bundle").mkdir()
    ran = _run_main(monkeypatch, repo, _words(_CHECK_BUNDLE, tmp_path / "bundle"))
    assert ran.status == UNCHECKED
    assert ran.said[0].endswith("; the licence texts are unchecked")


@pytest.mark.parametrize(
    ("record", "reason"),
    [
        (None, Prose(f"[Errno 2] No such file or directory: '{{repo}}/{_WHERE}'")),
        (Prose("ghc: [unclosed\n"), Prose("while parsing a flow sequence")),
        (Prose('ghc: "9.8.4"\n'), Prose(f"{_WHERE} lacks the key 'tarball'")),
    ],
    ids=["absent", "not-yaml", "lacking"],
)
def test_main_check_is_unchecked_when_the_record_cannot_be_read(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, record: Prose | None, reason: Prose
) -> None:
    """A record absent, not YAML, or lacking a key exits 2 with the reason, never a traceback."""
    repo = plant(tmp_path, {TextPath(f"{KEPT}/text-2.1.1/LICENSE"): NOTICE})
    if record is not None:
        _ = (repo / _WHERE).write_text(record, encoding="utf-8")
    ran = _run_main(monkeypatch, repo, _words(_CHECK, TEXT))
    assert ran.status == UNCHECKED
    assert len(ran.said) == 1
    assert ran.said[0].startswith("bundle-licences: ")
    assert reason.replace("{repo}", str(repo)) in ran.said[0]
    assert ran.said[0].endswith("; the licence texts are unchecked")


@pytest.mark.parametrize(
    "absent", [CommandWord("ghc"), CommandWord("ghc-pkg"), CommandWord("agda")]
)
def test_main_is_unchecked_when_a_tool_it_runs_is_not_on_the_search_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, absent: CommandWord
) -> None:
    """A program the check runs that the search path lacks exits 2, never a traceback."""

    def found(name: CommandWord) -> CommandWord:
        """Resolve every program but ``absent``, which raises as the search path's lookup does."""
        if name == absent:
            message = f"required executable not found on PATH: {name}"
            raise RuntimeError(message)
        return name

    said = _prepare(monkeypatch, _plant_tree(tmp_path), _words(_CHECK, TEXT))
    monkeypatch.setattr("tools.bundle_licences.find_executable", found)
    assert (main(), said) == (
        UNCHECKED,
        [
            Prose(
                f"bundle-licences: required executable not found on PATH: {absent}; "
                + "the licence texts are unchecked"
            )
        ],
    )


@pytest.mark.parametrize(
    "argv",
    [
        [],
        ["check"],
        ["stage", "bundle"],
        ["check-bundle"],
        ["check-bundle", "a", "b"],
        ["audit", "x"],
    ],
)
def test_main_refuses_a_command_line_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch, argv: Command
) -> None:
    """A missing command, a command missing its operands, or an unknown one is refused."""
    monkeypatch.setattr("sys.argv", ["bundle_licences", *argv])
    with pytest.raises(SystemExit) as refused:
        _ = main()
    assert refused.value.code == ExitStatus(2)


def test_the_exit_statuses_are_the_ones_the_usage_states() -> None:
    """Held, found and unchecked exit 0, 1 and 2, as the module's usage says."""
    assert (ExitStatus(0), ExitStatus(1), ExitStatus(2)) == (HELD, FOUND, UNCHECKED)
