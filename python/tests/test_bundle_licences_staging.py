# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.bundle_licences``'s staging and its check of a staged bundle.

Staging copies each library's kept texts, mode 0644 whatever the umask, or
nothing and a finding per library without one.  The bundle check holds a
staged bundle's ``lib/`` to its ``licenses/`` both ways: the kernel carried with
a ``LICENSE.md`` naming a copyright, each other library with exactly its kept
texts, every folder with its library, nothing else in either.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Literal

import pytest
from _licence_fixtures import (
    FFI,
    GHC_LIBRARIES,
    GHC_TEXTS,
    GMP,
    KEPT_TEXTS,
    LIBRARIES,
    NOTICE,
    RTS,
    SECOND_TEXT,
    TEXT,
    VERSIONS,
    Texts,
    make_bundle,
    plant,
    plant_strays,
    without,
)

from tools.bundle_licences import (
    BUNDLED,
    KEPT,
    KERNEL,
    KERNEL_LICENCE,
    RECORD,
    Folder,
    LicenceText,
    TextPath,
    bundle_findings,
    stage,
)

from aletheia.common_types import Prose

# stage


def test_stage_copies_each_librarys_texts_into_the_bundle(tmp_path: Path) -> None:
    """Each library's kept texts land under the bundle's licence folder, readable by all."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    bundle = tmp_path / "bundle"
    assert not stage(bundle, LIBRARIES, VERSIONS, kept)
    staged = [path for path in sorted(bundle.rglob("*")) if path.is_file()]
    assert {
        TextPath(p.relative_to(bundle / BUNDLED).as_posix()): p.read_bytes() for p in staged
    } == KEPT_TEXTS
    assert {path.stat().st_mode & 0o777 for path in staged} == {0o644}


def test_stage_makes_each_text_readable_by_all_whatever_the_umask(tmp_path: Path) -> None:
    """A text is staged mode 0644 under a umask that would make it private: the tarball's mode."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    bundle = tmp_path / "bundle"
    previous = os.umask(0o077)
    try:
        assert not stage(bundle, LIBRARIES, VERSIONS, kept)
    finally:
        _ = os.umask(previous)
    staged = [path for path in (bundle / BUNDLED).rglob("*") if path.is_file()]
    assert {path.stat().st_mode & 0o777 for path in staged} == {0o644}


def test_stage_copies_only_the_libraries_given(tmp_path: Path) -> None:
    """A kept folder no library given claims is not staged."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    bundle = tmp_path / "bundle"
    assert not stage(bundle, [FFI], VERSIONS, kept)
    assert sorted(path.name for path in (bundle / BUNDLED).iterdir()) == ["libffi-3.4.6"]


@pytest.mark.parametrize("present", ["folder", "link"])
def test_stage_writes_nothing_into_a_licence_folder_already_there(
    tmp_path: Path, present: Literal["folder", "link"]
) -> None:
    """A licenses/ already in the bundle, or a link there, is refused and left as it is."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    bundle = tmp_path / "bundle"
    outside = tmp_path / "outside"
    outside.mkdir()
    bundle.mkdir()
    if present == "folder":
        (bundle / BUNDLED).mkdir()
    else:
        (bundle / BUNDLED).symlink_to(outside, target_is_directory=True)
    assert stage(bundle, LIBRARIES, VERSIONS, kept) == [
        Prose(f"{BUNDLED}/: already in the bundle; stage writes it fresh")
    ]
    assert not list((bundle / BUNDLED).iterdir())
    assert not list(outside.iterdir())


@pytest.mark.parametrize(
    ("library", "finding"),
    [
        (GMP, Prose("libgmp.so.10: no licence is kept for it")),
        (
            Path("libHSbase-4.19.2.0-9f38-ghc9.8.4.so"),
            Prose(
                f"libHSbase-4.19.2.0-9f38-ghc9.8.4.so: {KEPT}/base-4.19.2.0/ keeps no licence text"
            ),
        ),
    ],
)
def test_stage_copies_nothing_for_a_library_with_no_kept_text(
    tmp_path: Path, library: Path, finding: Prose
) -> None:
    """A library the tree keeps no text for is a finding naming it, and nothing is staged."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    bundle = tmp_path / "bundle"
    assert stage(bundle, [TEXT, library, FFI], VERSIONS, kept) == [finding]
    assert not bundle.exists()


# bundle_findings


def _bundle_findings(
    tmp_path: Path,
    libraries: list[Path] | None = None,
    licences: Texts | None = None,
    *,
    kernel_licence: bool = True,
) -> list[Prose]:
    """Return the bundle check's findings for a bundle of ``libraries`` and ``licences``.

    Left out, they are the kernel with the fixture's libraries, and the kept texts.
    """
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    carried = LIBRARIES if libraries is None else libraries
    staged = KEPT_TEXTS if licences is None else licences
    bundle = make_bundle(tmp_path, carried, staged, kernel_licence=kernel_licence)
    return bundle_findings(bundle, VERSIONS, kept)


def test_bundle_findings_holds_a_bundle_staged_from_the_kept_texts(tmp_path: Path) -> None:
    """A bundle whose every library has its kept texts, and the kernel its licence: no finding."""
    assert not _bundle_findings(tmp_path)


def test_bundle_findings_holds_what_stage_writes(tmp_path: Path) -> None:
    """The bundle check holds the bundle the staging writes."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    bundle = make_bundle(tmp_path, LIBRARIES, {}, kernel_licence=True)
    assert not stage(bundle, LIBRARIES, VERSIONS, kept)
    assert not bundle_findings(bundle, VERSIONS, kept)


def test_bundle_findings_names_a_kernel_without_its_licence(tmp_path: Path) -> None:
    """The kernel library without LICENSE.md beside lib/ is a finding."""
    assert _bundle_findings(tmp_path, kernel_licence=False) == [
        Prose(f"lib/{KERNEL}: the bundle carries no {KERNEL_LICENCE}")
    ]


def test_bundle_findings_names_a_bundle_without_the_kernel(tmp_path: Path) -> None:
    """A lib/ without the kernel is a finding, so a bundle carrying nothing is never held."""
    found = _bundle_findings(
        tmp_path, libraries=GHC_LIBRARIES, licences=GHC_TEXTS, kernel_licence=False
    )
    assert found == [Prose(f"lib/: the bundle carries no {KERNEL}")]
    assert _bundle_findings(tmp_path / "empty", libraries=[], licences={}) == [
        Prose(f"lib/: the bundle carries no {KERNEL}")
    ]


def test_the_bundle_layout_is_the_one_the_dist_rule_writes(tmp_path: Path) -> None:
    """The kernel is lib/libaletheia-ffi.so, its licence LICENSE.md, the texts under licenses/."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    bundle = tmp_path / "bundle"
    (bundle / "lib").mkdir(parents=True)
    for name in ("libaletheia-ffi.so", *(library.name for library in LIBRARIES)):
        _ = (bundle / "lib" / name).write_bytes(b"\x7fELF")
    _ = (bundle / "LICENSE.md").write_text("Copyright 2025\n", encoding="utf-8")
    assert not stage(bundle, LIBRARIES, VERSIONS, kept)
    assert (bundle / "licenses" / "text-2.1.1" / "LICENSE").read_bytes() == NOTICE
    assert not bundle_findings(bundle, VERSIONS, kept)


def _with_bindings(bundle: Path, copies: dict[Prose, LicenceText | None]) -> Path:
    """Give ``bundle`` a binding per entry of ``copies``, each with that LICENSE.md or none."""
    for name, text in copies.items():
        (bundle / "bindings" / name).mkdir(parents=True)
        if text is not None:
            _ = (bundle / "bindings" / name / "LICENSE.md").write_bytes(text)
    return bundle


def test_bundle_findings_holds_bindings_carrying_the_bundles_licence(tmp_path: Path) -> None:
    """Each binding with a copy of the bundle's LICENSE.md holds."""
    bundle = make_bundle(tmp_path, LIBRARIES, KEPT_TEXTS, kernel_licence=True)
    own = LicenceText((bundle / KERNEL_LICENCE).read_bytes())
    _ = _with_bindings(bundle, {Prose("python"): own, Prose("rust"): own})
    assert not bundle_findings(bundle, VERSIONS, plant(tmp_path / "kept", KEPT_TEXTS))


def test_bundle_findings_names_a_binding_without_the_bundles_licence(tmp_path: Path) -> None:
    """A binding whose LICENSE.md is absent or another text is a finding, the others held."""
    bundle = make_bundle(tmp_path, LIBRARIES, KEPT_TEXTS, kernel_licence=True)
    own = LicenceText((bundle / KERNEL_LICENCE).read_bytes())
    copies = {Prose("cpp"): None, Prose("go"): LicenceText(b"Copyright MIT\n"), Prose("rust"): own}
    _ = _with_bindings(bundle, copies)
    assert bundle_findings(bundle, VERSIONS, plant(tmp_path / "kept", KEPT_TEXTS)) == [
        Prose(f"bindings/cpp: carries no {KERNEL_LICENCE}"),
        Prose(f"bindings/go: its {KERNEL_LICENCE} is not the bundle's"),
    ]


def test_bundle_findings_names_bindings_when_the_bundle_has_no_licence(tmp_path: Path) -> None:
    """Without the bundle's own LICENSE.md no binding's copy can be the bundle's."""
    bundle = make_bundle(tmp_path, LIBRARIES, KEPT_TEXTS, kernel_licence=False)
    _ = _with_bindings(bundle, {Prose("python"): LicenceText(b"Copyright 2025\n")})
    assert Prose(f"bindings/python: its {KERNEL_LICENCE} is not the bundle's") in bundle_findings(
        bundle, VERSIONS, plant(tmp_path / "kept", KEPT_TEXTS)
    )


def test_bundle_findings_names_a_library_without_a_licence(tmp_path: Path) -> None:
    """A library in lib/ whose folder the bundle lacks is a finding."""
    assert _bundle_findings(tmp_path, licences=without(Folder("rts-1.0.2"))) == [
        Prose(f"lib/{RTS.name}: {BUNDLED}/rts-1.0.2/ holds no licence text")
    ]


def test_bundle_findings_names_every_library_of_a_bundle_with_no_licence_folder(
    tmp_path: Path,
) -> None:
    """A bundle staged with no licence folder at all names each library it carries."""
    assert _bundle_findings(tmp_path, licences={}) == [
        Prose(f"lib/{KERNEL}: {BUNDLED}/Agda-2.8.0/ holds no licence text"),
        Prose(f"lib/{FFI.name}: {BUNDLED}/libffi-3.4.6/ holds no licence text"),
        Prose(f"lib/{RTS.name}: {BUNDLED}/rts-1.0.2/ holds no licence text"),
        Prose(f"lib/{KERNEL}: {BUNDLED}/standard-library-2.4/ holds no licence text"),
        Prose(f"lib/{TEXT.name}: {BUNDLED}/text-2.1.1/ holds no licence text"),
    ]


def test_bundle_findings_names_a_library_the_tree_keeps_no_licence_for(tmp_path: Path) -> None:
    """A library in lib/ that is neither a GHC package nor libffi is a finding."""
    assert _bundle_findings(tmp_path, libraries=[Path(KERNEL), *LIBRARIES, GMP]) == [
        Prose("lib/libgmp.so.10: no licence is kept for it")
    ]


@pytest.mark.parametrize(
    "licences",
    [
        {**KEPT_TEXTS, SECOND_TEXT: LicenceText(b"Copyright (c) 2003 someone else.\n")},
        {path: text for path, text in KEPT_TEXTS.items() if path != SECOND_TEXT},
        {**KEPT_TEXTS, TextPath("rts-1.0.2/NOTICE"): NOTICE},
    ],
    ids=["changed", "missing", "added"],
)
def test_bundle_findings_names_a_folder_that_is_not_the_kept_one(
    tmp_path: Path, licences: Texts
) -> None:
    """A staged folder whose texts are not exactly the kept ones is a finding."""
    assert _bundle_findings(tmp_path, licences=licences) == [
        Prose(f"lib/{RTS.name}: {BUNDLED}/rts-1.0.2/ is not {KEPT}/rts-1.0.2/")
    ]


def test_bundle_findings_names_a_folder_for_no_library_lib_carries(tmp_path: Path) -> None:
    """A staged folder no library in lib/ claims is a finding."""
    licences = {**KEPT_TEXTS, TextPath("base-4.19.2.0/LICENSE"): NOTICE}
    assert _bundle_findings(tmp_path, licences=licences) == [
        Prose(f"{BUNDLED}/base-4.19.2.0/: the bundle's lib/ carries no library it covers")
    ]


def test_bundle_findings_names_an_entry_of_lib_that_is_no_library_file(tmp_path: Path) -> None:
    """A folder or a link under lib/ is a finding, never a library skipped."""
    bundle = make_bundle(tmp_path, LIBRARIES, KEPT_TEXTS, kernel_licence=True)
    (bundle / "lib" / "libgmp.so.10").mkdir()
    (bundle / "lib" / "libz.so.1").symlink_to(bundle / "lib" / KERNEL)
    assert bundle_findings(bundle, VERSIONS, plant(tmp_path / "kept", KEPT_TEXTS)) == [
        Prose("lib/libgmp.so.10: not a library file"),
        Prose("lib/libz.so.1: not a library file"),
    ]


def test_bundle_findings_names_a_kernel_licence_naming_no_copyright(tmp_path: Path) -> None:
    """An empty LICENSE.md is no licence for the kernel."""
    bundle = make_bundle(tmp_path, LIBRARIES, KEPT_TEXTS, kernel_licence=True)
    _ = (bundle / KERNEL_LICENCE).write_text("", encoding="utf-8")
    assert bundle_findings(bundle, VERSIONS, plant(tmp_path / "kept", KEPT_TEXTS)) == [
        Prose(f"lib/{KERNEL}: its {KERNEL_LICENCE} names no copyright")
    ]


def test_bundle_findings_reads_a_kernel_licence_beside_bytes_utf8_cannot_decode(
    tmp_path: Path,
) -> None:
    """A LICENSE.md naming a copyright beside bytes UTF-8 cannot decode is the kernel's licence."""
    bundle = make_bundle(tmp_path, LIBRARIES, KEPT_TEXTS, kernel_licence=True)
    _ = (bundle / KERNEL_LICENCE).write_bytes(b"\xff Copyright 2025\n")
    assert not bundle_findings(bundle, VERSIONS, plant(tmp_path / "kept", KEPT_TEXTS))


def test_bundle_findings_names_every_stray_in_the_staged_folders(tmp_path: Path) -> None:
    """The staged folder holds library folders of texts only, the record included in that."""
    bundle = make_bundle(tmp_path, LIBRARIES, KEPT_TEXTS, kernel_licence=True)
    outside = tmp_path / "outside"
    _ = outside.write_bytes(NOTICE)
    strays = plant_strays(bundle / BUNDLED, outside)
    _ = (bundle / BUNDLED / RECORD).write_text("ghc: x\n", encoding="utf-8")
    found = bundle_findings(bundle, VERSIONS, plant(tmp_path / "kept", KEPT_TEXTS))
    assert found == [
        *(
            Prose(f"{BUNDLED}/{path}: not a licence text in a library's folder")
            for path in sorted([*strays, TextPath(str(RECORD))])
        ),
    ]


@pytest.mark.parametrize("shape", ["file", "link"])
def test_bundle_findings_names_a_licence_folder_that_is_not_one(
    tmp_path: Path, shape: Literal["file", "link"]
) -> None:
    """A licenses/ that is a file, or a link to the kept folders, holds no library's text."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    bundle = make_bundle(tmp_path, [Path(KERNEL), FFI], {}, kernel_licence=True)
    if shape == "file":
        _ = (bundle / BUNDLED).write_text("Copyright\n", encoding="utf-8")
    else:
        (bundle / BUNDLED).symlink_to(kept, target_is_directory=True)
    assert bundle_findings(bundle, VERSIONS, kept) == [
        Prose(f"{BUNDLED}: not a folder"),
        Prose(f"lib/{KERNEL}: {BUNDLED}/Agda-2.8.0/ holds no licence text"),
        Prose(f"lib/{FFI.name}: {BUNDLED}/libffi-3.4.6/ holds no licence text"),
        Prose(f"lib/{KERNEL}: {BUNDLED}/standard-library-2.4/ holds no licence text"),
    ]
