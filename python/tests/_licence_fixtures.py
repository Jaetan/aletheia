# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Fixtures shared by the tests of ``tools.bundle_licences``: libraries, kept texts, bundles."""

from __future__ import annotations

from pathlib import Path

from tools.bundle_licences import (
    BUNDLED,
    KERNEL,
    KERNEL_LICENCE,
    AgdaLibrary,
    AgdaVersion,
    Folder,
    LibffiRelease,
    LicenceText,
    TextPath,
    Versions,
)

# A licence folder's texts by their paths from the folders' parent.
type Texts = dict[TextPath, LicenceText]

LIBFFI = LibffiRelease("3.4.6")
AGDA = AgdaVersion("2.8.0")
STDLIB = AgdaLibrary("standard-library-2.4")
VERSIONS = Versions(LIBFFI, AGDA, [STDLIB])
KERNEL_LIBRARY = Path(KERNEL)
TEXT = Path("libHStext-2.1.1-787c-ghc9.8.4.so")
RTS = Path("libHSrts-1.0.2_thr-ghc9.8.4.so")
FFI = Path("libffi.so.8")
GMP = Path("libgmp.so.10")
GHC_LIBRARIES = [TEXT, RTS, FFI]
LIBRARIES = [KERNEL_LIBRARY, *GHC_LIBRARIES]
SECOND_TEXT = TextPath("rts-1.0.2/COPYING")
NOTICE = LicenceText(b"Copyright (c) 2008-2009, Tom Harper\nAll rights reserved.\n")
# Each library's folder and the texts it keeps, as the tree keeps them.
KEPT_TEXTS: Texts = {
    TextPath("Agda-2.8.0/LICENSE"): LicenceText(
        b"Copyright (c) 2005-2025 remains with the authors.\n"
    ),
    TextPath("standard-library-2.4/LICENCE"): LicenceText(
        b"Copyright (c) 2007-2026 Nils Anders Danielsson, Ulf Norell.\n"
    ),
    TextPath("text-2.1.1/LICENSE"): NOTICE,
    TextPath("rts-1.0.2/LICENSE"): LicenceText(
        b"The Glasgow Haskell Compiler License\n\nCopyright 2002.\n"
    ),
    SECOND_TEXT: LicenceText(b"Copyright (c) 2003-2017 University of Illinois.\n"),
    TextPath("libffi-3.4.6/LICENSE"): LicenceText(
        b"libffi - Copyright (c) 1996-2024  Anthony Green.\n"
    ),
}


def plant(root: Path, texts: Texts) -> Path:
    """Write ``texts`` under ``root``, each at its path; return ``root``."""
    root.mkdir(parents=True, exist_ok=True)
    for path, text in texts.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        _ = (root / path).write_bytes(text)
    return root


def without(folder: Folder) -> Texts:
    """Return the kept texts but those ``folder`` holds."""
    return {path: text for path, text in KEPT_TEXTS.items() if Path(path).parts[0] != folder}


def plant_strays(root: Path, outside: Path) -> list[TextPath]:
    """Plant under ``root`` each entry a licence folder may not hold; return their paths."""
    _ = plant(root, {TextPath("text-2.1.1/sub/LICENSE"): NOTICE})
    _ = (root / "README").write_text("stray\n", encoding="utf-8")
    (root / "rts-1.0.2" / "NOTICE").symlink_to(outside)
    (root / "linked-1.0").symlink_to(root / "text-2.1.1", target_is_directory=True)
    (root / "rts-1.0.2" / "dangling").symlink_to(root / "absent")
    return [
        TextPath("README"),
        TextPath("linked-1.0"),
        TextPath("rts-1.0.2/NOTICE"),
        TextPath("rts-1.0.2/dangling"),
        TextPath("text-2.1.1/sub"),
    ]


def make_bundle(
    tmp_path: Path, libraries: list[Path], licences: Texts, *, kernel_licence: bool
) -> Path:
    """Return a bundle carrying ``libraries`` in ``lib/`` and ``licences`` in its licence folder."""
    bundle = tmp_path / "bundle"
    (bundle / "lib").mkdir(parents=True)
    for library in libraries:
        _ = (bundle / "lib" / library.name).write_bytes(b"\x7fELF")
    if licences:
        _ = plant(bundle / BUNDLED, licences)
    if kernel_licence:
        _ = (bundle / KERNEL_LICENCE).write_text("Copyright 2025\n", encoding="utf-8")
    return bundle


# The kept texts but the kernel's, the Agda ones.
GHC_TEXTS: Texts = {
    path: text
    for path, text in KEPT_TEXTS.items()
    if Path(path).parts[0] not in {f"Agda-{AGDA}", STDLIB}
}
