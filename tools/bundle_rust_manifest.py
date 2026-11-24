# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Write the Rust crate's manifest as the bundle ships it: without its examples.

The bundle carries the crate's library alone (``Cargo.toml``, ``Cargo.lock`` and
``src/``), as the other bindings' bundles carry theirs, and cargo refuses a
manifest naming a target whose files are absent: an ``[[example]]`` table
naming ``examples/`` the bundle leaves out stops every build of the bundled
crate as a package of its own.  The staged manifest is the repository's with
each ``[[example]]`` table, and the comment lines written directly above it,
left out; every other table and key is kept as it is.

The dist step rewrites the staged ``bindings/rust/Cargo.toml`` with it, and
``tools/check_bundle_consumers.py`` builds the crate staged the same way.

Run: ``python -m tools.bundle_rust_manifest MANIFEST``, rewriting it in place.
Exits 0 when written, 2 on a usage error or an unreadable manifest.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import NewType

from tools._common import CommandWord, emit

from aletheia.common_types import ExitStatus

# A manifest's text, and one of its lines.
ManifestText = NewType("ManifestText", str)
ManifestLine = NewType("ManifestLine", str)

_EXAMPLE_HEADER = "[[example]]"


def _is_header(line: ManifestLine) -> bool:
    """Say whether ``line`` opens a table or an array of tables."""
    return str(line).lstrip().startswith("[")


def staged_manifest(text: ManifestText) -> ManifestText:
    """Return ``text`` without its ``[[example]]`` tables and the comments directly above them."""
    kept: list[ManifestLine] = []
    # Comment and blank lines met inside an example table: the next table's when
    # a header follows them, the example's when a key of it does.
    held: list[ManifestLine] = []
    skipping = False
    for raw in text.splitlines(keepends=True):
        line = ManifestLine(raw)
        stripped = raw.strip()
        if stripped == _EXAMPLE_HEADER:
            while kept and str(kept[-1]).lstrip().startswith("#"):
                _ = kept.pop()
            held.clear()
            skipping = True
        elif not skipping:
            kept.append(line)
        elif _is_header(line):
            kept.extend(held)
            kept.append(line)
            held.clear()
            skipping = False
        elif stripped == "" or stripped.startswith("#"):
            held.append(line)
        else:
            held.clear()
    while kept and not str(kept[-1]).strip():
        _ = kept.pop()
    return ManifestText("".join(kept))


def main(argv: list[CommandWord] | None = None) -> ExitStatus:
    """Rewrite the manifest named on the command line as the bundle ships it."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("manifest", type=Path, help="the staged Cargo.toml, rewritten in place")
    args = parser.parse_args(argv)
    manifest = Path(args.manifest)
    try:
        text = ManifestText(manifest.read_text(encoding="utf-8"))
    except OSError as error:
        emit(f"bundle_rust_manifest: {manifest}: {error}")
        return ExitStatus(2)
    _ = manifest.write_text(staged_manifest(text), encoding="utf-8")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())
