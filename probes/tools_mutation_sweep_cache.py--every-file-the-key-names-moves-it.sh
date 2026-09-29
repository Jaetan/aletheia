#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_sweep_cache.py.
# Claim: every file the C++ sweep key names moves the key when its content
# changes and its size does not, when it is removed, and, for a file the tree
# does not hold, when it appears; so a kept sweep taken against one library,
# test kernel, fixture, configuration or source is never served for another.
# The probe mirrors today's key into a scratch root, every ELF file as a link
# to the real one so what it names is named as in the tree, every other file
# as bytes of its own, and points the key at that root. A linked file is
# replaced by a file of its own before it is rewritten, so nothing is written
# through a link into the tree. The sources a binary's mutants name are the
# real tree's, which a mirrored binary cannot point elsewhere, so they are
# changed in a second pass, under a binary whose mutants name their mirrors.
# Non-zero exit: a file the key names that left the key unmoved, listed with
# the change that did not move it. Exits 2 without the venv, when the mirror
# does not name the files the tree's key names, or when restoring every file
# does not bring the key back. Exits 0 with a note without a built tree, since
# the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

exec "$py" - << 'EOF'
import sys
import tempfile
from pathlib import Path
from typing import Literal, NamedTuple

import tools.mutation_cpp as mutation_cpp
import tools.mutation_cpp_config as mutation_cpp_config
import tools.mutation_sweep_cache as sweep_cache
from tools.mutation_cpp_legs import CppTree

# What is done to a file the key names: its last byte changed, the file
# removed, or, for a file the tree does not hold, the file created.
Change = Literal["rewritten", "removed", "created"]


class Unmoved(NamedTuple):
    """A file the key names, and the change to it that left the key where it was."""

    relative: Path
    change: Change


tree = sweep_cache.REPO_ROOT
for build in CppTree:
    if not sweep_cache.tree_binary(build).is_file():
        print(f"the {build.value} mutation tree is not built, claim untestable")
        sys.exit(0)
named = {path.relative_to(tree) for path in sweep_cache.key_inputs()}
sources = {
    path.relative_to(tree)
    for build in CppTree
    for path in sweep_cache.binary_sources(sweep_cache.tree_binary(build))
    if path.is_relative_to(tree)
}
held = {relative for relative in named if (tree / relative).is_file()}
linked = {relative for relative in held - sources if (tree / relative).read_bytes()[:4] == b"\x7fELF"}

with tempfile.TemporaryDirectory(prefix="sweep-key-") as scratch:
    root = Path(scratch)

    def restore(relative: Path) -> None:
        mirror = root / relative
        mirror.unlink(missing_ok=True)
        mirror.parent.mkdir(parents=True, exist_ok=True)
        if relative in linked:
            mirror.symlink_to(tree / relative)
        elif relative in held:
            mirror.write_bytes(f"mirror of {relative}".encode())

    def unmoved_by(relatives: set[Path]) -> list[Unmoved]:
        before = sweep_cache.sweep_key()
        found: list[Unmoved] = []
        for relative in sorted(relatives):
            mirror = root / relative
            changes: tuple[Change, ...] = ("rewritten", "removed") if relative in held else ("created",)
            for change in changes:
                if change == "rewritten":
                    data = mirror.read_bytes()
                    mirror.unlink()
                    mirror.write_bytes(data[:-1] + bytes([data[-1] ^ 1]))
                elif change == "removed":
                    mirror.unlink()
                else:
                    mirror.parent.mkdir(parents=True, exist_ok=True)
                    mirror.write_bytes(f"created {relative}".encode())
                if sweep_cache.sweep_key() == before:
                    found.append(Unmoved(relative, change))
                restore(relative)
        if sweep_cache.sweep_key() != before:
            print("restoring every file did not bring the key back")
            sys.exit(2)
        return found

    for relative in held - sources:
        restore(relative)
    sweep_cache.REPO_ROOT = mutation_cpp.REPO_ROOT = mutation_cpp_config.REPO_ROOT = root
    mirrored = {path.relative_to(root) for path in sweep_cache.key_inputs()}
    if mirrored != named - sources:
        print(f"the mirror names {len(mirrored)} files where the tree's key names {len(named - sources)}")
        sys.exit(2)
    unmoved = unmoved_by(named - sources)

    # The second pass: one binary whose mutants name the sources' mirrors.
    first = sweep_cache.tree_binary(next(iter(CppTree))).relative_to(root)
    (root / first).unlink()
    (root / first).write_bytes(
        b"\0".join(f"cxx_add_to_sub:{root / relative}:1:1:1:1:0a.0".encode() for relative in sorted(sources))
    )
    for relative in sources:
        restore(relative)
    mirrored = {path.relative_to(root) for path in sweep_cache.key_inputs()}
    if not sources <= mirrored:
        print(f"the key names {len(sources & mirrored)} of the {len(sources)} sources a binary's mutants name")
        sys.exit(2)
    unmoved += unmoved_by(sources)

for relative, change in unmoved:
    print(f"the key did not move: {relative} {change}")
print(
    f"{len(named)} files named, {len(held)} held by the tree, {len(sources)} of them sources,"
    f" {len(unmoved)} changes left the key unmoved"
)
sys.exit(1 if unmoved else 0)
EOF
