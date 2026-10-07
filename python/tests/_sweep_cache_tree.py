# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A fake repository for the sweep cache's tests: every file a sweep reads, each tree built.

The tree is faked under a scratch root, every file a sweep reads in it
standing for one the lane's sweep was traced reading, and an absent file is
one of the states a file can be in.
"""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, Literal, NewType

import tools.mutation_sweep_cache as sweep_cache
from tools import mutation_cpp, mutation_cpp_config
from tools.mutation_cpp_legs import CppLeg, CppTree

if TYPE_CHECKING:
    import pytest

LIBRARY = Path("build/libaletheia-ffi.so")

# The test kernel each tree builds beside its binary, and the stand-in kernels
# the build makes beside the library.
_KERNELS = ("recording_kernel",)
_STAND_INS = ("abi_only_kernel", "null_kernel", "stale_abi_kernel", "symbolless")

# The sources the leak tree's binary carries mutants in, and one it does not.
SOURCES = (Path("cpp/src/client.cpp"), Path("cpp/include/aletheia/client.hpp"))
UNMUTATED = Path("cpp/src/other.cpp")

# A source a mutant names outside the tree, as a system header would be.
OUTSIDE = Path("/usr/include/c++/vector")

# One file of each kind a sweep reads from the tree at a path the tree's
# layout fixes, each present in the fake tree unless its test creates it; the
# libraries found by name or by a search path are tested apart.  The library
# is looked for at every path the tests look for it, and found at the first.
READ_BY_A_SWEEP = (
    LIBRARY,
    Path("dist/aletheia/lib/libaletheia-ffi.so"),
    Path("cpp/build/libaletheia-ffi.so"),
    Path("examples/demo/demo_workbook.xlsx"),
    Path("cpp/mull.yml"),
    Path("cpp", CppTree.ADDRESS.directory, "mull-config.yml"),
    *(Path("cpp", tree.directory, "unit_tests") for tree in CppTree),
    *(
        Path("cpp", tree.directory, sweep_cache.CPP_FRESH_PROCESS_DIR, "child_tests")
        for tree in CppTree
    ),
    *(
        Path("cpp", tree.directory, f"libaletheia_test_{kernel}.so")
        for tree in CppTree
        for kernel in _KERNELS
    ),
    *(sweep_cache.STAND_IN_DIR / f"{name}.so" for name in _STAND_INS),
    *SOURCES,
)
LOOKED_FOR_ONLY = frozenset(READ_BY_A_SWEEP[1:3])

# The tree's configuration: a mutator every tree keeps, and one the address
# tree drops, so that tree is built under a configuration of its own.
MULL_CONFIG = "mutators:\n  - cxx_add_to_sub\n  - cxx_remove_void_call\nexcludePaths: []\n"

# What is done to a file: its last byte changed, so its size is not; the file
# removed; or the file created.
FileChange = Literal["rewritten", "removed", "created"]

# A mutant's name as a binary carries it.
_MutantName = NewType("_MutantName", bytes)


def _mutant(source: Path) -> _MutantName:
    """Spell a mutant's name as a binary carries it, pointing at ``source``."""
    return _MutantName(f"cxx_add_to_sub:{source}:12:3:12:9:0a1b2c.0".encode())


def change_file(path: Path, how: FileChange) -> None:
    """Change a file's last byte, remove it, or create it."""
    if how == "rewritten":
        data = path.read_bytes()
        _ = path.write_bytes(data[:-1] + bytes([data[-1] ^ 1]))
    elif how == "removed":
        path.unlink()
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_bytes(b"created")


def root_at(monkeypatch: pytest.MonkeyPatch, root: Path) -> None:
    """Point every module a sweep's key and run read the repository from at ``root``."""
    for module in (sweep_cache, mutation_cpp, mutation_cpp_config):
        monkeypatch.setattr(module, "REPO_ROOT", root)


def fake_tree(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Fake the repository under a scratch root, each tree built under the configuration it gets.

    The root is a directory of the test's own scratch, so what a test puts
    beside the tree, a stand-in tool or a report directory, is its own.
    """
    root = tmp_path / "repo"
    root.mkdir()
    root_at(monkeypatch, root)
    monkeypatch.setattr(sweep_cache, "CACHE_ROOT", root / "cpp" / "mutation-sweeps")
    config = root / "cpp" / "mull.yml"
    config.parent.mkdir(parents=True)
    _ = config.write_text(MULL_CONFIG, encoding="utf-8")
    for build in CppTree:
        _ = mutation_cpp_config.leg_config(CppLeg(build), sweep_cache.tree_build_dir(build))
    for relative in (*READ_BY_A_SWEEP, UNMUTATED):
        path = root / relative
        if relative in LOOKED_FOR_ONLY or path.exists():
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_bytes(f"first {relative}".encode())
        path.chmod(0o755)
    names = [_mutant(root / source) for source in SOURCES] + [_mutant(OUTSIDE)]
    _ = sweep_cache.tree_binary(CppTree.LEAK).write_bytes(b"\0".join([b"first", *names]))
    return root
