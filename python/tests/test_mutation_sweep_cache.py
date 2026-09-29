# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ sweep cache: what a kept sweep is keyed on, how one is run and kept, and where.

A kept sweep is served for as long as its key reads the same, so every file a
sweep reads from the tree has to move the key: a sweep taken against one
library and served for another reports verdicts no sweep of today's tree
would.  The tree is faked under a scratch root, every file a sweep reads in it
standing for one the lane's sweep was traced reading, and an absent file is
one of the states a file can be in.  What a binary records about its linking is read
from ELF images the tests build with the format's own constants rather than
the reader's, so a wrong constant in the reader reads red.

The sweep pins its runner with ``taskset -c``, which widens an affinity as
readily as it narrows one, so a list counted from the machine re-pins a run
launched on part of it onto CPUs it was never given.  The machine and the
affinity are faked so the two disagree on every host, and the given CPUs are
neither zero-based nor contiguous, which is what a list counted up from zero
gets wrong; nor does a set of them iterate in order, so the CPU left free is
the highest because it was chosen, not because it came last.
"""

from __future__ import annotations

import fcntl
import os
import shutil
import struct
import subprocess
import sys
import tempfile
from enum import IntEnum
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType

import pytest

import tools.mutation_sweep_cache as sweep_cache
from tools import mutation_cpp, mutation_cpp_config
from tools._resources import Cpu
from tools.cpp_scratch import scratch_root
from tools.mutation_cpp import CPP_LEG_REPORT_SUFFIXES
from tools.mutation_cpp_legs import CPP_SLICE_ENV, CPP_STAGE_ENV, CppLeg, CppTree
from tools.mutation_sweep_cache import polite

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Sequence

    from tools.mutation_cpp_config import ConfigText

_REPO = Path(__file__).resolve().parents[2]
_LIBRARY = Path("build/libaletheia-ffi.so")
_PLAIN_BINARY = Path("cpp", CppTree.PLAIN.directory, "unit_tests")

# The test kernels each tree builds beside its binary.
_KERNELS = ("abi_only", "recording_kernel", "stale_abi_kernel", "symbolless")

# The sources the leak tree's binary carries mutants in, and one it does not.
_SOURCES = (Path("cpp/src/client.cpp"), Path("cpp/include/aletheia/client.hpp"))
_UNMUTATED = Path("cpp/src/other.cpp")

# A source a mutant names outside the tree, as a system header would be.
_OUTSIDE = Path("/usr/include/c++/vector")

# One file of each kind a sweep reads from the tree at a path the tree's
# layout fixes, each present in the fake tree unless its test creates it; the
# libraries found by name or by a search path are tested apart.  The library
# is looked for at every path the tests look for it, and found at the first.
_READ_BY_A_SWEEP = (
    _LIBRARY,
    Path("dist/aletheia/lib/libaletheia-ffi.so"),
    Path("cpp/build/libaletheia-ffi.so"),
    Path("examples/demo/demo_workbook.xlsx"),
    Path("cpp/mull.yml"),
    Path("cpp", CppTree.ADDRESS.directory, "mull-config.yml"),
    *(Path("cpp", tree.directory, "unit_tests") for tree in CppTree),
    *(
        Path("cpp", tree.directory, f"libaletheia_test_{kernel}.so")
        for tree in CppTree
        for kernel in _KERNELS
    ),
    *_SOURCES,
)
_LOOKED_FOR_ONLY = frozenset(_READ_BY_A_SWEEP[1:3])

# The tree's configuration: a mutator every tree keeps, and one the address
# tree drops, so that tree is built under a configuration of its own.
_MULL_CONFIG = "mutators:\n  - cxx_add_to_sub\n  - cxx_remove_void_call\nexcludePaths: []\n"

# What is done to a file: its last byte changed, so its size is not; the file
# removed; or the file created.
_Change = Literal["rewritten", "removed", "created"]

# An image's bytes, a name an image records, and where a name sits in its
# string table.
_Image = NewType("_Image", bytes)
_Name = NewType("_Name", str)
_StringAt = NewType("_StringAt", int)
_FileAt = NewType("_FileAt", int)


class _Tag(IntEnum):
    """The dynamic tags the images use, with the values the ELF format gives them."""

    NULL = 0
    NEEDED = 1
    STRTAB = 5
    RPATH = 15
    DEBUG = 21
    RUNPATH = 29


class _Entry(NamedTuple):
    """A dynamic entry: its tag, and the name it points at, empty for one that points at none."""

    tag: _Tag
    name: _Name = _Name("")


class _Patch(NamedTuple):
    """Bytes written over an image at an offset."""

    offset: _FileAt
    data: _Image


# Where an image loads, apart from where its bytes sit in the file, so an
# address read as an offset reads nothing; and the sizes of the ELF64 header,
# of a program header and of a dynamic entry.
_BASE = 0x400000
_HEADER = 64
_PROGRAM_HEADER = 56
_DYNAMIC_ENTRY = 16

# Where an image's header records the program headers; where each program
# header records its segment's place in the file, and the loadable one its
# size there; where the dynamic section starts, and where in it the string
# table's address and the first entry's value sit.
_PHOFF = _FileAt(32)
_LOAD_FILESZ = _FileAt(_HEADER + 32)
_DYNAMIC_OFFSET = _FileAt(_HEADER + _PROGRAM_HEADER + 8)
_DYNAMIC_AT = _HEADER + 2 * _PROGRAM_HEADER
_STRTAB_VALUE = _FileAt(_DYNAMIC_AT + 8)
_FIRST_VALUE = _FileAt(_DYNAMIC_AT + _DYNAMIC_ENTRY + 8)


def _elf(entries: Sequence[_Entry]) -> _Image:
    """Build an ELF64 little-endian image: a loadable segment, and a dynamic one of ``entries``.

    The dynamic section opens on the string table's address and closes on its
    end marker, with the entries between.
    """
    strings = bytearray(b"\0")
    at: dict[_Name, _StringAt] = {}
    for entry in entries:
        if entry.name and entry.name not in at:
            at[entry.name] = _StringAt(len(strings))
            strings += entry.name.encode() + b"\0"
    strings_at = _DYNAMIC_AT + _DYNAMIC_ENTRY * (len(entries) + 2)
    rows = [(_Tag.STRTAB, _BASE + strings_at)]
    rows += [(entry.tag, at.get(entry.name, 0)) for entry in entries]
    rows += [(_Tag.NULL, 0)]
    dynamic = b"".join(struct.pack("<qQ", tag, value) for tag, value in rows)
    size = strings_at + len(strings)
    ident = b"\x7fELF\x02\x01\x01" + bytes(9)
    header = ident + struct.pack(
        "<HHIQQQIHHHHHH", 3, 62, 1, 0, _HEADER, 0, 0, _HEADER, _PROGRAM_HEADER, 2, 0, 0, 0
    )
    # PT_LOAD over the whole file, then PT_DYNAMIC over the dynamic section,
    # each with a physical address and a size in memory unlike the fields the
    # reader takes, so a reader taking the wrong field reads nothing.
    load = struct.pack("<IIQQQQQQ", 1, 4, 0, _BASE, 0, size, size + 0x1000, 0x1000)
    address = _BASE + _DYNAMIC_AT
    segment = struct.pack(
        "<IIQQQQQQ", 2, 6, _DYNAMIC_AT, address, 0, len(dynamic), len(dynamic) + 16, 8
    )
    return _Image(header + load + segment + dynamic + bytes(strings))


def _patched(image: _Image, *patches: _Patch) -> _Image:
    """Write each patch over a copy of the image."""
    raw = bytearray(image)
    for patch in patches:
        raw[patch.offset : patch.offset + len(patch.data)] = patch.data
    return _Image(bytes(raw))


def _mutant(source: Path) -> _Image:
    """Spell a mutant's name as a binary carries it, pointing at ``source``."""
    return _Image(f"cxx_add_to_sub:{source}:12:3:12:9:0a1b2c.0".encode())


def _change(path: Path, change: _Change) -> None:
    """Change a file's last byte, remove it, or create it."""
    if change == "rewritten":
        data = path.read_bytes()
        _ = path.write_bytes(data[:-1] + bytes([data[-1] ^ 1]))
    elif change == "removed":
        path.unlink()
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_bytes(b"created")


def _root_at(monkeypatch: pytest.MonkeyPatch, root: Path) -> None:
    """Point every module a sweep's key and run read the repository from at ``root``."""
    for module in (sweep_cache, mutation_cpp, mutation_cpp_config):
        monkeypatch.setattr(module, "REPO_ROOT", root)


@pytest.fixture(name="tree")
def _tree(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Fake the repository under a scratch root, each tree built under the configuration it gets.

    The root is a directory of the test's own scratch, so what a test puts
    beside the tree, a stand-in tool or a report directory, is its own.
    """
    root = tmp_path / "repo"
    root.mkdir()
    _root_at(monkeypatch, root)
    monkeypatch.setattr(sweep_cache, "CACHE_ROOT", root / "cpp" / "mutation-sweeps")
    config = root / "cpp" / "mull.yml"
    config.parent.mkdir(parents=True)
    _ = config.write_text(_MULL_CONFIG, encoding="utf-8")
    for build in CppTree:
        _ = mutation_cpp_config.leg_config(CppLeg(build), sweep_cache.tree_build_dir(build))
    for relative in (*_READ_BY_A_SWEEP, _UNMUTATED):
        path = root / relative
        if relative in _LOOKED_FOR_ONLY or path.exists():
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_bytes(f"first {relative}".encode())
        path.chmod(0o755)
    names = [_mutant(root / source) for source in _SOURCES] + [_mutant(_OUTSIDE)]
    _ = sweep_cache.tree_binary(CppTree.LEAK).write_bytes(b"\0".join([b"first", *names]))
    return root


_CHANGES = [
    *(
        pytest.param(relative, change, id=f"{relative}-{change}")
        for relative in _READ_BY_A_SWEEP
        if relative not in _LOOKED_FOR_ONLY
        for change in ("rewritten", "removed")
    ),
    *(pytest.param(relative, "created", id=f"{relative}-created") for relative in _LOOKED_FOR_ONLY),
]


@pytest.mark.parametrize(("relative", "change"), _CHANGES)
def test_every_file_a_sweep_reads_moves_the_key(
    tree: Path, relative: Path, change: _Change
) -> None:
    """Rewriting a file at its own size, removing it, or creating it keys the sweep apart."""
    before = sweep_cache.sweep_key()
    _change(tree / relative, change)
    assert sweep_cache.sweep_key() != before


def test_the_sources_keyed_are_the_ones_a_binary_carries_mutants_in(tree: Path) -> None:
    """A source no mutant names is not read by a sweep, and one outside the tree is not keyed."""
    keyed = set(sweep_cache.key_inputs())
    assert {tree / source for source in _SOURCES} <= keyed
    assert tree / _UNMUTATED not in keyed
    assert _OUTSIDE not in keyed
    before = sweep_cache.sweep_key()
    _change(tree / _UNMUTATED, "rewritten")
    assert sweep_cache.sweep_key() == before


_NEEDED = _Name("libneeded.so.1")
_WELL_FORMED = _elf([_Entry(_Tag.NEEDED, _NEEDED)])


def test_a_library_the_binary_needs_is_keyed_where_the_runner_looks_for_it(tree: Path) -> None:
    """The runner looks each needed library up by name in the directory it sweeps from."""
    _ = (tree / _PLAIN_BINARY).write_bytes(_WELL_FORMED)
    beside = tree / "cpp" / _NEEDED
    assert beside in sweep_cache.key_inputs()
    before = sweep_cache.sweep_key()
    _change(beside, "created")
    assert sweep_cache.sweep_key() != before


_NOT_TAKEN = [
    pytest.param(_patched(_WELL_FORMED, _Patch(_FileAt(0), _Image(b"MZ\0\0"))), id="not ELF"),
    pytest.param(_patched(_WELL_FORMED, _Patch(_FileAt(4), _Image(b"\x01"))), id="32-bit"),
    pytest.param(_patched(_WELL_FORMED, _Patch(_FileAt(5), _Image(b"\x02"))), id="big-endian"),
    pytest.param(
        _patched(_WELL_FORMED, _Patch(_FileAt(54), _Image(struct.pack("<H", 32)))),
        id="program headers shorter than one",
    ),
    pytest.param(
        _patched(_WELL_FORMED, _Patch(_FileAt(56), _Image(struct.pack("<H", 2000)))),
        id="program headers past the bound",
    ),
    pytest.param(
        _patched(_WELL_FORMED, _Patch(_STRTAB_VALUE, _Image(struct.pack("<Q", 0)))),
        id="string table in no segment",
    ),
    pytest.param(
        _patched(_WELL_FORMED, _Patch(_LOAD_FILESZ, _Image(struct.pack("<Q", _DYNAMIC_AT)))),
        id="string table past its segment's bytes in the file",
    ),
    pytest.param(
        _patched(_WELL_FORMED, _Patch(_PHOFF, _Image(struct.pack("<Q", 1 << 63)))),
        id="program headers past the file",
    ),
    pytest.param(
        _patched(_WELL_FORMED, _Patch(_DYNAMIC_OFFSET, _Image(struct.pack("<Q", (1 << 64) - 1)))),
        id="dynamic section past the file",
    ),
    pytest.param(
        _patched(_WELL_FORMED, _Patch(_FIRST_VALUE, _Image(struct.pack("<Q", 1 << 63)))),
        id="a name past the file",
    ),
    pytest.param(_elf([_Entry(_Tag.NULL), _Entry(_Tag.NEEDED, _NEEDED)]), id="a name past the end"),
    pytest.param(
        _elf([*[_Entry(_Tag.DEBUG)] * (1 << 16), _Entry(_Tag.NEEDED, _NEEDED)]),
        id="a name past the dynamic bound",
    ),
]


@pytest.mark.parametrize("image", _NOT_TAKEN)
def test_a_file_the_reader_does_not_take_keys_no_library(tree: Path, image: _Image) -> None:
    """A file the reader cannot read whole, or a name it is not to read, keys nothing it names."""
    _ = (tree / _PLAIN_BINARY).write_bytes(image)
    keyed = set(sweep_cache.key_inputs())
    assert tree / "cpp" / _NEEDED not in keyed
    assert tree / "cpp" not in keyed


def test_a_name_is_read_up_to_its_bound(tree: Path) -> None:
    """A name longer than the reader takes is cut at the bound, not read to its end."""
    long = "l" * 5000
    _ = (tree / _PLAIN_BINARY).write_bytes(_elf([_Entry(_Tag.NEEDED, _Name(long))]))
    keyed = {path.name for path in sweep_cache.key_inputs()}
    assert long[:4096] in keyed
    assert long not in keyed


def _searching(tree: Path, searched: _Name, tag: _Tag = _Tag.RUNPATH) -> None:
    """Make the kernel library at build/ one that needs a library and searches ``searched``."""
    _ = (tree / _LIBRARY).write_bytes(_elf([_Entry(_Tag.NEEDED, _NEEDED), _Entry(tag, searched)]))


_SEARCHED = [
    pytest.param("$ORIGIN/../lib", Path("lib"), id="$ORIGIN"),
    pytest.param("${ORIGIN}/sub", Path("build/sub"), id="${ORIGIN}"),
    pytest.param("sub", Path("cpp/sub"), id="relative, from where the sweep runs"),
    pytest.param("", Path("cpp"), id="empty, where the sweep runs"),
]


@pytest.mark.parametrize("tag", [_Tag.RUNPATH, _Tag.RPATH], ids=["runpath", "rpath"])
@pytest.mark.parametrize(("entry", "directory"), _SEARCHED)
def test_a_file_appearing_where_a_loaded_library_searches_moves_the_key(
    tree: Path, tag: _Tag, entry: _Name, directory: Path
) -> None:
    """A library appearing where the loader searches the tree for one keys the sweep apart."""
    outside = tree.parent / "outside"
    _change(outside / _NEEDED, "created")
    _searching(tree, _Name(f"{entry}:{outside}"), tag)
    before = sweep_cache.sweep_key()
    _change(tree / directory / "libother.so", "created")
    assert sweep_cache.sweep_key() != before
    assert not [path for path in sweep_cache.key_inputs() if path.is_relative_to(outside)]


def test_a_library_under_a_searched_directory_s_glibc_hwcaps_moves_the_key(tree: Path) -> None:
    """The loader tries each supported level's subdirectory before the directory itself."""
    _searching(tree, _Name("$ORIGIN/../lib"))
    before = sweep_cache.sweep_key()
    _change(tree / "lib" / "glibc-hwcaps" / "x86-64-v3" / _NEEDED, "created")
    assert sweep_cache.sweep_key() != before


def test_what_a_library_found_in_the_tree_searches_is_followed(tree: Path) -> None:
    """A library the loader finds in the tree searches the tree in turn, by its own $ORIGIN."""
    _searching(tree, _Name("$ORIGIN/../dist"))
    found = tree / "dist" / _NEEDED
    found.parent.mkdir()
    second = _elf(
        [
            _Entry(_Tag.NEEDED, _Name("libsecond.so")),
            _Entry(_Tag.RUNPATH, _Name("$ORIGIN/../other")),
        ]
    )
    _ = found.write_bytes(second)
    before = sweep_cache.sweep_key()
    _change(tree / "other" / "libsecond.so", "created")
    assert sweep_cache.sweep_key() != before


def test_a_needed_name_holding_a_slash_is_a_path_from_where_the_sweep_runs(tree: Path) -> None:
    """The loader opens such a name as it stands; one outside the tree is not the tree's."""
    names = [
        _Entry(_Tag.NEEDED, _Name("sub/libslashed.so")),
        _Entry(_Tag.NEEDED, _Name("/opt/elsewhere/libfoo.so")),
    ]
    _ = (tree / _LIBRARY).write_bytes(_elf(names))
    _ = (tree / _PLAIN_BINARY).write_bytes(_elf(names))
    keyed = set(sweep_cache.key_inputs())
    assert tree / "cpp" / "sub" / "libslashed.so" in keyed
    assert not [path for path in keyed if path.is_relative_to("/opt")]
    before = sweep_cache.sweep_key()
    _change(tree / "cpp" / "sub" / "libslashed.so", "created")
    assert sweep_cache.sweep_key() != before


@pytest.mark.parametrize("searched", ["$LIB", "${PLATFORM}/x", "$ORIGINx/sub"])
@pytest.mark.usefixtures("swept")
def test_a_search_the_key_cannot_follow_is_refused(tree: Path, searched: _Name) -> None:
    """A substitution whose value is the loader's, not the file's, is refused and nothing swept."""
    _searching(tree, _Name(searched))
    assert sweep_cache.sweep_directory() == (
        f"a library a sweep loads searches {searched}, whose substitution the key"
        + " cannot follow, so no kept sweep could say what it read"
    )


@pytest.mark.usefixtures("tree")
def test_the_argv_moves_the_key(monkeypatch: pytest.MonkeyPatch) -> None:
    """A cap per mutant the lane passes differently keys the sweep apart."""
    before = sweep_cache.sweep_key()
    monkeypatch.setattr(mutation_cpp, "CPP_MUTANT_CAP_MS", mutation_cpp.CPP_MUTANT_CAP_MS + 1)
    assert sweep_cache.sweep_key() != before


@pytest.mark.usefixtures("tree")
def test_the_search_path_moves_the_key(monkeypatch: pytest.MonkeyPatch) -> None:
    """The caller's search path is part of the sweep's environment, so of its key."""
    before = sweep_cache.sweep_key()
    monkeypatch.setenv("PATH", "/elsewhere/bin")
    assert sweep_cache.sweep_key() != before


def test_nothing_else_of_the_callers_environment_reaches_a_sweep(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The library override, a sanitizer's options and a locale the caller sets stay out."""
    before = sweep_cache.sweep_key()
    monkeypatch.setenv("ALETHEIA_LIB", "/elsewhere/libaletheia-ffi.so")
    monkeypatch.setenv("ASAN_OPTIONS", "detect_leaks=0")
    monkeypatch.setenv("LC_ALL", "C")
    assert sweep_cache.sweep_key() == before
    build = sweep_cache.tree_build_dir(CppTree.ADDRESS)
    assert mutation_cpp.cpp_sweep_environment(CppLeg(CppTree.ADDRESS), build).variables() == {
        "PATH": os.environ["PATH"],
        "LC_ALL": "C.UTF-8",
        "TMPDIR": tempfile.gettempdir(),
        "ALETHEIA_REPO_ROOT": str(tree),
        "MULL_CONFIG": str(build / "mull-config.yml"),
        "PYTHONUNBUFFERED": "1",
    }


def test_the_runs_make_their_scratch_where_the_reaper_looks(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The temp directory a sweep hands its runs is the one the reaper sweeps after each tree."""
    elsewhere = tree.parent / "scratch"
    monkeypatch.setattr(tempfile, "gettempdir", lambda: str(elsewhere))
    build = sweep_cache.tree_build_dir(CppTree.LEAK)
    variables = mutation_cpp.cpp_sweep_environment(CppLeg(CppTree.LEAK), build).variables()
    assert Path(variables["TMPDIR"]) == scratch_root() == elsewhere


def test_a_tree_elsewhere_keys_apart(tree: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Two trees holding the same files are two keys: the environment names where each is."""
    _ = sweep_cache.tree_binary(CppTree.LEAK).write_bytes(b"first")
    here = sweep_cache.sweep_key()
    elsewhere = tree.parent / "elsewhere"
    _ = shutil.copytree(tree, elsewhere)
    _root_at(monkeypatch, elsewhere)
    assert sweep_cache.sweep_key() != here


# Prints the key of the tree its argument names, in a process of its own.
_KEY_OF = """import sys
from pathlib import Path
import tools.mutation_cpp as lane
import tools.mutation_cpp_config as config
import tools.mutation_sweep_cache as cache
lane.REPO_ROOT = config.REPO_ROOT = cache.REPO_ROOT = Path(sys.argv[1])
print(cache.sweep_key())
"""


def test_the_key_is_the_same_under_every_hash_seed(tree: Path) -> None:
    """The key orders what it digests, so a set's iteration order never reaches it."""
    keys = {
        subprocess.run(
            [sys.executable, "-c", _KEY_OF, str(tree)],
            cwd=_REPO,
            env={**os.environ, "PYTHONHASHSEED": seed},
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        for seed in ("1", "2", "3")
    }
    assert keys == {sweep_cache.sweep_key()}


def _write_reports(directory: Path) -> None:
    """Write every report every tree's sweep writes."""
    for build in CppTree:
        for suffix in CPP_LEG_REPORT_SUFFIXES:
            _ = (directory / f"{CppLeg(build).report_name}{suffix}").write_text("report")


def _reporting(swept: list[Path]) -> Callable[[Path], Prose | None]:
    """Stand in for a sweep that writes every report every tree writes, recording where."""

    def sweep(directory: Path) -> Prose | None:
        swept.append(directory)
        _write_reports(directory)

    return sweep


@pytest.fixture(name="swept")
def _swept(tree: Path, monkeypatch: pytest.MonkeyPatch) -> list[Path]:
    """Record every sweep instead of running one, the runner found as on a host that has it."""
    _ = tree
    swept: list[Path] = []
    monkeypatch.setattr(sweep_cache, "_sweep_into", _reporting(swept))
    monkeypatch.setattr(sweep_cache, "MULL_RUNNER", sys.executable)
    return swept


def test_a_kept_sweep_is_served_without_another(swept: list[Path]) -> None:
    """The same key is served from the directory its sweep filled."""
    first = sweep_cache.sweep_directory()
    assert sweep_cache.sweep_directory() == first
    assert len(swept) == 1


def test_a_sweep_against_one_library_is_not_served_for_another(
    tree: Path, swept: list[Path]
) -> None:
    """A rebuilt library, and then none, each get a sweep of their own."""
    library = tree / _LIBRARY
    first = sweep_cache.sweep_directory()
    _change(library, "rewritten")
    rebuilt = sweep_cache.sweep_directory()
    library.unlink()
    removed = sweep_cache.sweep_directory()
    assert len(swept) == 3
    assert len({first, rebuilt, removed}) == 3


def test_a_refresh_sweeps_a_kept_sweep_again(swept: list[Path]) -> None:
    """Asked to refresh, the cache sweeps again into the same key."""
    first = sweep_cache.sweep_directory()
    assert sweep_cache.sweep_directory(refresh=True) == first
    assert len(swept) == 2


def test_a_refresh_that_fails_keeps_the_kept_sweep(
    swept: list[Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    """The kept sweep is replaced only by a complete one, so a refresh that stops loses nothing."""
    first = sweep_cache.sweep_directory()
    stopped = Prose("the sweep of the leak tree wrote no report")

    def stop(_directory: Path) -> Prose | None:
        return stopped

    monkeypatch.setattr(sweep_cache, "_sweep_into", stop)
    assert sweep_cache.sweep_directory(refresh=True) == stopped
    assert sweep_cache.sweep_directory() == first
    assert len(swept) == 1


# An open file descriptor, as os.open returns one.
_Descriptor = NewType("_Descriptor", int)


def _locked(directory: Path) -> _Descriptor:
    """Hold a lock on a directory as a running sweep does, and give back what holds it."""
    directory.mkdir()
    handle = _Descriptor(os.open(directory, os.O_RDONLY))
    fcntl.flock(handle, fcntl.LOCK_EX)
    return handle


@pytest.mark.usefixtures("swept")
def test_only_the_newest_sweep_is_kept(tree: Path) -> None:
    """Filing a sweep removes every other kept sweep and each abandoned one, not a running one."""
    first = sweep_cache.sweep_directory()
    assert isinstance(first, Path)
    running = sweep_cache.CACHE_ROOT / "sweeping-running"
    handle = _locked(running)
    abandoned = sweep_cache.CACHE_ROOT / "sweeping-abandoned"
    abandoned.mkdir()
    notes = sweep_cache.CACHE_ROOT / "notes"
    notes.mkdir()
    try:
        _change(tree / _LIBRARY, "rewritten")
        second = sweep_cache.sweep_directory()
    finally:
        os.close(handle)
    assert isinstance(second, Path)
    assert sorted(sweep_cache.CACHE_ROOT.iterdir()) == sorted([second, running, notes])


@pytest.mark.usefixtures("tree")
def test_a_sweep_holds_its_directory_s_lock_while_it_runs(monkeypatch: pytest.MonkeyPatch) -> None:
    """Another process asking for the lock is refused until the sweep ends."""
    refused: list[Path] = []

    def sweep(directory: Path) -> Prose | None:
        handle = os.open(directory, os.O_RDONLY)
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            refused.append(directory)
        finally:
            os.close(handle)
        _write_reports(directory)

    monkeypatch.setattr(sweep_cache, "_sweep_into", sweep)
    monkeypatch.setattr(sweep_cache, "MULL_RUNNER", sys.executable)
    assert isinstance(sweep_cache.sweep_directory(), Path)
    assert len(refused) == 1


class _InterruptedError(Exception):
    """A sweep ended by something other than a reason it gives."""


@pytest.mark.usefixtures("tree")
def test_a_sweep_that_raised_leaves_nothing(monkeypatch: pytest.MonkeyPatch) -> None:
    """However a sweep ends, its partial directory goes with it."""

    def sweep(directory: Path) -> Prose | None:
        _ = (directory / "partial").write_text("report")
        raise _InterruptedError

    monkeypatch.setattr(sweep_cache, "_sweep_into", sweep)
    monkeypatch.setattr(sweep_cache, "MULL_RUNNER", sys.executable)
    with pytest.raises(_InterruptedError):
        _ = sweep_cache.sweep_directory()
    assert not list(sweep_cache.CACHE_ROOT.iterdir())


_STALE_CONFIGS = [
    pytest.param(_MULL_CONFIG + "timeout: 1000\n", id="a key every tree reads"),
    pytest.param(
        _MULL_CONFIG.replace("  - cxx_remove_void_call\n", ""),
        id="a mutator only the whole trees read",
    ),
]


@pytest.mark.parametrize("config", _STALE_CONFIGS)
def test_a_tree_built_under_another_configuration_is_refused_and_kept(
    tree: Path, swept: list[Path], config: ConfigText
) -> None:
    """The cache never rebuilds a tree: a stale one is reported, kept, and nothing is swept."""
    _ = (tree / "cpp" / "mull.yml").write_text(config, encoding="utf-8")
    result = sweep_cache.sweep_directory()
    assert isinstance(result, str)
    assert f"the {CppTree.LEAK.value} mutation tree was built under another configuration" in result
    assert not swept
    assert all(sweep_cache.tree_binary(build).is_file() for build in CppTree)
    assert not sweep_cache.CACHE_ROOT.exists()


@pytest.mark.usefixtures("swept")
def test_an_unbuilt_tree_is_reported(tree: Path) -> None:
    """A tree whose binary does not run is named, before anything is swept."""
    sweep_cache.tree_binary(CppTree.PLAIN).chmod(0o644)
    assert sweep_cache.sweep_directory() == f"the {CppTree.PLAIN.value} mutation tree is not built"
    assert not (tree / "cpp" / "mutation-sweeps").exists()


@pytest.mark.usefixtures("swept")
def test_a_missing_runner_is_reported(monkeypatch: pytest.MonkeyPatch) -> None:
    """A host without the runner is told so rather than sweeping with another."""
    monkeypatch.setattr(sweep_cache, "MULL_RUNNER", "/nowhere/mull-runner-23")
    assert sweep_cache.sweep_directory() == "/nowhere/mull-runner-23 is not installed"


def test_a_tree_changed_while_it_was_swept_is_not_kept(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The key is read again when the sweep ends, and a sweep of a tree that moved is dropped."""

    def sweep(directory: Path) -> Prose | None:
        _write_reports(directory)
        _change(tree / _LIBRARY, "rewritten")

    monkeypatch.setattr(sweep_cache, "_sweep_into", sweep)
    monkeypatch.setattr(sweep_cache, "MULL_RUNNER", sys.executable)
    assert sweep_cache.sweep_directory() == (
        "the trees changed while they were swept; the sweep was not kept"
    )
    assert not list(sweep_cache.CACHE_ROOT.iterdir())


@pytest.mark.usefixtures("tree")
def test_a_sweep_that_stopped_leaves_nothing(monkeypatch: pytest.MonkeyPatch) -> None:
    """A sweep that says why it stopped is reported, and its partial directory removed."""
    stopped = Prose("the sweep of the leak tree wrote no report")

    def sweep(directory: Path) -> Prose | None:
        _ = (directory / "partial").write_text("report")
        return stopped

    monkeypatch.setattr(sweep_cache, "_sweep_into", sweep)
    monkeypatch.setattr(sweep_cache, "MULL_RUNNER", sys.executable)
    assert sweep_cache.sweep_directory() == stopped
    assert not list(sweep_cache.CACHE_ROOT.iterdir())


# A runner standing in for Mull: it writes every report a leg writes, and
# records the directory it ran in, its argv and its environment beside them.
_RUNNER = """#!{python}
import os
import sys

options = dict(arg.split("=", 1) for arg in sys.argv[1:] if arg.startswith("--report-"))
base = os.path.join(options["--report-dir"], options["--report-name"])
for suffix in {suffixes!r}:
    open(base + suffix, "w").close()
with open(base + ".cwd", "w") as out:
    out.write(os.getcwd())
with open(base + ".argv", "w") as out:
    out.write("\\0".join(sys.argv))
with open(base + ".env", "w") as out:
    out.write("\\0".join(name + "=" + value for name, value in sorted(os.environ.items())))
with open(base + ".cpus", "w") as out:
    out.write(",".join(str(cpu) for cpu in sorted(os.sched_getaffinity(0))))
"""


def _fake_runner(tree: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Install the runner standing in for Mull as the one the cache runs."""
    runner = tree.parent / "runner"
    _ = runner.write_text(
        _RUNNER.format(python=sys.executable, suffixes=tuple(CPP_LEG_REPORT_SUFFIXES)),
        encoding="utf-8",
    )
    runner.chmod(0o755)
    monkeypatch.setattr(sweep_cache, "MULL_RUNNER", str(runner))
    return runner


def _assert_ran_as_the_lane(tree: Path, base: Path, leg: CppLeg, build_dir: Path) -> None:
    """Check the stand-in runner ran in the lane's directory and environment for ``leg``."""
    assert Path(base.with_suffix(".cwd").read_text(encoding="utf-8")) == tree / "cpp"
    text = base.with_suffix(".env").read_text(encoding="utf-8")
    recorded = dict(item.split("=", 1) for item in text.split("\0"))
    assert recorded == mutation_cpp.cpp_sweep_environment(leg, build_dir).variables()


def test_each_tree_is_swept_as_the_lane_sweeps_it(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The lane's argv, directory and environment, tree by tree, the scratch reaped after each."""
    runner = _fake_runner(tree, monkeypatch)
    reaped: list[frozenset[Path]] = []

    def reap() -> None:
        reaped.append(frozenset(sweep_cache.CACHE_ROOT.rglob("*.argv")))

    monkeypatch.setattr(sweep_cache, "reap_dead_scratch_dirs", reap)
    kept = sweep_cache.sweep_directory()
    assert isinstance(kept, Path)
    for build in CppTree:
        leg = CppLeg(build)
        build_dir = sweep_cache.tree_build_dir(build)
        base = kept / leg.report_name
        _assert_ran_as_the_lane(tree, base, leg, build_dir)
        argv = base.with_suffix(".argv").read_text(encoding="utf-8").split("\0")
        report_dir = Path(
            next(arg for arg in argv if arg.startswith("--report-dir=")).split("=", 1)[1]
        )
        assert report_dir.parent == sweep_cache.CACHE_ROOT
        assert argv == mutation_cpp.cpp_lane_command(str(runner), build_dir, report_dir, leg)
    assert [len(argvs) for argvs in reaped] == [1, 2, 3]


def test_a_dry_run_of_a_slice_runs_the_lanes_command_for_it(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The slice's own tree, configuration and report name, and the runner told to run no mutant."""
    runner = _fake_runner(tree, monkeypatch)
    leg = CppLeg(CppTree.PLAIN, 2)
    build_dir = sweep_cache.leg_build_dir(leg)
    assert build_dir == tree / "cpp" / f"{CppTree.PLAIN.directory}-2"
    report_dir = tree.parent / "reports"
    report_dir.mkdir()
    assert sweep_cache.dry_run_report(leg, report_dir) == report_dir / f"{leg.report_name}.json"
    base = report_dir / leg.report_name
    _assert_ran_as_the_lane(tree, base, leg, build_dir)
    argv = base.with_suffix(".argv").read_text(encoding="utf-8").split("\0")
    assert argv == mutation_cpp.cpp_lane_command(
        str(runner), build_dir, report_dir, leg, dry_run=True
    )


def test_a_dry_run_that_wrote_no_report_says_so(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A runner that ran and left no Elements report is reported, not read."""
    monkeypatch.setattr(sweep_cache, "MULL_RUNNER", "true")
    leg = CppLeg(CppTree.LEAK)
    assert sweep_cache.dry_run_report(leg, tree.parent) == (
        f"the dry run of the {leg} leg wrote no {leg.report_name}.json"
    )


def _without_report_dir(argv_file: Path) -> list[Path]:
    """Read a recorded argv with the directory its reports went to taken out, as paths."""
    argv = argv_file.read_text(encoding="utf-8").split("\0")
    return [Path(arg) for arg in argv if not arg.startswith("--report-dir=")]


def test_the_lane_and_the_cache_run_the_runner_alike(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The CI lane's runner and the cache's start in one directory, under one environment and argv.

    The lane is run for one leg as a CI job runs it, its tools stood in for on
    the search path, a cmake that builds nothing among them, so the runner it
    starts is the one under test; only where each writes its reports differs.
    """
    tools = tree.parent / "bin"
    tools.mkdir()
    runner = tools / "mull-runner-23"
    _ = runner.write_text(
        _RUNNER.format(python=sys.executable, suffixes=tuple(CPP_LEG_REPORT_SUFFIXES)),
        encoding="utf-8",
    )
    for stand_in in (runner, tools / "cmake", tools / "clang++-23"):
        if not stand_in.exists():
            _ = stand_in.write_text("#!/bin/sh\n", encoding="utf-8")
        stand_in.chmod(0o755)
    home = tree.parent / "home"
    plugin = home / ".local" / "bin" / "mull-ir-frontend-23"
    plugin.parent.mkdir(parents=True)
    _ = plugin.write_text("plugin", encoding="utf-8")
    monkeypatch.setenv("HOME", str(home))
    monkeypatch.setenv("PATH", f"{tools}{os.pathsep}{os.environ['PATH']}")
    monkeypatch.setenv(CPP_STAGE_ENV, CppTree.LEAK.value)
    monkeypatch.delenv(CPP_SLICE_ENV, raising=False)
    monkeypatch.setattr(mutation_cpp, "reap_dead_scratch_dirs", lambda: 0)
    leg = CppLeg(CppTree.LEAK)
    lane, cache = tree.parent / "lane", tree.parent / "cache"
    lane.mkdir()
    cache.mkdir()
    _ = mutation_cpp.run_cpp(lane)
    sweep_cache.run_leg(leg, cache)
    lane_base, cache_base = lane / leg.report_name, cache / leg.report_name
    assert lane_base.with_suffix(".cwd").read_text(encoding="utf-8") == (
        cache_base.with_suffix(".cwd").read_text(encoding="utf-8")
    )
    assert lane_base.with_suffix(".env").read_text(encoding="utf-8") == (
        cache_base.with_suffix(".env").read_text(encoding="utf-8")
    )
    lane_argv = _without_report_dir(lane_base.with_suffix(".argv"))
    assert lane_argv == _without_report_dir(cache_base.with_suffix(".argv"))
    assert lane_argv[0] == runner


def test_the_cache_runs_the_runner_inside_the_cpus_it_leaves(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The runner the cache starts runs on the CPUs the prefix names, not on all it was given."""
    if shutil.which("taskset") is None or len(os.sched_getaffinity(0)) < 2:
        pytest.skip("pinning needs taskset and two CPUs to leave one free")
    _ = _fake_runner(tree, monkeypatch)
    leg = CppLeg(CppTree.LEAK)
    sweep_cache.run_leg(leg, tree.parent)
    text = (tree.parent / f"{leg.report_name}.cpus").read_text(encoding="utf-8")
    recorded = {Cpu(int(cpu)) for cpu in text.split(",")}
    assert recorded == _pinned(sweep_cache.polite(["runner"]))


_MACHINE = 24
_GIVEN = frozenset({Cpu(4), Cpu(5), Cpu(9), Cpu(10)})
_ARGV = ["mull-runner-23", "unit_tests"]


def _taskset(_name: str) -> str:
    """Find taskset, as a host that has it does."""
    return "/usr/bin/taskset"


def _nowhere(_name: str) -> None:
    """Find nothing, as a host without taskset does."""


def _given(monkeypatch: pytest.MonkeyPatch, cpus: frozenset[Cpu]) -> None:
    """Fake a machine of ``_MACHINE`` CPUs with taskset installed, the process given ``cpus``."""

    def affinity(_pid: int) -> set[int]:
        return set(cpus)

    monkeypatch.setattr(os, "cpu_count", lambda: _MACHINE)
    monkeypatch.setattr(os, "sched_getaffinity", affinity)
    monkeypatch.setattr(shutil, "which", _taskset)


def _pinned(argv: list[str]) -> frozenset[Cpu]:
    """Read the CPUs a ``taskset -c`` prefix names, ranges included."""
    assert argv[:2] == ["taskset", "-c"]
    cpus: set[Cpu] = set()
    for part in argv[2].split(","):
        low, _, high = part.partition("-")
        cpus.update(Cpu(cpu) for cpu in range(int(low), int(high or low) + 1))
    return frozenset(cpus)


def test_the_sweep_is_pinned_inside_the_cpus_it_was_given(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every given CPU but the highest, and none outside them."""
    _given(monkeypatch, _GIVEN)
    argv = polite(_ARGV)
    assert _pinned(argv) == _GIVEN - {max(_GIVEN)}
    assert argv[3:] == _ARGV


def test_a_sweep_given_one_cpu_keeps_it(monkeypatch: pytest.MonkeyPatch) -> None:
    """There is no CPU to leave, so the sweep runs on the one it has."""
    _given(monkeypatch, frozenset({Cpu(7)}))
    assert _pinned(polite(_ARGV)) == {Cpu(7)}


def test_without_taskset_the_runner_is_left_alone(monkeypatch: pytest.MonkeyPatch) -> None:
    """A host without the tool runs the argv as the lane wrote it."""
    monkeypatch.setattr(shutil, "which", _nowhere)
    assert polite(_ARGV) == _ARGV
