# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Sweeps of the mutation lanes, kept for every probe that reads them.

Several probes each state a claim about one sweep: that the recorded census is
what a sweep produces, that the recorded routes are, that every survivor and
every unobserved kill is a recorded one.  Written to sweep for themselves they
re-measure one run once per claim: four of them on three trees took 674, 650,
622 and 648 seconds.  This runs the sweep once and keys it on what could change
its outcome, so the second reader pays nothing and each probe still runs alone.
The same holds across runs of the store: a probe that sweeps the C++ trees
under another order of the cases, or without ending a run at its first failing
assertion, took 775 and 1605 seconds, and the Go and Rust baselines 181 and
162, each of them on every run of the store over an unchanged tree.

A key has two halves: what a sweep reads from the tree, and how it runs.  A
C++ sweep's first half is the content of every file it reads from the tree or
the fact that the file is absent.  A trace of the lane's own command finds the
files: each tree's test binary
and the test kernels built beside it, which the binary loads by path; the
stand-in kernels the build makes beside the kernel library, loaded by path too; the
binaries it runs as children, built into a directory of their own; the
configuration the runner is given; the kernel library, at every path in the
tree the tests look for it; the fixture a test reads; the source files the
binary's mutants point at, which the runner copies into its report; the
libraries the binary needs, which the runner looks for by name in the
directory it runs in; and every file the loader can open in a directory in the
tree that a file the sweep loads searches, followed from library to
library.  Its second half is the argv each tree is swept with, its paths taken
within the tree, and the environment it sweeps under, which names where the
tree is.  The environment is the sweep's own, taking nothing of the caller's
but its search path and temp directory; the order among the tests is pinned
and the cap is on the argv; so nothing else in the tree decides what a sweep
reports, which is why the same key may be served rather than swept again.  What
a sweep reads from outside the tree is not keyed: the runner, the system's and
GHC's runtime libraries, and the one library path the tests look at above the
repository.  A probe's variant of the lane, another order of the cases or no
end at the first failing assertion over some of the trees, moves the second
half only.

The Go and Rust lanes sweep a scratch copy of the tracked tree, so the first
half of their key is the tree's id, which names every tracked file as it
stands, with the kernel library their tests load, the stand-in kernels beside
it, and what the loader reaches from them.  The second half is where each tool
of the lane's toolchain is found and what it says of itself, and the caller's
variables the tools and the tests read.

A C++ tree has to have been built under the configuration it would be given
now, and every search path a loaded library records has to be one the key can
follow, or the reason is reported and nothing is swept: the cache reads the
trees and never removes one.  The key is read again when the sweep ends, and a
sweep of a tree that changed meanwhile is not kept.

The reports land under a directory named by the key, and a sweep writes into a
temporary neighbour, locked while it runs, that is renamed into place when
every report is there: a run interrupted halfway leaves no directory a later
reader would trust, and a later sweep removes it once its lock is free.  Once a
sweep is in place every kept sweep of its kind that read another tree is
removed, so the sweeps kept are those of the tree as it stands, the lane's and
each variant beside it; a refresh sweeps again and replaces the kept sweep
only with a complete one.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import mmap
import os
import re
import shutil
import struct
import subprocess
import tempfile
from enum import IntEnum
from functools import partial
from pathlib import Path
from typing import TYPE_CHECKING, BinaryIO, Literal, NamedTuple, NewType, cast

from tools._common import emit
from tools._resources import polite_cpu_list
from tools.cpp_scratch import reap_dead_scratch_dirs
from tools.mutation_cpp import (
    CPP_LEG_REPORT_SUFFIXES,
    CPP_TEST_TARGET,
    LANE_RUN,
    REPO_ROOT,
    CppRun,
    cpp_lane_command,
    cpp_sweep_directory,
    cpp_sweep_environment,
)
from tools.mutation_cpp_config import built_under_config, leg_config_path
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_go import GO_RAW_LOG
from tools.mutation_run import run_go
from tools.mutation_rust import OUTCOMES, run_rust
from tools.sweep_evidence import tracked_tree

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable

# Where the sweeps are kept: inside the tree, beside the build trees the
# .gitignore already holds out, because a probe reads no path outside it.
CACHE_ROOT = REPO_ROOT / "cpp" / "mutation-sweeps"

# The runner the lane names. Read here rather than searched for, so a reader
# without it is told what is missing instead of sweeping with another one.
MULL_RUNNER = "mull-runner-23"

# The kernel library, at every path in the tree the tests look for it from the
# root the sweep passes and the directory it runs in, cpp/: the integration
# tests try build/ and then dist/, the renderer and the test binary's runtime
# listener build/ and then cpp/build/. Which of them a run loads depends on all
# of them, so each is keyed.
_LIBRARY_PATHS = (
    Path("build/libaletheia-ffi.so"),
    Path("dist/aletheia/lib/libaletheia-ffi.so"),
    Path("cpp/build/libaletheia-ffi.so"),
)

# Where the build makes the stand-in kernels the tests load by path, beside
# the library (Shakefile.hs).
STAND_IN_DIR = Path("build/stand-ins")

# The fixtures the tests read from the tree.
_FIXTURES = (Path("examples/demo/demo_workbook.xlsx"),)

# The directory of a mutation tree the binaries its test binary runs as
# processes of their own are built into (cpp/CMakeLists.txt).
CPP_FRESH_PROCESS_DIR = "fresh-process"

# How a mutant is named inside the binary that carries it: its mutator, the
# absolute path of its source file, its span, a hash and an ordinal. The runner
# enables a mutant by that name and copies each named file into its report.
_MUTANT = re.compile(rb"[a-z][a-z_]*:(/[^\x00:\n]+):\d+:\d+:\d+:\d+:[0-9a-f]+\.\d+")

# A kept sweep's directory, named by its key: its kind, the digest of what it
# read from the tree and the digest of how it ran. And the prefix of the
# directory a sweep writes into until every report is there.
_KEPT = re.compile(r"(cpp|go|rust)-([0-9a-f]{16})-[0-9a-f]{16}")
_STAGING_PREFIX = "sweeping-"

# The one substitution the loader makes in a search path that the file itself
# decides: $ORIGIN, braced or bare, a bare one ending where no name character
# follows. Any other, $LIB or $PLATFORM, takes the loader's value.
_ORIGIN = re.compile(r"\$(?:\{ORIGIN\}|ORIGIN(?![A-Za-z0-9_]))")

# What the linking reader reads of an ELF64 little-endian file: its
# identification; the header's e_phoff, e_phentsize and e_phnum; each program
# header's p_type, p_offset, p_vaddr and p_filesz; each dynamic entry's tag
# and value; at most this many bytes of a name; at most these many bytes of
# program headers, past which a file is not one the reader takes; and at most
# these many bytes of dynamic section, past which its entries are not read.
_ELF64_LITTLE_ENDIAN = b"\x7fELF\x02\x01"
_ELF_HEADER = struct.Struct("<32xQ14xHH")
_SEGMENT = struct.Struct("<I4xQQ8xQ")
_DYNAMIC_ENTRY = struct.Struct("<qQ")
_LONGEST_NAME = 4096
_LONGEST_TABLE = 1 << 16
_LONGEST_DYNAMIC = 1 << 20

# A kept sweep's key, one of the two digests it carries, a line one of them
# digests, and a file's digest as the key spells it.
SweepKey = NewType("SweepKey", str)
_KeyPart = NewType("_KeyPart", str)
_KeyLine = NewType("_KeyLine", str)
_FileDigest = NewType("_FileDigest", str)

# A lane tool's command line, asking it what it is, its words split at spaces.
_ToolQuery = NewType("_ToolQuery", str)

# What a kept sweep sweeps: the C++ trees, or the Go or Rust lane's package.
SweepKind = Literal["cpp", "go", "rust"]
LaneKind = Literal["go", "rust"]

# A name as the string table holds it; a library's file name, as a binary
# records it; a library search path as a binary records it, $ORIGIN and all.
_RawName = NewType("_RawName", bytes)
_LibraryName = NewType("_LibraryName", str)
_SearchPath = NewType("_SearchPath", str)

# Places in an ELF file, kept apart so that one is never read as another: a
# byte's offset in the file, the address it loads at, a count of bytes, and a
# name's offset in the string table.
_FileOffset = NewType("_FileOffset", int)
_Address = NewType("_Address", int)
_Length = NewType("_Length", int)
_NameOffset = NewType("_NameOffset", int)


class _SegmentType(IntEnum):
    """The program header types the reader keeps."""

    LOAD = 1
    DYNAMIC = 2


class _DynamicTag(IntEnum):
    """The dynamic tags the reader keeps: the end, a needed library, the strings, a search path."""

    NULL = 0
    NEEDED = 1
    STRTAB = 5
    RPATH = 15
    RUNPATH = 29


class _Span(NamedTuple):
    """A run of bytes in the file."""

    offset: _FileOffset
    length: _Length


class _Loadable(NamedTuple):
    """A loadable segment: its bytes in the file, and the address the first of them loads at."""

    span: _Span
    address: _Address

    def locate(self, address: _Address) -> _FileOffset | None:
        """Name the file offset of the byte loaded at ``address``, if this segment holds it."""
        if self.address <= address < self.address + self.span.length:
            return _FileOffset(self.span.offset + address - self.address)
        return None


class _Segments(NamedTuple):
    """What the reader keeps of a file's program headers."""

    loadable: list[_Loadable]
    dynamic: _Span | None


class _Dynamic(NamedTuple):
    """What the reader keeps of the dynamic section: where its strings load, and each name."""

    strings: _Address | None
    needed: list[_NameOffset]
    searched: list[_NameOffset]


class _Linked(NamedTuple):
    """What an ELF file records about its linking: the libraries it needs, and where to look."""

    needed: list[_LibraryName]
    searched: list[_SearchPath]


def polite(argv: list[str]) -> list[str]:
    """Run the sweep on every CPU it was given but one, so the machine stays usable while it does.

    Mull decides its own worker count from the machine, and a sweep that takes
    every core makes the desktop it runs on unusable for the minutes it lasts.
    The affinity is set outside the runner rather than by an argument, because
    the argument is part of what the lane sweeps with and this is not: it
    changes when the mutants run, never which of them run or what each reads.
    A host without the tool is left alone.
    """
    if shutil.which("taskset") is None:
        return argv
    return ["taskset", "-c", polite_cpu_list(), *argv]


def leg_build_dir(leg: CppLeg) -> Path:
    """Name the directory one leg's tree is built in."""
    return cpp_sweep_directory() / leg.directory


def tree_build_dir(tree: CppTree) -> Path:
    """Name the directory one whole tree is built in."""
    return leg_build_dir(CppLeg(tree))


def tree_binary(tree: CppTree) -> Path:
    """Name the test binary of one tree, which the runner runs once per mutant."""
    return tree_build_dir(tree) / CPP_TEST_TARGET


def _digest(path: Path) -> _FileDigest:
    """Digest a file, read in blocks so a 100 MB binary costs no memory."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return _FileDigest(digest.hexdigest())


def _segments(handle: BinaryIO, size: _Length) -> _Segments:
    """Read an ELF64 little-endian file's loadable and dynamic segments; none from another file."""
    header = handle.read(_ELF_HEADER.size)
    if len(header) < _ELF_HEADER.size or not header.startswith(_ELF64_LITTLE_ENDIAN):
        return _Segments([], None)
    phoff, phentsize, phnum = _ELF_HEADER.unpack(header)
    if phentsize < _SEGMENT.size or phentsize * phnum > _LONGEST_TABLE or phoff >= size:
        return _Segments([], None)
    _ = handle.seek(phoff)
    table = handle.read(phentsize * phnum)
    loadable: list[_Loadable] = []
    dynamic: _Span | None = None
    for at in range(len(table) // phentsize):
        kind, offset, address, length = _SEGMENT.unpack_from(table, at * phentsize)
        span = _Span(_FileOffset(offset), _Length(length))
        if kind == _SegmentType.LOAD:
            loadable.append(_Loadable(span, _Address(address)))
        elif kind == _SegmentType.DYNAMIC:
            dynamic = span
    return _Segments(loadable, dynamic)


def _dynamic(handle: BinaryIO, span: _Span, size: _Length) -> _Dynamic:
    """Read the dynamic section's entries up to the one that ends them; none past the file's end."""
    if span.offset >= size:
        return _Dynamic(None, [], [])
    _ = handle.seek(span.offset)
    section = handle.read(min(span.length, _LONGEST_DYNAMIC))
    strings: _Address | None = None
    needed: list[_NameOffset] = []
    searched: list[_NameOffset] = []
    whole = section[: len(section) - len(section) % _DYNAMIC_ENTRY.size]
    for tag, value in _DYNAMIC_ENTRY.iter_unpack(whole):
        if tag == _DynamicTag.NULL:
            break
        if tag == _DynamicTag.STRTAB:
            strings = _Address(value)
        elif tag == _DynamicTag.NEEDED:
            needed.append(_NameOffset(value))
        elif tag in (_DynamicTag.RPATH, _DynamicTag.RUNPATH):
            searched.append(_NameOffset(value))
    return _Dynamic(strings, needed, searched)


def _linked(binary: Path) -> _Linked:
    """Read what an ELF64 little-endian file records about its linking; nothing from another file.

    The dynamic section holds each name as an offset into the string table,
    whose address maps to a file offset through the loadable segment that
    holds it.  An offset past the file's end reads as nothing, and so does an
    empty name.
    """
    with binary.open("rb") as handle:
        size = _Length(os.fstat(handle.fileno()).st_size)
        segments = _segments(handle, size)
        if segments.dynamic is None:
            return _Linked([], [])
        dynamic = _dynamic(handle, segments.dynamic, size)
        strings = dynamic.strings
        if strings is None:
            return _Linked([], [])
        placed = [segment.locate(strings) for segment in segments.loadable]
        table = next((offset for offset in placed if offset is not None), None)
        if table is None:
            return _Linked([], [])

        def name_at(offset: _NameOffset) -> _RawName:
            if table + offset >= size:
                return _RawName(b"")
            _ = handle.seek(table + offset)
            return _RawName(handle.read(_LONGEST_NAME).split(b"\0", 1)[0])

        needed = [_LibraryName(os.fsdecode(name_at(offset))) for offset in dynamic.needed]
        searched = [_SearchPath(os.fsdecode(name_at(offset))) for offset in dynamic.searched]
        return _Linked([name for name in needed if name], [path for path in searched if path])


def binary_sources(binary: Path) -> set[Path]:
    """Name the source files the mutants a binary carries point at, which the runner reads."""
    with binary.open("rb") as handle:
        if os.fstat(handle.fileno()).st_size == 0:
            return set()
        with mmap.mmap(handle.fileno(), 0, access=mmap.ACCESS_READ) as mapped:
            return {Path(os.fsdecode(path)) for path in _MUTANT.findall(mapped)}


class _Reach(NamedTuple):
    """What the loader can open in the tree for the files a sweep loads, and what it cannot follow.

    The files are every file of every directory in the tree that one of those
    files searches, and every file a name it needs points at directly.  A
    search path the key cannot follow names a substitution whose value is the
    loader's rather than the file's.
    """

    files: set[Path]
    unfollowed: list[_SearchPath]


def _loaded() -> list[Path]:
    """Name the ELF files a sweep loads from the tree, whether they are there or not.

    The kernel library at every path the tests look for it, the stand-in
    kernels the build makes beside it, each tree's test binary, the test
    kernels built beside it and the binaries it runs as children, which the
    binary names by path and is not relinked for, so its digest cannot stand
    for theirs.
    """
    loaded = [REPO_ROOT / path for path in _LIBRARY_PATHS]
    loaded.extend(sorted((REPO_ROOT / STAND_IN_DIR).glob("*.so")))
    for tree in CppTree:
        loaded.append(tree_binary(tree))
        loaded.extend(sorted(tree_build_dir(tree).glob("libaletheia_test_*.so")))
        loaded.extend(sorted((tree_build_dir(tree) / CPP_FRESH_PROCESS_DIR).glob("*")))
    return loaded


def _searched_files(directory: Path) -> set[Path]:
    """Name the files the loader can open in a directory it searches, glibc-hwcaps ones included."""
    if not directory.is_dir():
        return set()
    candidates = (*directory.iterdir(), *directory.glob("glibc-hwcaps/*/*"))
    return {path for path in candidates if path.is_file()}


def _reach(loaded: Iterable[Path], runs_in: Path) -> _Reach:
    """Follow what the loader can open in the tree, from the given files through each file found.

    A search path entry takes $ORIGIN as the directory of the file recording
    it, and one that is relative, or empty, as ``runs_in``, the directory the
    sweep runs in.  A name holding a slash is a path the loader opens as it
    stands, from that same directory when it is relative.
    """
    files: set[Path] = set()
    unfollowed: list[_SearchPath] = []
    seen: set[Path] = set()
    pending = [path for path in loaded if path.is_file()]
    while pending:
        elf = pending.pop()
        if elf in seen:
            continue
        seen.add(elf)
        linked = _linked(elf)
        reached: set[Path] = set()
        for searched in linked.searched:
            for entry in searched.split(":"):
                # A replacement string reads a backslash as an escape.
                expanded = _ORIGIN.sub(str(elf.parent).replace("\\", "\\\\"), entry)
                if "$" in expanded:
                    unfollowed.append(_SearchPath(entry))
                    continue
                directory = Path(os.path.normpath(runs_in / expanded))
                if directory.is_relative_to(REPO_ROOT):
                    reached |= _searched_files(directory)
        for name in linked.needed:
            if "/" in name:
                path = Path(os.path.normpath(runs_in / name))
                if path.is_relative_to(REPO_ROOT):
                    files.add(path)
                    reached |= {path} if path.is_file() else set()
        files |= reached
        pending.extend(sorted(reached - seen))
    return _Reach(files, unfollowed)


def key_inputs() -> list[Path]:
    """Name every file a sweep of today's trees reads from the tree, whether it is there or not."""
    loaded = _loaded()
    paths = {
        *loaded,
        *(REPO_ROOT / path for path in _FIXTURES),
        *_reach(loaded, cpp_sweep_directory()).files,
    }
    for tree in CppTree:
        build_dir, binary = tree_build_dir(tree), tree_binary(tree)
        paths.add(leg_config_path(CppLeg(tree), build_dir))
        if binary.is_file():
            # The runner looks each library the binary needs up by name in the
            # directory it runs in; a name holding a slash is followed above.
            needed = [name for name in _linked(binary).needed if "/" not in name]
            paths.update(cpp_sweep_directory() / name for name in needed)
            paths.update(path for path in binary_sources(binary) if path.is_relative_to(REPO_ROOT))
    return sorted(paths)


def _part(lines: Iterable[_KeyLine]) -> _KeyPart:
    """Digest the lines of one half of a key."""
    return _KeyPart(hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16])


def _files_lines(paths: Iterable[Path]) -> list[_KeyLine]:
    """Spell each file a sweep reads from the tree by its content, or as absent."""
    return [
        _KeyLine(f"{path.relative_to(REPO_ROOT)}:{_digest(path) if path.is_file() else 'absent'}")
        for path in paths
    ]


class CppVariant(NamedTuple):
    """The C++ trees a sweep covers and how the runner runs each: the lane's way, or a probe's."""

    trees: tuple[CppTree, ...]
    run: CppRun = LANE_RUN


# The lane's own sweep.
CPP_LANE = CppVariant(tuple(CppTree))


def _cpp_run(variant: CppVariant) -> _KeyPart:
    """Digest how a variant sweeps: each of its trees' argv and environment."""
    lines: list[_KeyLine] = []
    for tree in variant.trees:
        leg = CppLeg(tree)
        argv = cpp_lane_command(MULL_RUNNER, Path(tree.directory), Path(), leg, variant.run)
        lines.append(_KeyLine(" ".join(argv)))
        variables = cpp_sweep_environment(leg, tree_build_dir(tree)).variables()
        lines.append(_KeyLine(" ".join(f"{name}={variables[name]}" for name in sorted(variables))))
    return _part(lines)


def sweep_key(variant: CppVariant = CPP_LANE) -> SweepKey:
    """Name what a sweep of today's trees would read, their files, and how it would run them."""
    return SweepKey(f"cpp-{_part(_files_lines(key_inputs()))}-{_cpp_run(variant)}")


def _reports_present(trees: tuple[CppTree, ...], directory: Path) -> bool:
    """Say whether the directory holds every report each of the trees' sweeps writes."""
    return all(
        (directory / f"{CppLeg(tree).report_name}{suffix}").is_file()
        for tree in trees
        for suffix in CPP_LEG_REPORT_SUFFIXES
    )


def run_leg(leg: CppLeg, report_dir: Path, run: CppRun = LANE_RUN) -> None:
    """Run the lane's command for one leg into ``report_dir``, as ``run`` says.

    The runner exits non-zero whenever a mutant survives, which is a property
    of the surface rather than of the run, so the reports are what says
    whether it ran.
    """
    build_dir = leg_build_dir(leg)
    _ = subprocess.run(
        polite(cpp_lane_command(MULL_RUNNER, build_dir, report_dir, leg, run)),
        cwd=cpp_sweep_directory(),
        env=cpp_sweep_environment(leg, build_dir).variables(),
        check=False,
        capture_output=True,
    )


def dry_run_report(leg: CppLeg, report_dir: Path) -> Path | Prose:
    """Run the lane's command over one leg as a dry run, and name the Elements report it wrote."""
    run_leg(leg, report_dir, CppRun(dry_run=True))
    report = report_dir / f"{leg.report_name}.json"
    if report.is_file():
        return report
    return Prose(f"the dry run of the {leg} leg wrote no {report.name}")


def _sweep_into(variant: CppVariant, directory: Path) -> Prose | None:
    """Sweep a variant's trees into the directory, or say what stopped it."""
    for tree in variant.trees:
        leg = CppLeg(tree)
        run_leg(leg, directory, variant.run)
        _ = reap_dead_scratch_dirs()
        missing = [
            suffix
            for suffix in CPP_LEG_REPORT_SUFFIXES
            if not (directory / f"{leg.report_name}{suffix}").is_file()
        ]
        if missing:
            return Prose(
                f"the sweep of the {tree.value} tree wrote no {leg.report_name}{missing[0]}"
            )
    return None


def _abandoned(staging: Path) -> bool:
    """Say whether the sweep writing into ``staging`` has gone, its lock free to take.

    A sweep holds a ``flock`` on its directory for as long as it runs, which
    the kernel drops however the process ends, the way the test binaries'
    scratch directories are told live from dead.
    """
    try:
        handle = os.open(staging, os.O_RDONLY | os.O_CLOEXEC)
    except OSError:
        return False
    try:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        return False
    finally:
        os.close(handle)
    return True


def _forget_other_sweeps(kept: Path) -> None:
    """Remove each sweep of ``kept``'s kind that read another tree, and each abandoned one.

    A sweep of the same kind that read the same tree stays: a probe's variant
    of the lane's argv is kept beside the lane's own sweep, never in its place.
    """
    mine = _KEPT.fullmatch(kept.name)
    for entry in CACHE_ROOT.iterdir():
        if entry == kept or entry.is_symlink() or not entry.is_dir():
            continue
        other = _KEPT.fullmatch(entry.name)
        stale = (
            mine is not None
            and other is not None
            and other.group(1) == mine.group(1)
            and other.group(2) != mine.group(2)
        )
        if stale or (entry.name.startswith(_STAGING_PREFIX) and _abandoned(entry)):
            shutil.rmtree(entry)


def _refusal() -> Prose | None:
    """Say why today's trees cannot be swept as they stand, if they cannot."""
    for tree in CppTree:
        if not os.access(tree_binary(tree), os.X_OK):
            return Prose(f"the {tree.value} mutation tree is not built")
    if shutil.which(MULL_RUNNER) is None:
        return Prose(f"{MULL_RUNNER} is not installed")
    for tree in CppTree:
        if not built_under_config(CppLeg(tree), tree_build_dir(tree)):
            return Prose(
                f"the {tree.value} mutation tree was built under another configuration than"
                + " cpp/mull.yml gives it now; rebuild it with the lane before sweeping"
            )
    unfollowed = _reach(_loaded(), cpp_sweep_directory()).unfollowed
    if unfollowed:
        return Prose(
            f"a library a sweep loads searches {unfollowed[0]}, whose substitution the key"
            + " cannot follow, so no kept sweep could say what it read"
        )
    return None


class _Keeping(NamedTuple):
    """One sweep as it is kept: its key, how it is swept, what it leaves, how it is keyed again."""

    key: SweepKey
    sweep: Callable[[Path], Prose | None]
    present: Callable[[Path], bool]
    rekey: Callable[[], SweepKey]


def _kept(keeping: _Keeping, *, refresh: bool) -> Path | Prose:
    """Serve the sweep kept under its key, or sweep into a locked neighbour and file it there."""
    wanted = CACHE_ROOT / keeping.key
    if not refresh and keeping.present(wanted):
        return wanted
    CACHE_ROOT.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(dir=CACHE_ROOT, prefix=_STAGING_PREFIX))
    lock = os.open(staging, os.O_RDONLY | os.O_CLOEXEC)
    try:
        fcntl.flock(lock, fcntl.LOCK_EX)
        failure = keeping.sweep(staging)
        if failure is None and keeping.rekey() != keeping.key:
            failure = Prose("the trees changed while they were swept; the sweep was not kept")
        if failure is not None:
            return failure
        if wanted.is_dir():
            shutil.rmtree(wanted)
        staging.rename(wanted)
    finally:
        os.close(lock)
        shutil.rmtree(staging, ignore_errors=True)
    _forget_other_sweeps(wanted)
    return wanted


def sweep_directory(*, refresh: bool = False, variant: CppVariant = CPP_LANE) -> Path | Prose:
    """Return the directory holding a variant's sweep of today's trees, sweeping where none is."""
    refusal = _refusal()
    if refusal is not None:
        return refusal
    return _kept(
        _Keeping(
            sweep_key(variant),
            partial(_sweep_into, variant),
            partial(_reports_present, variant.trees),
            partial(sweep_key, variant),
        ),
        refresh=refresh,
    )


# The library a Go or Rust sweep's tests load, as each lane hands it to them
# through ALETHEIA_LIB; the stand-in kernels they load from beside it are the
# ones the C++ key names.
_LANE_LIBRARY = _LIBRARY_PATHS[0]

# What each lane's sweep leaves that its probe reads.
LANE_REPORT: dict[LaneKind, Path] = {"go": Path(GO_RAW_LOG), "rust": OUTCOMES}

# What a lane reads from outside the tree that decides what it reports: each
# tool of its toolchain, by where it is found, its bytes, since a tool built
# from a module's head says only that it is a development build, and what it
# says of itself; and the caller's variables the tools and the tests read. Go
# is asked for the settings that decide a build by name, since its whole
# environment also names a temporary directory that changes with each asking.
# What the toolchains keep of their own outside the tree, configuration and
# caches, is not followed, as the C++ key does not follow the runner.
_LANE_TOOLS: dict[LaneKind, tuple[_ToolQuery, ...]] = {
    "go": (
        _ToolQuery(
            "go env GOVERSION GOOS GOARCH GOAMD64 GOEXPERIMENT GOFLAGS GOTOOLCHAIN"
            + " CC CXX CGO_ENABLED CGO_CFLAGS CGO_CPPFLAGS CGO_CXXFLAGS CGO_LDFLAGS"
        ),
        _ToolQuery("gremlins --version"),
    ),
    "rust": (
        _ToolQuery("rustc -vV"),
        _ToolQuery("cargo -V"),
        _ToolQuery("cargo mutants --version"),
    ),
}
LANE_VARIABLES = re.compile(
    r"ALETHEIA_\w*|LC_\w+|LANG|GO\w*|CGO_\w+|CARGO\w*|RUST\w*|CC|CXX|CFLAGS|CXXFLAGS|LDFLAGS"
)


def _lane_runs_in() -> Path:
    """Name where a lane's sweep runs: a scratch copy under the temporary directory.

    The copy holds the tracked tree, which the tree id names, so a relative
    search path of what the tests load resolves to nothing else to key.
    """
    return Path(tempfile.gettempdir())


def _lane_loaded() -> list[Path]:
    """Name the ELF files a lane's tests load: the library, the stand-ins beside it."""
    return [REPO_ROOT / _LANE_LIBRARY, *sorted((REPO_ROOT / STAND_IN_DIR).glob("*.so"))]


def _lane_tools(kind: LaneKind) -> list[_KeyLine]:
    """Spell where each of a lane's tools is found, its bytes and its word, or that it is not."""
    lines: list[_KeyLine] = []
    for query in _LANE_TOOLS[kind]:
        argv = query.split(" ")
        found = shutil.which(argv[0])
        if found is None:
            lines.append(_KeyLine(f"{argv[0]}: not found"))
            continue
        said = subprocess.run(
            [found, *argv[1:]], cwd=REPO_ROOT / kind, capture_output=True, text=True, check=False
        )
        lines += [
            _KeyLine(f"{found}:{_digest(Path(found))}"),
            _KeyLine(f"{found} {' '.join(argv[1:])}: exit {said.returncode}"),
            _KeyLine(said.stdout),
            _KeyLine(said.stderr),
        ]
    return lines


def _lane_refusal(kind: LaneKind) -> Prose | None:
    """Say why a lane's sweep of today's tree could not be keyed, if it could not."""
    if tracked_tree(REPO_ROOT) is None:
        return Prose("git could not name the tracked tree, so no kept sweep could say what it read")
    unfollowed = _reach(_lane_loaded(), _lane_runs_in()).unfollowed
    if unfollowed:
        return Prose(
            f"a library the {kind} tests load searches {unfollowed[0]}, whose substitution the"
            + " key cannot follow, so no kept sweep could say what it read"
        )
    return None


def lane_sweep_key(kind: LaneKind) -> SweepKey:
    """Name what a lane's sweep of today's tree would read from it, and how it would run.

    The lane sweeps a scratch copy of the tracked tree, so the tree id names
    every file of the tree it reads, and the library its tests load from the
    tree, with what the loader reaches from it, is named file by file.
    """
    loaded = _lane_loaded()
    files = [
        _KeyLine(f"tree:{tracked_tree(REPO_ROOT)}"),
        *_files_lines(sorted({*loaded, *_reach(loaded, _lane_runs_in()).files})),
    ]
    variables = {
        name: value for name, value in os.environ.items() if LANE_VARIABLES.fullmatch(name)
    }
    run = [
        *_lane_tools(kind),
        *(_KeyLine(f"{name}={variables[name]}") for name in sorted(variables)),
    ]
    return SweepKey(f"{kind}-{_part(files)}-{_part(run)}")


def _lane_report_present(kind: LaneKind, directory: Path) -> bool:
    """Say whether the directory holds the report a lane's sweep leaves."""
    return (directory / LANE_REPORT[kind]).is_file()


def _lane_sweep_into(kind: LaneKind, directory: Path) -> Prose | None:
    """Run a lane's sweep of its whole package into the directory, or say what stopped it."""
    report = run_go(directory) if kind == "go" else run_rust(directory)
    if report.error is not None:
        return Prose("\n".join([report.error, *report.raw_log.splitlines()[-3:]]))
    if not _lane_report_present(kind, directory):
        return Prose(f"the {kind} sweep wrote no {LANE_REPORT[kind]}")
    return None


def lane_sweep_directory(kind: LaneKind, *, refresh: bool = False) -> Path | Prose:
    """Return the directory holding a lane's sweep of today's tree, sweeping where there is none."""
    refusal = _lane_refusal(kind)
    if refusal is not None:
        return refusal
    return _kept(
        _Keeping(
            lane_sweep_key(kind),
            partial(_lane_sweep_into, kind),
            partial(_lane_report_present, kind),
            partial(lane_sweep_key, kind),
        ),
        refresh=refresh,
    )


def main() -> ExitStatus:
    """Print the directory of a sweep of today's trees, or the reason there is none."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--refresh", action="store_true", help="sweep again where a sweep of today's trees is kept"
    )
    result = sweep_directory(refresh=cast("bool", parser.parse_args().refresh))
    if isinstance(result, Path):
        emit(str(result))
        return ExitStatus(0)
    emit(result)
    return ExitStatus(1)


if __name__ == "__main__":
    raise SystemExit(main())
