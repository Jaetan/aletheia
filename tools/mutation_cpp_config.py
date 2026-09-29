# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The configuration a C++ mutation leg is built and swept under, and the stamp that says which.

A whole tree that keeps every mutator reads ``cpp/mull.yml`` itself.  Any
other leg, a tree that drops mutators or one slice of a tree, is given a
configuration generated from it and written inside its build tree.  Every
tree carries a stamp of the content it was built under: nothing in the build
knows an object depends on the configuration, so the stamp is what says which
one a tree was built under.  The files a leg carries are computed here too, a
slice's configuration being the tree's with the files of the other slices
held out.
"""

from __future__ import annotations

import hashlib
import shutil
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath
from tools.mutation_cpp_slices import (
    CPP_SLICES,
    partition,
    slice_config_text,
    slice_domain,
    tree_config_text,
)
from tools.mutation_report import REPO_ROOT, load_spec

if TYPE_CHECKING:
    from pathlib import Path

    from tools.mutation_cpp_legs import CppLeg

# How many mutants the census recorded a file carrying.
MutantCount = NewType("MutantCount", int)


def recorded_mutant_counts() -> dict[RelPath, MutantCount]:
    """Read the mutants each file carried when the census was last taken.

    The weights the partition balances on.  They are a measurement and they
    age: a file that grows carries more mutants than the record knows, which
    costs the balance of the slices and never their coverage, and the review
    that re-takes them is scheduled rather than triggered, because growth is
    ordinary work and nothing about it goes red.
    """
    baseline = load_spec().get("bindings", {}).get("cpp", {}).get("baseline", {})
    counts = baseline.get("mutants_by_file", {})
    return {RelPath(path): MutantCount(int(count)) for path, count in counts.items()}


def leg_files(leg: CppLeg) -> tuple[list[RelPath], list[RelPath]]:
    """Give the files a leg carries mutants for, and the domain files it holds out.

    Computed from the tree and the recorded counts rather than read from a
    list, so a file added to the library is in the partition the moment it is
    tracked; every leg of a run computes the same partition from the same
    commit.
    """
    domain = slice_domain(REPO_ROOT, REPO_ROOT / "cpp" / "mull.yml")
    if leg.slice_no is None:
        return domain, []
    claimed = partition(domain, recorded_mutant_counts())[leg.slice_no - 1]
    return list(claimed), [path for path in domain if path not in set(claimed)]


# Where a tree records the configuration it was built under, so a tree built
# under another is discarded rather than reused.
CPP_CONFIG_STAMP = ".mull-config.sha256"

# What a generated configuration is written as, inside the tree it configures:
# a slice's, a tree's narrowed mutator set, or both at once.
CPP_GENERATED_CONFIG = "mull-config.yml"


# A configuration's text as the build and the runner read it, and the digest a
# tree's stamp records of the one it was built under.
ConfigText = NewType("ConfigText", str)
ConfigDigest = NewType("ConfigDigest", str)


def _reads_tree_config(leg: CppLeg) -> bool:
    """Say whether a leg reads ``cpp/mull.yml`` itself: a whole tree that keeps every mutator."""
    return leg.slice_no is None and not leg.tree.dropped_mutators


def leg_config_text(leg: CppLeg) -> ConfigText | None:
    """Spell the configuration a leg builds and sweeps under; None where it reads cpp/mull.yml."""
    if _reads_tree_config(leg):
        return None
    config = REPO_ROOT / "cpp" / "mull.yml"
    dropped = leg.tree.dropped_mutators
    if leg.slice_no is None:
        return ConfigText(tree_config_text(config, dropped))
    _, held_out = leg_files(leg)
    return ConfigText(slice_config_text(config, held_out, leg.slice_no, CPP_SLICES, dropped))


def _config_digest(text: ConfigText) -> ConfigDigest:
    """Digest a configuration the way a tree's stamp records it."""
    return ConfigDigest(hashlib.sha256(text.encode("utf-8")).hexdigest())


def leg_config_path(leg: CppLeg, build_dir: Path) -> Path:
    """Name the configuration file the leg builds and sweeps under, writing nothing.

    A whole tree that keeps every mutator reads ``cpp/mull.yml`` itself; every
    other leg reads the one ``leg_config`` writes inside its build tree.
    """
    if _reads_tree_config(leg):
        return REPO_ROOT / "cpp" / "mull.yml"
    return build_dir / CPP_GENERATED_CONFIG


def _stamped_text(leg: CppLeg) -> ConfigText:
    """Spell what a leg's stamp records: its generated configuration, or cpp/mull.yml itself."""
    text = leg_config_text(leg)
    if text is not None:
        return text
    return ConfigText((REPO_ROOT / "cpp" / "mull.yml").read_text(encoding="utf-8"))


def built_under_config(leg: CppLeg, build_dir: Path) -> bool:
    """Say whether a tree was built under the configuration it would be given now.

    Its stamp has to name the content it would read today, whether the tree
    reads cpp/mull.yml itself or a configuration generated from it.
    """
    stamp = build_dir / CPP_CONFIG_STAMP
    return stamp.is_file() and stamp.read_text(encoding="utf-8") == _config_digest(
        _stamped_text(leg)
    )


def leg_config(leg: CppLeg, build_dir: Path) -> Path:
    """Put the configuration the leg builds and sweeps under in place, and name it.

    A whole tree that keeps every mutator reads the configuration the tree
    itself states.  Any other leg gets one written inside its build tree: that
    configuration without the mutators the tree drops and, for a slice, with
    the files of the other slices held out, so the build carries this slice's
    mutants alone.

    Every tree, whichever configuration it reads, is stamped with the content
    it is built under, and a tree whose objects were built under different
    content is removed first.
    Nothing in the build knows an object depends on this file: CMake compiles
    a source when the source is newer, the configuration is not a source, and
    a tree left from another slice would answer a rebuild by doing nothing and
    sweeping the mutants of that other slice.  Measured: with the tree kept,
    holding a file out of the other slices changed the configuration and the
    census did not move.  The stamp is the content's digest and not its time,
    so an identical configuration keeps the tree it built, and the compiler
    cache turns the rebuild after a real change into cache reads.
    """
    written = leg_config_path(leg, build_dir)
    if build_dir.is_dir() and not built_under_config(leg, build_dir):
        shutil.rmtree(build_dir)
    build_dir.mkdir(parents=True, exist_ok=True)
    text = leg_config_text(leg)
    if text is not None:
        _ = written.write_text(text, encoding="utf-8")
    stamp = _config_digest(_stamped_text(leg))
    _ = (build_dir / CPP_CONFIG_STAMP).write_text(stamp, encoding="utf-8")
    return written
