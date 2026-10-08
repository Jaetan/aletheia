# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The configuration a C++ mutation leg is built and swept under, and the stamp that says which.

The whole leg reads ``cpp/mull.yml`` itself.  A slice is given a
configuration generated from it and written inside its build tree.  Every
build tree carries a stamp of the content it was built under: nothing in the
build knows an object depends on the configuration, so the stamp is what says
which one the tree was built under.  The files a leg carries are computed
here too, a slice's configuration being ``cpp/mull.yml`` with the files of
the other slices held out.
"""

from __future__ import annotations

import hashlib
import shutil
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath
from tools.mutation_cpp_slices import (
    CPP_SLICES,
    FileRuns,
    SuiteRuns,
    partition,
    slice_config_text,
    slice_domain,
)
from tools.mutation_report import REPO_ROOT, load_spec

if TYPE_CHECKING:
    from pathlib import Path

    from tools.mutation_cpp_legs import CppLeg


def recorded_runs() -> FileRuns:
    """Read the suite runs each file's mutants cost when the weights were last taken.

    The weights the partition balances on.  They are a measurement and they
    age: a file that grows costs more than the record knows, which costs the
    balance of the slices and never their coverage, and the review that
    re-takes them is scheduled rather than triggered, because growth is
    ordinary work and nothing about it goes red.
    """
    baseline = load_spec().get("bindings", {}).get("cpp", {}).get("baseline", {})
    runs = baseline.get("runs_by_file", {})
    return {RelPath(path): SuiteRuns(float(value)) for path, value in runs.items()}


def leg_files(leg: CppLeg) -> tuple[list[RelPath], list[RelPath]]:
    """Give the files a leg carries mutants for, and the domain files it holds out.

    Computed from the domain and the recorded weights rather than read from a
    list, so a file added to the library is in the partition the moment it is
    tracked; every leg of a run computes the same partition from the same
    commit.
    """
    domain = slice_domain(REPO_ROOT, REPO_ROOT / "cpp" / "mull.yml")
    if leg.slice_no is None:
        return domain, []
    claimed = partition(domain, recorded_runs())[leg.slice_no - 1]
    return list(claimed), [path for path in domain if path not in set(claimed)]


# Where a build tree records the configuration it was built under, so one
# built under another is discarded rather than reused.
CPP_CONFIG_STAMP = ".mull-config.sha256"

# What a slice's generated configuration is written as, inside the build tree
# it configures.
CPP_GENERATED_CONFIG = "mull-config.yml"


# A configuration's text as the build and the runner read it, and the digest a
# build tree's stamp records of the one it was built under.
ConfigText = NewType("ConfigText", str)
ConfigDigest = NewType("ConfigDigest", str)


def leg_config_text(leg: CppLeg) -> ConfigText | None:
    """Spell the configuration a leg builds and sweeps under; None where it reads cpp/mull.yml."""
    if leg.slice_no is None:
        return None
    config = REPO_ROOT / "cpp" / "mull.yml"
    _, held_out = leg_files(leg)
    return ConfigText(slice_config_text(config, held_out, leg.slice_no, CPP_SLICES))


def _config_digest(text: ConfigText) -> ConfigDigest:
    """Digest a configuration the way a build tree's stamp records it."""
    return ConfigDigest(hashlib.sha256(text.encode("utf-8")).hexdigest())


def leg_config_path(leg: CppLeg, build_dir: Path) -> Path:
    """Name the configuration file the leg builds and sweeps under, writing nothing.

    The whole leg reads ``cpp/mull.yml`` itself; a slice reads the one
    ``leg_config`` writes inside its build tree.
    """
    if leg.slice_no is None:
        return REPO_ROOT / "cpp" / "mull.yml"
    return build_dir / CPP_GENERATED_CONFIG


def _stamped_text(leg: CppLeg) -> ConfigText:
    """Spell what a leg's stamp records: its generated configuration, or cpp/mull.yml itself."""
    text = leg_config_text(leg)
    if text is not None:
        return text
    return ConfigText((REPO_ROOT / "cpp" / "mull.yml").read_text(encoding="utf-8"))


def built_under_config(leg: CppLeg, build_dir: Path) -> bool:
    """Say whether a build tree was built under the configuration it would be given now.

    Its stamp has to name the content it would read today, whether the leg
    reads cpp/mull.yml itself or a configuration generated from it.
    """
    stamp = build_dir / CPP_CONFIG_STAMP
    return stamp.is_file() and stamp.read_text(encoding="utf-8") == _config_digest(
        _stamped_text(leg)
    )


def leg_config(leg: CppLeg, build_dir: Path) -> Path:
    """Put the configuration the leg builds and sweeps under in place, and name it.

    The whole leg reads the configuration ``cpp/mull.yml`` states.  A slice
    gets one written inside its build tree: that configuration with the files
    of the other slices held out, so the build carries this slice's mutants
    alone.

    Every build tree, whichever configuration it reads, is stamped with the
    content it is built under, and one whose objects were built under
    different content is removed first.
    Nothing in the build knows an object depends on this file: CMake compiles
    a source when the source is newer, the configuration is not a source, and
    a build tree left from another slice would answer a rebuild by doing
    nothing and sweeping the mutants of that other slice.  Measured: with the
    build tree kept, holding a file out of the other slices changed the
    configuration and the census did not move.  The stamp is the content's
    digest and not its time, so an identical configuration keeps the build
    tree it built, and the compiler cache turns the rebuild after a real
    change into cache reads.
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
