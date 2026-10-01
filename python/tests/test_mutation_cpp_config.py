# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The configuration a mutation tree is built and swept under, and the stamp that says which.

A whole tree keeping every mutator reads the tree's own configuration; every
other leg reads one generated from it and written inside its build tree.
Every tree's stamp records the digest of the content it was built under, and
a tree whose stamp names other content was built under another configuration:
the lane removes it before building, and the sweep cache refuses to sweep it.
The tree is faked under a scratch root.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from tools import mutation_cpp_config
from tools._common import RelPath
from tools.mutation_cpp_config import (
    CPP_CONFIG_STAMP,
    CPP_GENERATED_CONFIG,
    built_under_config,
    leg_config,
    leg_config_path,
)
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_cpp_slices import CPP_SLICES, SuiteRuns, held_out_patterns, hold_out_pattern

if TYPE_CHECKING:
    from pathlib import Path

    from tools.mutation_cpp_slices import TreeRuns

# The tree's configuration: a mutator every tree keeps, and a call mutator the
# address tree drops.
_MULL_CONFIG = "mutators:\n  - cxx_add_to_sub\n  - cxx_remove_void_call\nexcludePaths: []\n"
_ADDRESS = CppLeg(CppTree.ADDRESS)


@pytest.fixture(name="root")
def _root(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Fake the repository under a scratch root, holding the tree's configuration."""
    monkeypatch.setattr(mutation_cpp_config, "REPO_ROOT", tmp_path)
    config = tmp_path / "cpp" / "mull.yml"
    config.parent.mkdir(parents=True)
    _ = config.write_text(_MULL_CONFIG, encoding="utf-8")
    return tmp_path


def _build_dir(root: Path, leg: CppLeg) -> Path:
    """Name the directory a leg is built in under the fake root."""
    return root / "cpp" / leg.directory


@pytest.mark.parametrize("tree", [CppTree.LEAK, CppTree.PLAIN], ids=str)
def test_a_whole_tree_keeping_every_mutator_reads_the_trees_configuration(
    root: Path, tree: CppTree
) -> None:
    """Nothing is generated for it, and its stamp names the tree's configuration."""
    leg = CppLeg(tree)
    build = _build_dir(root, leg)
    assert not built_under_config(leg, build)
    assert leg_config(leg, build) == root / "cpp" / "mull.yml"
    assert leg_config_path(leg, build) == root / "cpp" / "mull.yml"
    assert not (build / CPP_GENERATED_CONFIG).exists()
    assert (build / CPP_CONFIG_STAMP).is_file()
    assert built_under_config(leg, build)


def test_a_tree_dropping_mutators_is_built_under_its_own_configuration(root: Path) -> None:
    """The generated configuration lacks the dropped mutators, and the stamp names it."""
    build = _build_dir(root, _ADDRESS)
    assert not built_under_config(_ADDRESS, build)
    written = leg_config(_ADDRESS, build)
    assert written == build / CPP_GENERATED_CONFIG == leg_config_path(_ADDRESS, build)
    text = written.read_text(encoding="utf-8")
    assert "cxx_add_to_sub" in text
    assert all(mutator not in text for mutator in CppTree.ADDRESS.dropped_mutators)
    assert built_under_config(_ADDRESS, build)


@pytest.mark.parametrize("tree", list(CppTree), ids=str)
def test_a_changed_configuration_makes_the_tree_stale_and_the_lane_rebuilds_it(
    root: Path, tree: CppTree
) -> None:
    """A tree built under other content is removed before the lane writes the new configuration."""
    leg = CppLeg(tree)
    build = _build_dir(root, leg)
    _ = leg_config(leg, build)
    built = build / "unit_tests"
    _ = built.write_bytes(b"built under the first configuration")
    _ = (root / "cpp" / "mull.yml").write_text(_MULL_CONFIG + "timeout: 1000\n", encoding="utf-8")
    assert not built_under_config(leg, build)
    _ = leg_config(leg, build)
    assert not built.exists()
    assert built_under_config(leg, build)


@pytest.mark.parametrize("tree", list(CppTree), ids=str)
def test_an_unchanged_configuration_keeps_the_tree(root: Path, tree: CppTree) -> None:
    """The stamp is the content's digest, so the same configuration again keeps what it built."""
    leg = CppLeg(tree)
    build = _build_dir(root, leg)
    _ = leg_config(leg, build)
    built = build / "unit_tests"
    _ = built.write_bytes(b"built")
    _ = leg_config(leg, build)
    assert built.is_file()


@pytest.mark.parametrize("tree", [CppTree.PLAIN, CppTree.ADDRESS], ids=str)
def test_a_slice_holds_out_the_files_the_other_slices_claim(
    root: Path, monkeypatch: pytest.MonkeyPatch, tree: CppTree
) -> None:
    """A slice's configuration adds the files it does not claim to the tree's hold-outs.

    A slice of a tree that drops mutators drops them too.
    """
    held = RelPath("cpp/src/held.cpp")

    def files(_leg: CppLeg) -> tuple[list[RelPath], list[RelPath]]:
        return [RelPath("cpp/src/claimed.cpp")], [held]

    monkeypatch.setattr(mutation_cpp_config, "leg_files", files)
    leg = CppLeg(tree, 1)
    build = _build_dir(root, leg)
    written = leg_config(leg, build)
    assert written == build / CPP_GENERATED_CONFIG
    assert hold_out_pattern(held) in held_out_patterns(written)
    text = written.read_text(encoding="utf-8")
    assert all(mutator not in text for mutator in tree.dropped_mutators)
    assert built_under_config(leg, build)


def test_each_tree_reads_its_own_recorded_runs(monkeypatch: pytest.MonkeyPatch) -> None:
    """The weights a tree's slices are cut on are the figures recorded for that tree alone."""
    leak = {RelPath("cpp/src/a.cpp"): SuiteRuns(3.5), RelPath("cpp/src/b.cpp"): SuiteRuns(5.0)}
    plain = {RelPath("cpp/src/a.cpp"): SuiteRuns(9.0)}
    spec = {"bindings": {"cpp": {"baseline": {"runs_by_file": {"leak": leak, "plain": plain}}}}}
    monkeypatch.setattr(mutation_cpp_config, "load_spec", lambda: spec)
    assert mutation_cpp_config.recorded_runs(CppTree.LEAK) == leak
    assert mutation_cpp_config.recorded_runs(CppTree.PLAIN) == plain
    assert mutation_cpp_config.recorded_runs(CppTree.ADDRESS) == {}


# A domain of files, each weighing one suite run more than the last.
_DOMAIN = [RelPath(f"cpp/src/file_{index}.cpp") for index in range(7)]


def test_the_slices_partition_the_domain(monkeypatch: pytest.MonkeyPatch) -> None:
    """A slice holds out what it does not claim, and together the slices claim the domain once."""

    def domain(_root: Path, _config: Path) -> list[RelPath]:
        return list(_DOMAIN)

    monkeypatch.setattr(mutation_cpp_config, "slice_domain", domain)
    weights: TreeRuns = {path: SuiteRuns(index + 1) for index, path in enumerate(_DOMAIN)}

    def recorded(_tree: CppTree) -> TreeRuns:
        return weights

    monkeypatch.setattr(mutation_cpp_config, "recorded_runs", recorded)
    assert mutation_cpp_config.leg_files(CppLeg(CppTree.PLAIN)) == (_DOMAIN, [])
    claimed_by_slice: list[list[RelPath]] = []
    for number in range(1, CPP_SLICES + 1):
        claimed, held = mutation_cpp_config.leg_files(CppLeg(CppTree.PLAIN, number))
        assert sorted(claimed + held) == sorted(_DOMAIN)
        assert not set(claimed) & set(held)
        claimed_by_slice.append(claimed)
    assert sorted(path for claimed in claimed_by_slice for path in claimed) == sorted(_DOMAIN)
    # Cut on the weights: the 28 runs fall 10, 9 and 9, where a cut on names gives 12, 7 and 9.
    loads = [sum(weights[path] for path in claimed) for claimed in claimed_by_slice]
    assert sorted(loads) == [9, 9, 10]
