# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The configuration a mutation leg is built and swept under, and the stamp that says which.

The whole tree reads ``cpp/mull.yml`` itself; a slice reads one generated
from it and written inside its build tree.  Every build tree's stamp records
the digest of the content it was built under, and one whose stamp names other
content was built under another configuration: the lane removes it before
building.  The repository is faked under a scratch root.
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
from tools.mutation_cpp_legs import CppLeg
from tools.mutation_cpp_slices import CPP_SLICES, SuiteRuns, held_out_patterns, hold_out_pattern

if TYPE_CHECKING:
    from pathlib import Path

    from tools.mutation_cpp_slices import FileRuns

# The tree's configuration: two mutators and no hold-out.
_MULL_CONFIG = "mutators:\n  - cxx_add_to_sub\n  - cxx_remove_void_call\nexcludePaths: []\n"


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


def _no_files(_leg: CppLeg) -> tuple[list[RelPath], list[RelPath]]:
    """Stand in for the partition over the fake root, which tracks no file: nothing claimed."""
    return [], []


def test_the_whole_tree_reads_the_trees_configuration(root: Path) -> None:
    """Nothing is generated for it, and its stamp names the tree's configuration."""
    leg = CppLeg()
    build = _build_dir(root, leg)
    assert not built_under_config(leg, build)
    assert leg_config(leg, build) == root / "cpp" / "mull.yml"
    assert leg_config_path(leg, build) == root / "cpp" / "mull.yml"
    assert not (build / CPP_GENERATED_CONFIG).exists()
    assert (build / CPP_CONFIG_STAMP).is_file()
    assert built_under_config(leg, build)


@pytest.mark.parametrize("leg", [CppLeg(), CppLeg(1)], ids=str)
def test_a_changed_configuration_makes_the_tree_stale_and_the_lane_rebuilds_it(
    root: Path, monkeypatch: pytest.MonkeyPatch, leg: CppLeg
) -> None:
    """A tree built under other content is removed before the lane writes the new configuration."""
    monkeypatch.setattr(mutation_cpp_config, "leg_files", _no_files)
    build = _build_dir(root, leg)
    _ = leg_config(leg, build)
    built = build / "unit_tests"
    _ = built.write_bytes(b"built under the first configuration")
    _ = (root / "cpp" / "mull.yml").write_text(_MULL_CONFIG + "timeout: 1000\n", encoding="utf-8")
    assert not built_under_config(leg, build)
    _ = leg_config(leg, build)
    assert not built.exists()
    assert built_under_config(leg, build)


@pytest.mark.parametrize("leg", [CppLeg(), CppLeg(1)], ids=str)
def test_an_unchanged_configuration_keeps_the_tree(
    root: Path, monkeypatch: pytest.MonkeyPatch, leg: CppLeg
) -> None:
    """The stamp is the content's digest, so the same configuration again keeps what it built."""
    monkeypatch.setattr(mutation_cpp_config, "leg_files", _no_files)
    build = _build_dir(root, leg)
    _ = leg_config(leg, build)
    built = build / "unit_tests"
    _ = built.write_bytes(b"built")
    _ = leg_config(leg, build)
    assert built.is_file()


def test_a_slice_holds_out_the_files_the_other_slices_claim(
    root: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A slice's configuration adds the files it does not claim to the tree's hold-outs.

    The mutators stay the tree's: nothing a slice reads is dropped.
    """
    held = RelPath("cpp/src/held.cpp")

    def files(_leg: CppLeg) -> tuple[list[RelPath], list[RelPath]]:
        return [RelPath("cpp/src/claimed.cpp")], [held]

    monkeypatch.setattr(mutation_cpp_config, "leg_files", files)
    leg = CppLeg(1)
    build = _build_dir(root, leg)
    written = leg_config(leg, build)
    assert written == build / CPP_GENERATED_CONFIG == leg_config_path(leg, build)
    assert hold_out_pattern(held) in held_out_patterns(written)
    text = written.read_text(encoding="utf-8")
    assert "cxx_add_to_sub" in text
    assert "cxx_remove_void_call" in text
    assert built_under_config(leg, build)


def test_the_recorded_runs_are_read_flat(monkeypatch: pytest.MonkeyPatch) -> None:
    """The weights the slices are cut on are the record's one mapping of file to suite runs."""
    runs = {RelPath("cpp/src/a.cpp"): SuiteRuns(3.5), RelPath("cpp/src/b.cpp"): SuiteRuns(5.0)}
    spec = {"bindings": {"cpp": {"baseline": {"runs_by_file": runs}}}}
    monkeypatch.setattr(mutation_cpp_config, "load_spec", lambda: spec)
    assert mutation_cpp_config.recorded_runs() == runs


# A domain of files, each weighing one suite run more than the last.
_DOMAIN = [RelPath(f"cpp/src/file_{index}.cpp") for index in range(7)]


def test_the_slices_partition_the_domain(monkeypatch: pytest.MonkeyPatch) -> None:
    """A slice holds out what it does not claim, and together the slices claim the domain once."""

    def domain(_root: Path, _config: Path) -> list[RelPath]:
        return list(_DOMAIN)

    monkeypatch.setattr(mutation_cpp_config, "slice_domain", domain)
    weights: FileRuns = {path: SuiteRuns(index + 1) for index, path in enumerate(_DOMAIN)}

    def recorded() -> FileRuns:
        return weights

    monkeypatch.setattr(mutation_cpp_config, "recorded_runs", recorded)
    assert mutation_cpp_config.leg_files(CppLeg()) == (_DOMAIN, [])
    claimed_by_slice: list[list[RelPath]] = []
    for number in range(1, CPP_SLICES + 1):
        claimed, held = mutation_cpp_config.leg_files(CppLeg(number))
        assert sorted(claimed + held) == sorted(_DOMAIN)
        assert not set(claimed) & set(held)
        claimed_by_slice.append(claimed)
    assert sorted(path for claimed in claimed_by_slice for path in claimed) == sorted(_DOMAIN)
    # Cut on the weights: the 28 runs fall 10, 9 and 9, where a cut on names gives 12, 7 and 9.
    loads = [sum(weights[path] for path in claimed) for claimed in claimed_by_slice]
    assert sorted(loads) == [9, 9, 10]
