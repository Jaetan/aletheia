# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.docs_arms.ffi_symbols``: the building guide names only exported C symbols.

Each test plants a tree holding the guide and the shim, all tracked, and calls the
arm the way the documentation gate does.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from _planted_tree import run_planted

from tools.docs_arms.ffi_symbols import GUIDE, SHIM, findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_SHIM_TEXT = Prose(
    "module AletheiaFFI where\n"
    + "foreign export ccall aletheia_process :: IO ()\n"
    + "foreign export ccall aletheia_send_frame :: IO ()\n"
)
_EMPTY_SHIM = Prose("module AletheiaFFI where\n")
_CLEAN_GUIDE = Prose(
    "# Building\n\n"
    + "The shim exports `aletheia_process` for JSON commands and `aletheia_send_frame`\n"
    + "for binary frames.\n"
)
_PLANTED_GUIDE = Prose(_CLEAN_GUIDE + "\nA name mismatch shows up as `aletheia_process_json`.\n")
_SILENT_GUIDE = Prose("# Building\n\nNo entry point is named here.\n")


def _repo(tmp_path: Path, guide: Prose | None, shim: Prose | None) -> Path:
    """Return a planted tree holding the given guide and shim, each omitted when None."""
    repo = tmp_path / "repo"
    repo.mkdir()
    if guide is not None:
        (repo / GUIDE).parent.mkdir(parents=True)
        _ = (repo / GUIDE).write_text(guide, encoding="utf-8")
    if shim is not None:
        (repo / SHIM).parent.mkdir(parents=True)
        _ = (repo / SHIM).write_text(shim, encoding="utf-8")
    _ = (repo / "README.md").write_text("# Readme\n", encoding="utf-8")
    return repo.resolve()


def _run(repo: Path) -> list[Prose]:
    """Call the arm over ``repo`` with the arguments the documentation gate passes."""
    return run_planted(findings, repo)


def test_clean_guide_has_no_finding(tmp_path: Path) -> None:
    """A guide naming only exported symbols passes."""
    assert _run(_repo(tmp_path, _CLEAN_GUIDE, _SHIM_TEXT)) == list[Prose]()


def test_unexported_symbol_is_a_finding(tmp_path: Path) -> None:
    """A guide naming a symbol the shim does not export is reported, naming the guide."""
    assert _run(_repo(tmp_path, _PLANTED_GUIDE, _SHIM_TEXT)) == [
        Prose(f"{GUIDE}: names aletheia_process_json, which {SHIM} does not export")
    ]


def test_a_token_inside_a_longer_word_is_not_a_symbol(tmp_path: Path) -> None:
    """``libaletheia_ffi.so`` names a library file, not a symbol ``aletheia_ffi``."""
    guide = Prose(_CLEAN_GUIDE + "\nThe build links `libaletheia_ffi.so`.\n")
    assert _run(_repo(tmp_path, guide, _SHIM_TEXT)) == list[Prose]()


def test_a_commented_out_export_is_not_exported(tmp_path: Path) -> None:
    """An export the shim comments out is no C entry point, so a guide naming it is reported."""
    shim = Prose(_SHIM_TEXT + "-- foreign export ccall aletheia_old :: IO ()\n")
    guide = Prose(_CLEAN_GUIDE + "\nThe old entry point was `aletheia_old`.\n")
    assert _run(_repo(tmp_path, guide, shim)) == [
        Prose(f"{GUIDE}: names aletheia_old, which {SHIM} does not export")
    ]


def test_guide_naming_no_symbol_is_a_finding(tmp_path: Path) -> None:
    """A guide naming no symbol gives the arm nothing to hold, which it reports."""
    assert _run(_repo(tmp_path, _SILENT_GUIDE, _SHIM_TEXT)) == [
        Prose(f"{GUIDE}: names no aletheia_<name> symbol; the arm has nothing to hold")
    ]


def test_untracked_guide_is_a_finding(tmp_path: Path) -> None:
    """A tree without the guide is reported rather than passed."""
    assert _run(_repo(tmp_path, None, _SHIM_TEXT)) == [
        Prose(f"{GUIDE}: not tracked, so the arm has no guide to read")
    ]


def test_untracked_shim_is_a_finding(tmp_path: Path) -> None:
    """A tree without the shim is reported rather than passed."""
    assert _run(_repo(tmp_path, _CLEAN_GUIDE, None)) == [
        Prose(f"{SHIM}: not tracked, so the arm has no exports to check the guide against")
    ]


def test_shim_exporting_nothing_is_a_finding(tmp_path: Path) -> None:
    """A shim with no foreign export cannot hold any name, which is reported."""
    assert _run(_repo(tmp_path, _CLEAN_GUIDE, _EMPTY_SHIM)) == [
        Prose(f"{SHIM}: has no foreign export ccall line; the arm has nothing to hold")
    ]


def test_unexported_symbols_are_reported_in_name_order(tmp_path: Path) -> None:
    """Several symbols the shim does not export are reported one each, in name order."""
    guide = Prose(
        _CLEAN_GUIDE
        + "\nRetired: `aletheia_delta`, `aletheia_alpha`, `aletheia_charlie`, `aletheia_bravo`.\n"
    )
    assert _run(_repo(tmp_path, guide, _SHIM_TEXT)) == [
        Prose(f"{GUIDE}: names aletheia_{name}, which {SHIM} does not export")
        for name in ("alpha", "bravo", "charlie", "delta")
    ]


def test_a_shim_byte_that_is_not_utf8_does_not_stop_the_read(tmp_path: Path) -> None:
    """A non-UTF-8 shim byte ends the name it sits in, not vanishing; exports after it are read."""
    guide = Prose(_CLEAN_GUIDE + "\nThe cut name `aletheia_proc` is exported.\n")
    repo = _repo(tmp_path, guide, _EMPTY_SHIM)
    _ = (repo / SHIM).write_bytes(
        b"module AletheiaFFI where\n"
        + b"foreign export ccall aletheia_proc\xe9ess :: IO ()\n"
        + b"foreign export ccall aletheia_send_frame :: IO ()\n"
    )
    assert _run(repo) == [Prose(f"{GUIDE}: names aletheia_process, which {SHIM} does not export")]


def test_a_tracked_guide_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A guide git tracks and the work tree lacks is named as unread, never as untracked."""
    repo = _repo(tmp_path, None, _SHIM_TEXT)
    assert run_planted(findings, repo, absent={GUIDE}) == [
        Prose(f"{GUIDE}: could not be read, so what it says is unchecked"),
        Prose(f"{GUIDE}: could not be read, so the arm has no guide to read"),
    ]


def test_a_tracked_shim_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A shim git tracks and the work tree lacks is a finding, not an error."""
    repo = _repo(tmp_path, _CLEAN_GUIDE, None)
    assert run_planted(findings, repo, absent={SHIM}) == [
        Prose(f"{SHIM}: could not be read, so the arm has no exports to check the guide against")
    ]
