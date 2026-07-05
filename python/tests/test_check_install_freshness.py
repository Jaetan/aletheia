# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_install_freshness`` — the deployed-artifact rot gate.

Hermetic tmp-tree runs of ``main`` in both polarities per artifact class,
parameterized over the single differentiator (matching vs diverged library
bytes; present vs absent install config), per
[[feedback_test_guard_parameterise_over_diff]].  The DI seam is the tool's
own ``--repo-root`` / ``--prefix`` flags — no monkeypatching.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tools.check_install_freshness import BUILD_SO, find_problems, main

# The real built kernel — a genuine ELF carrying a GNU build-id note. Present
# after `cabal run shake -- build`; absent on a fresh clone (skip the build-id
# branch then; the sha256 branch is covered regardless).
_REAL_SO = Path(__file__).resolve().parents[2] / BUILD_SO

FRESH_BYTES = b"kernel-image-v2"
STALE_BYTES = b"kernel-image-v1"


def _write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(payload)


def _make_repo(tmp_path: Path, *, with_build: bool = True) -> Path:
    repo = tmp_path / "repo"
    if with_build:
        _write(repo / "build" / "libaletheia-ffi.so", FRESH_BYTES)
    else:
        repo.mkdir(parents=True, exist_ok=True)
    return repo


def _make_prefix(tmp_path: Path, payload: bytes, *, with_config: bool = True) -> Path:
    prefix = tmp_path / "prefix"
    _write(prefix / "lib" / "aletheia" / "libaletheia-ffi.so", payload)
    if with_config:
        _write(
            prefix
            / "lib"
            / "aletheia"
            / "venv"
            / "lib"
            / "python3.14"
            / "site-packages"
            / "aletheia"
            / "_install_config.py",
            b"LIBRARY_PATH = ...\n",
        )
    return prefix


def _run(repo: Path, prefix: Path) -> int:
    return main(["--repo-root", str(repo), "--prefix", str(prefix)])


def test_no_build_artifact_is_skip_pass(tmp_path: Path) -> None:
    """A tree without build output (fresh clone, CI) has nothing to rot."""
    repo = _make_repo(tmp_path, with_build=False)
    assert _run(repo, tmp_path / "prefix") == 0


def test_no_deployed_artifacts_pass(tmp_path: Path) -> None:
    """Build output alone (never ran dist/install) is fresh by definition."""
    repo = _make_repo(tmp_path)
    assert _run(repo, tmp_path / "prefix") == 0


@pytest.mark.parametrize(
    ("dist_bytes", "expected_exit"),
    [(FRESH_BYTES, 0), (STALE_BYTES, 1)],
    ids=["matching-dist-passes", "diverged-dist-fails"],
)
def test_dist_freshness(tmp_path: Path, dist_bytes: bytes, expected_exit: int) -> None:
    """dist/ passes iff its library bytes match build/'s."""
    repo = _make_repo(tmp_path)
    _write(repo / "dist" / "aletheia" / "lib" / "libaletheia-ffi.so", dist_bytes)
    assert _run(repo, tmp_path / "prefix") == expected_exit


@pytest.mark.parametrize(
    ("deploy_bytes", "expected_exit"),
    [(FRESH_BYTES, 0), (STALE_BYTES, 1)],
    ids=["matching-install-passes", "diverged-install-fails"],
)
def test_install_freshness(tmp_path: Path, deploy_bytes: bytes, expected_exit: int) -> None:
    """The install prefix passes iff its library bytes match build/'s."""
    repo = _make_repo(tmp_path)
    prefix = _make_prefix(tmp_path, deploy_bytes)
    assert _run(repo, prefix) == expected_exit


@pytest.mark.parametrize(
    ("with_config", "expected_exit"),
    [(True, 0), (False, 1)],
    ids=["completed-install-passes", "partial-install-fails"],
)
def test_partial_install_detection(
    tmp_path: Path, *, with_config: bool, expected_exit: int
) -> None:
    """A deployed library without ``_install_config.py`` is a partial install.

    This is exactly the state the pre-fix Shake quoting bug left behind:
    libraries copied, package installed, config never written.
    """
    repo = _make_repo(tmp_path)
    prefix = _make_prefix(tmp_path, FRESH_BYTES, with_config=with_config)
    assert _run(repo, prefix) == expected_exit


def _write_receipt(repo: Path, prefix: Path, library: Path, config: Path) -> None:
    _write(
        repo / ".install-receipt",
        f"{prefix}\n{library}\n{config}\n".encode(),
    )


@pytest.mark.parametrize(
    ("deploy_bytes", "expected_exit"),
    [(FRESH_BYTES, 0), (STALE_BYTES, 1)],
    ids=["fresh-receipt-install-passes", "stale-receipt-install-fails"],
)
def test_receipt_freshness(tmp_path: Path, deploy_bytes: bytes, expected_exit: int) -> None:
    """With a receipt, the RECORDED library location is what gets verified."""
    repo = _make_repo(tmp_path)
    custom = tmp_path / "custom-prefix" / "lib" / "aletheia"
    _write(custom / "libaletheia-ffi.so", deploy_bytes)
    config = custom / "venv-site" / "_install_config.py"
    _write(config, b"LIBRARY_PATH = ...\n")
    _write_receipt(repo, tmp_path / "custom-prefix", custom / "libaletheia-ffi.so", config)
    assert _run(repo, tmp_path / "unused-default-prefix") == expected_exit


def test_receipt_supersedes_default_prefix_probe(tmp_path: Path) -> None:
    """A fresh receipted install passes even when the default prefix holds junk.

    This is the custom-``PREFIX`` scenario the receipt exists for: the gate
    must trust the recorded location, not a guessed one.
    """
    repo = _make_repo(tmp_path)
    stale_default = _make_prefix(tmp_path, STALE_BYTES)
    custom = tmp_path / "elsewhere" / "lib" / "aletheia"
    _write(custom / "libaletheia-ffi.so", FRESH_BYTES)
    config = custom / "venv-site" / "_install_config.py"
    _write(config, b"LIBRARY_PATH = ...\n")
    _write_receipt(repo, tmp_path / "elsewhere", custom / "libaletheia-ffi.so", config)
    assert _run(repo, stale_default) == 0


def test_receipt_with_missing_library_fails(tmp_path: Path) -> None:
    """A receipt pointing at a removed install must be loud, not a silent skip."""
    repo = _make_repo(tmp_path)
    gone = tmp_path / "gone" / "libaletheia-ffi.so"
    _write_receipt(repo, tmp_path / "gone", gone, gone.parent / "_install_config.py")
    assert _run(repo, tmp_path / "unused-default-prefix") == 1


def test_real_elf_matches_by_build_id_and_mixed_pair_falls_back(tmp_path: Path) -> None:
    """A real-ELF dist copy matches by build-id; a mixed pair decides jointly.

    Uses the built ``.so`` (a genuine ELF with a GNU build-id note) as
    ``build/``. A ``dist/`` copy of it compares equal via the build-id
    branch → fresh. Replacing that ``dist/`` with a NON-ELF file leaves
    only ``build/`` carrying a build-id: the comparison must fall back to
    SHA-256 (never build-id-vs-hash, which could never match) and report
    the copy stale — the exact case the per-file identity form got wrong.
    The non-ELF fixtures elsewhere in this file already cover the pure
    SHA-256 (neither-side-ELF) path.
    """
    if not _REAL_SO.is_file():
        pytest.skip(f"{_REAL_SO} not built — run 'cabal run shake -- build' to exercise this")
    real_bytes = _REAL_SO.read_bytes()
    repo = tmp_path / "repo"
    _write(repo / "build" / "libaletheia-ffi.so", real_bytes)
    dist_so = repo / "dist" / "aletheia" / "lib" / "libaletheia-ffi.so"
    unused_prefix = tmp_path / "unused-prefix"

    # dist/ is a byte-copy of the real ELF → same build-id → fresh.
    _write(dist_so, real_bytes)
    assert not find_problems(repo, unused_prefix)

    # dist/ is now a non-ELF file: only build/ has a build-id, so the
    # joint decision falls back to SHA-256 → different → stale (no crash).
    _write(dist_so, b"not an elf")
    assert any("stale dist/" in problem for problem in find_problems(repo, unused_prefix))
