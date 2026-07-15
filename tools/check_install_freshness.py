# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Freshness gate for locally deployed kernel artifacts.

Two deployment surfaces copy ``build/libaletheia-ffi.so`` out of the tree
and then rot silently when the tree moves on:

* ``dist/`` — the release-packaging output of ``cabal run shake -- dist``
  (gitignored; wiped and repacked per release).  After v2.0.0 it sat for
  weeks holding a June kernel while the tree advanced.
* the local install — populated by ``cabal run shake -- install``.  Until
  the Shake quoting fix that ships with this gate, EVERY install died
  after the copy steps but before writing ``_install_config.py``, leaving
  a partial install that the loader silently ignores.

The install's location is read from the ``.install-receipt`` the install
target writes at the repo root (prefix, library path, config path — one
per line): the gate must not *guess* where a user installed, and a
custom-``PREFIX`` install would otherwise vanish from view the moment
``PREFIX`` is no longer exported.  Without a receipt (pre-receipt
installs), the gate falls back to probing the installer's default prefix
(``$PREFIX``, else ``~/.local`` — mirrors Shakefile.hs).

This gate makes both failure modes loud: whenever an artifact copy
exists, it must be the *same build* as the current ``build/`` library,
and an installed library must be accompanied by a completed install (the
``_install_config.py`` the loader keys on).  Same-build identity is the
GNU build-id (both ``dist`` and ``install`` post-process their copies
with strip/patchelf, so raw bytes legitimately differ; the build-id note
survives both), with a SHA-256 fallback when either file carries no
build-id.  Absent *deployed* artifacts are fine — CI runners have neither,
and a dev box that never ran ``dist``/``install`` has nothing to rot.

A missing ``build/`` library is NOT automatically fine, and the two
absences must not be conflated.  The gate decides deployed-or-not first,
from the deployed side alone: with nothing deployed there is nothing to
rot (pass), but a deployed artifact whose ``build/`` counterpart is gone
cannot be certified fresh and is reported.  This gate must never rely on
the build gate failing first — it has to stand on its own, so that a green
here means something on its own terms.

Exit codes: 0 = fresh (or genuinely nothing deployed), 1 = at least one
stale, partial, or unverifiable artifact, with a per-artifact remedy.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import sys
from pathlib import Path

from tools._common import emit

_CHUNK_BYTES = 1 << 20
_ELFCLASS64 = 2
_ELFDATA2LSB = 1

# Repo-relative locations (mirror Shakefile.hs's `dist` / `install` targets).
BUILD_SO = Path("build") / "libaletheia-ffi.so"
DIST_SO = Path("dist") / "aletheia" / "lib" / "libaletheia-ffi.so"
INSTALL_RECEIPT = Path(".install-receipt")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(_CHUNK_BYTES):
            digest.update(chunk)
    return digest.hexdigest()


def _uint(data: bytes, offset: int, width: int) -> int:
    """Read a little-endian unsigned integer of `width` bytes at `offset`."""
    return int.from_bytes(data[offset : offset + width], "little")


def _note_desc(data: bytes, sec_off: int) -> str:
    """Return the descriptor of the ELF note starting at `sec_off`, as hex."""
    namesz = _uint(data, sec_off, 4)
    descsz = _uint(data, sec_off + 4, 4)
    desc_off = sec_off + 12 + ((namesz + 3) & ~3)
    return data[desc_off : desc_off + descsz].hex()


def _gnu_build_id(path: Path) -> str | None:
    """Return the GNU build-id note of a 64-bit little-endian ELF, or None.

    Minimal section-table walk (the only ELF flavour this project ships);
    any structural surprise returns None so the caller falls back to a
    content hash rather than mis-verdicting.
    """
    try:
        data = path.read_bytes()
        if data[:4] != b"\x7fELF" or data[4] != _ELFCLASS64 or data[5] != _ELFDATA2LSB:
            return None
        e_shoff = _uint(data, 0x28, 8)
        e_shentsize = _uint(data, 0x3A, 2)
        e_shnum = _uint(data, 0x3C, 2)
        strtab_off = _uint(data, e_shoff + _uint(data, 0x3E, 2) * e_shentsize + 0x18, 8)
        for i in range(e_shnum):
            hdr = e_shoff + i * e_shentsize
            name_off = strtab_off + _uint(data, hdr, 4)
            if data[name_off : data.index(b"\x00", name_off)] == b".note.gnu.build-id":
                return _note_desc(data, _uint(data, hdr + 0x18, 8))
    except OSError, IndexError, ValueError:
        return None
    return None


def _same_build(a: Path, b: Path) -> bool:
    """Return whether *a* and *b* are the same build.

    Compares GNU build-ids when BOTH files carry one (the note survives the
    strip/patchelf that ``dist``/``install`` apply, so equal build bytes
    that were post-processed differently still match). If EITHER file lacks
    a build-id (a non-ELF file, or a strip that dropped the note), falls
    back to a full SHA-256 content compare — the decision must be joint,
    never build-id on one side versus a hash on the other (which could
    never compare equal).
    """
    id_a, id_b = _gnu_build_id(a), _gnu_build_id(b)
    if id_a is not None and id_b is not None:
        return id_a == id_b
    return _sha256(a) == _sha256(b)


def _default_prefix() -> Path:
    """Return the prefix `cabal run shake -- install` targets (PREFIX env, else ~/.local)."""
    env = os.environ.get("PREFIX")
    return Path(env) if env else Path.home() / ".local"


_RECEIPT_FIELDS = 3  # prefix, library path, config path — one per line
_REINSTALL = "rerun `cabal run shake -- install`"


def _receipt_problems(receipt: Path, build_so: Path) -> list[str]:
    """Verify the install recorded in ``.install-receipt`` (authoritative path)."""
    lines = [line.strip() for line in receipt.read_text().splitlines() if line.strip()]
    if len(lines) < _RECEIPT_FIELDS:
        return [f"unreadable install receipt {receipt} — {_REINSTALL} to rewrite it"]
    deploy_so, config = Path(lines[1]), Path(lines[2])
    if not deploy_so.is_file():
        clear = "or `cabal run shake -- uninstall` to clear the receipt"
        detail = f"install receipt points at a missing library ({deploy_so})"
        return [f"{detail} — {_REINSTALL}, {clear}"]
    problems: list[str] = []
    if not _same_build(build_so, deploy_so):
        problems.append(
            f"stale local install: {deploy_so} does not match {build_so} — {_REINSTALL}"
        )
    if not config.is_file():
        detail = f"{deploy_so} exists but its {config.name} was never written"
        problems.append(f"partial local install: {detail} — {_REINSTALL}")
    return problems


def _default_prefix_problems(prefix: Path, build_so: Path) -> list[str]:
    """Probe the installer's default prefix (pre-receipt installs only)."""
    lib_dir = prefix / "lib" / "aletheia"
    deploy_so = lib_dir / "libaletheia-ffi.so"
    if not deploy_so.is_file():
        return []
    problems: list[str] = []
    if not _same_build(build_so, deploy_so):
        problems.append(
            f"stale local install: {deploy_so} does not match {build_so} — {_REINSTALL}"
        )
    # A completed install writes _install_config.py into the deploy venv's
    # site-packages; its absence means the install died partway (the
    # pre-fix Shake quoting bug left exactly this state).
    configs = list(lib_dir.glob("venv/lib/python*/site-packages/aletheia/_install_config.py"))
    if not configs:
        detail = f"{deploy_so} exists but no _install_config.py in the install venv"
        problems.append(f"partial local install: {detail} — {_REINSTALL}")
    return problems


def _deployed_artifacts(repo_root: Path, prefix: Path) -> list[Path]:
    """Return every sign that a copy was made out of ``build/``.

    These are the deployment states this gate owes a verdict on.

    Computed WITHOUT reference to ``build/`` on purpose: the gate must be able to
    say "something is deployed" even when the artifact it should be compared
    against is missing.  Otherwise "I cannot verify" is indistinguishable from
    "nothing to verify".

    A receipt counts as deployment state even when the library it names is gone
    or its contents are unreadable.  Those are findings in their own right when
    ``build/`` is present (``_receipt_problems`` reports both), so skipping them
    here would make the missing-build path silently disagree with the
    build-present path about the very same tree.
    """
    found: list[Path] = []
    dist_so = repo_root / DIST_SO
    if dist_so.is_file():
        found.append(dist_so)
    receipt = repo_root / INSTALL_RECEIPT
    if receipt.is_file():
        found.append(receipt)
    else:
        deploy_so = prefix / "lib" / "aletheia" / "libaletheia-ffi.so"
        if deploy_so.is_file():
            found.append(deploy_so)
    return found


def find_problems(repo_root: Path, prefix: Path) -> list[str]:
    """Return one remedy line per stale/partial deployed artifact (empty = fresh)."""
    build_so = repo_root / BUILD_SO
    if not build_so.is_file():
        # Decide DEPLOYED-or-not first, so this gate stands on its own rather than
        # leaning on the build gate having run before it.  Nothing deployed =>
        # nothing can be stale (an honest pass).  Something deployed but no build
        # to compare it against is a FINDING, not an OK — that is precisely the
        # unverifiable-kernel state this gate exists to catch.
        deployed = _deployed_artifacts(repo_root, prefix)
        if not deployed:
            return []
        listed = ", ".join(str(p) for p in deployed)
        return [
            f"cannot verify {len(deployed)} deployed artifact(s) — {build_so} is absent: "
            + f"{listed} — run `cabal run shake -- build` (a deployed kernel with no build "
            + "to compare against cannot be certified fresh)"
        ]

    problems: list[str] = []

    dist_so = repo_root / DIST_SO
    if dist_so.is_file() and not _same_build(build_so, dist_so):
        remedy = "rerun `cabal run shake -- dist`, or remove dist/ if no release is in flight"
        problems.append(f"stale dist/: {dist_so} does not match {build_so} — {remedy}")

    receipt = repo_root / INSTALL_RECEIPT
    if receipt.is_file():
        # Authoritative: the install target recorded exactly where it
        # deployed — no prefix guessing, no layout assumptions.
        problems.extend(_receipt_problems(receipt, build_so))
    else:
        # No receipt (pre-receipt install, or never installed): probe the
        # installer's DEFAULT prefix.  A custom-prefix pre-receipt install
        # is invisible here — rerunning install once writes the receipt
        # and brings it under watch.
        problems.extend(_default_prefix_problems(prefix, build_so))

    return problems


def main(argv: list[str] | None = None) -> int:
    """CLI entry point: report staleness, exit 1 when any artifact is stale."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path.cwd(),
        help="repository root holding build/ and dist/ (default: cwd)",
    )
    parser.add_argument(
        "--prefix",
        type=Path,
        default=None,
        help="install prefix to check (default: $PREFIX, else ~/.local)",
    )
    args = parser.parse_args(argv)
    prefix = args.prefix if args.prefix is not None else _default_prefix()

    problems = find_problems(args.repo_root, prefix)
    if problems:
        for problem in problems:
            emit(f"[check-install-freshness] FAIL: {problem}")
        return 1
    emit("[check-install-freshness] all deployed kernel artifacts match build/ (OK)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
