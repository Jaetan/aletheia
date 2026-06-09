# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Emit a CycloneDX 1.5 SBOM for a dist artifact.

Provides the "SBOM per release" deliverable for the Reproducible build
verification rule.

The SBOM enumerates the toolchain pin (Agda + stdlib version, GHC + cabal
version, Python pin) plus the GHC runtime .so dependencies that ship with
the artifact.  This is the audit trail the LGPL-contingency
``--bignum=native`` rebuild deliverable depends on for before/after
comparison.

Why a hand-rolled emitter (no syft / cyclonedx-cli dependency):
  * All the inputs are already known to Shake's `dist` rule.
  * The bill is intentionally narrow — runtime artifact, not full source
    closure.  Industry-grade scanners would over-discover.
  * Zero external dependency keeps the gate runnable on a bare CI agent.

Output schema: CycloneDX 1.5 JSON, the de-facto Linux-ecosystem default.
Cross-references to AGENTS.md § Universal Rules → "Reproducible build
verification" and PROTOCOL.md § Limits live in the bom.metadata.notes
field for downstream verifiers.
"""

from __future__ import annotations

import argparse
import datetime
import json
import re
import shutil
import subprocess
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import NotRequired, TypedDict, cast

from tools._common import emit, run_capture, sha256_file


class NameValue(TypedDict):
    """A CycloneDX ``{"name": ..., "value": ...}`` property entry."""

    name: str
    value: str


class Hash(TypedDict):
    """A CycloneDX ``{"alg": ..., "content": ...}`` hash entry."""

    alg: str
    content: str


Component = TypedDict(
    "Component",
    {
        "type": str,
        "name": str,
        "version": str,
        "scope": str,
        "purl": str,
        "bom-ref": NotRequired[str],
        "description": NotRequired[str],
        "properties": NotRequired[list[NameValue]],
        "hashes": NotRequired[list[Hash]],
    },
)


class Sbom(TypedDict):
    """The top-level CycloneDX 1.5 document this tool emits."""

    bomFormat: str
    specVersion: str
    serialNumber: str
    version: int
    metadata: dict[str, object]
    components: list[Component]


@dataclass(frozen=True)
class ImageInfo:
    """OCI-image-layer pins for the docker SBOM variant.

    Present only for the docker variant; when ``None`` is passed to
    ``build_sbom`` the dist variant is emitted instead.
    """

    image_id: str
    base: str | None
    libgmp: str | None


def _probe(tool: str, args: list[str]) -> str:
    """Return ``tool``'s output for ``args``, or ``"unknown"`` if it is absent.

    Mirrors the original per-tool ``try``/``except`` probes: a missing
    executable or a non-zero exit both fall back to ``"unknown"`` rather
    than raising, so an SBOM can still be produced on a partial toolchain.
    """
    resolved = shutil.which(tool)
    if resolved is None:
        return "unknown"
    try:
        result = run_capture([resolved, *args], check=True)
    except subprocess.CalledProcessError:
        return "unknown"
    return result.stdout.strip()


def _git_commit(repo: Path) -> str:
    """Return the HEAD commit of ``repo``, or ``"unknown"`` if unavailable."""
    git = shutil.which("git")
    if git is None:
        return "unknown"
    try:
        result = run_capture([git, "-C", str(repo), "rev-parse", "HEAD"], check=True)
    except subprocess.CalledProcessError:
        return "unknown"
    return result.stdout.strip()


def _agda_stdlib(repo: Path) -> str:
    """Return the pinned agda-stdlib version from ``aletheia.agda-lib``."""
    lib_file = repo / "aletheia.agda-lib"
    for line in lib_file.read_text(encoding="utf-8").splitlines():
        if line.startswith("depend:"):
            return line.split(":", 1)[1].strip()
    return "unknown"


def _ghc_version() -> str:
    """Return the GHC numeric version, or ``"unknown"`` if GHC is absent."""
    return _probe("ghc", ["--numeric-version"])


def _cabal_version() -> str:
    """Return the cabal numeric version, or ``"unknown"`` if cabal is absent."""
    return _probe("cabal", ["--numeric-version"])


def _agda_version() -> str:
    """Return the Agda version, or ``"unknown"`` if Agda is absent."""
    return _probe("agda", ["--version"]).split(" ")[-1]


def _aletheia_version(repo: Path) -> str:
    """Return the aletheia package version from ``haskell-shim/aletheia.cabal``."""
    cabal_file = repo / "haskell-shim" / "aletheia.cabal"
    pat = re.compile(r"^version:\s*([\w.-]+)", re.MULTILINE)
    m = pat.search(cabal_file.read_text(encoding="utf-8"))
    return m.group(1) if m else "0.0.0"


def _ghc_libdir() -> str:
    """Return GHC's library directory, or ``"unknown"`` if GHC is absent."""
    return _probe("ghc", ["--print-libdir"])


def _ghc_dep_components(deps: list[Path]) -> list[Component]:
    """Map each GHC runtime .so to one CycloneDX component.

    The hash field carries the post-strip + post-patchelf SHA-256 because
    those are the bytes shipped in the tarball.  Path is recorded as the
    in-tarball relative path under ``aletheia/lib/``.
    """
    components: list[Component] = []
    for so in deps:
        if not so.is_file():
            continue
        version = "unknown"
        # Pattern: libHSbase-4.18.2.1-...-ghc9.6.7.so → 4.18.2.1
        m = re.match(
            r"libHS([A-Za-z0-9_-]+?)-(\d[\w.-]*?)(?:-[a-z0-9]{8,})?-ghc[\d.]+\.so", so.name
        )
        package = so.stem
        if m:
            package = m.group(1)
            version = m.group(2)
        components.append(
            {
                "type": "library",
                "name": f"haskell-runtime/{package}",
                "version": version,
                "scope": "required",
                "purl": f"pkg:generic/haskell/{package}@{version}",
                "properties": [
                    {"name": "aletheia:source-file", "value": so.name},
                ],
                "hashes": [
                    {"alg": "SHA-256", "content": sha256_file(so)},
                ],
            }
        )
    return components


def _toolchain_components(repo: Path) -> list[Component]:
    """Build the toolchain (GHC / cabal / Agda / agda-stdlib) component list."""
    return [
        {
            "type": "application",
            "name": "ghc",
            "version": _ghc_version(),
            "scope": "required",
            "purl": f"pkg:generic/ghc@{_ghc_version()}",
            "description": "Glasgow Haskell Compiler — produces libaletheia-ffi.so via MAlonzo.",
        },
        {
            "type": "application",
            "name": "cabal-install",
            "version": _cabal_version(),
            "scope": "required",
            "purl": f"pkg:generic/cabal-install@{_cabal_version()}",
        },
        {
            "type": "application",
            "name": "agda",
            "version": _agda_version(),
            "scope": "required",
            "purl": f"pkg:generic/agda@{_agda_version()}",
            "description": "Agda compiler — produces MAlonzo Haskell from src/Aletheia/.",
        },
        {
            "type": "library",
            "name": "agda-stdlib",
            "version": _agda_stdlib(repo),
            "scope": "required",
            "purl": f"pkg:generic/agda-stdlib@{_agda_stdlib(repo)}",
            "description": f"Pinned in aletheia.agda-lib (depend: {_agda_stdlib(repo)}).",
        },
    ]


def _main_component(repo: Path, git_commit: str, image: ImageInfo | None) -> Component:
    """Build the SBOM's primary component (the FFI library or the OCI image)."""
    aletheia_version = _aletheia_version(repo)
    is_image = image is not None

    main_properties: list[NameValue] = [
        {"name": "aletheia:git-commit", "value": git_commit},
        {"name": "aletheia:agda-stdlib", "value": _agda_stdlib(repo)},
        {"name": "aletheia:ghc-libdir", "value": _ghc_libdir()},
    ]
    if image is not None:
        main_properties.append({"name": "aletheia:image-id", "value": image.image_id})
        if image.base is not None:
            main_properties.append({"name": "aletheia:image-base", "value": image.base})
        if image.libgmp is not None:
            main_properties.append({"name": "aletheia:image-libgmp-version", "value": image.libgmp})

    return {
        "type": "container" if is_image else "library",
        "bom-ref": f"pkg:aletheia/aletheia-ffi@{aletheia_version}",
        "name": "aletheia-ffi-image" if is_image else "aletheia-ffi",
        "version": aletheia_version,
        "scope": "required",
        "purl": f"pkg:generic/aletheia/aletheia-ffi@{aletheia_version}",
        "description": (
            "Aletheia OCI runtime image — Debian-slim base + libgmp10 + Python 3.13 + aletheia-ffi."
            if is_image
            else "Aletheia FFI shared library — formally verified CAN frame analysis."
        ),
        "properties": main_properties,
    }


def build_sbom(
    repo: Path,
    ghc_deps: list[Path],
    main_so: Path | None,
    source_epoch: int | None = None,
    image: ImageInfo | None = None,
) -> Sbom:
    """Emit a CycloneDX 1.5 SBOM.

    When ``image`` is passed the SBOM additionally records OCI-image-layer
    pins as properties on the main component plus a top-level metadata
    property — this is the docker variant.  Without ``image`` the SBOM
    is the dist-variant.
    """
    aletheia_version = _aletheia_version(repo)
    git_commit = _git_commit(repo)

    # Reproducible serial number: UUID5 derived from git commit + version, so
    # the same source produces the same UUID.  Avoids uuid.uuid4()'s entropy
    # source (which would defeat artifact-level repro).  Image SBOMs get a
    # distinct namespace suffix so dist + image SBOMs from the same commit
    # don't collide on serial.
    serial_seed = f"aletheia/{aletheia_version}/{git_commit}"
    if image is not None:
        serial_seed += f"/image/{image.image_id}"
    serial_uuid = str(uuid.uuid5(uuid.NAMESPACE_URL, serial_seed))

    if source_epoch is None:
        source_epoch = int(datetime.datetime.now(datetime.UTC).timestamp())
    timestamp = datetime.datetime.fromtimestamp(source_epoch, datetime.UTC).isoformat(
        timespec="seconds"
    )

    components = _toolchain_components(repo) + _ghc_dep_components(ghc_deps)

    main_component = _main_component(repo, git_commit, image)
    if main_so and main_so.is_file():
        main_component["hashes"] = [{"alg": "SHA-256", "content": sha256_file(main_so)}]

    return {
        "bomFormat": "CycloneDX",
        "specVersion": "1.5",
        "serialNumber": f"urn:uuid:{serial_uuid}",
        "version": 1,
        "metadata": {
            "timestamp": timestamp,
            "tools": {
                "components": [
                    {
                        "type": "application",
                        "name": "tools/sbom_generate.py",
                        "version": "0",
                        "manufacturer": {"name": "Aletheia"},
                    }
                ]
            },
            "component": main_component,
            "properties": [
                {
                    "name": "aletheia:reference",
                    "value": "AGENTS.md § Universal Rules → Reproducible build verification",
                },
                {
                    "name": "aletheia:protocol-limits",
                    "value": "docs/architecture/PROTOCOL.md § Limits",
                },
            ],
        },
        "components": components,
    }


def main() -> int:
    """Parse CLI arguments, build the SBOM, and write it to ``--out``."""
    description = (__doc__ or "").split("\n", maxsplit=1)[0]
    ap = argparse.ArgumentParser(description=description)
    ap.add_argument("--repo", type=Path, default=Path.cwd(), help="repository root (default cwd)")
    ap.add_argument("--main-so", type=Path, default=None, help="path to libaletheia-ffi.so")
    ap.add_argument("--out", type=Path, required=True, help="output JSON path")
    ap.add_argument(
        "--source-epoch",
        type=int,
        default=None,
        help="Unix epoch for SBOM timestamp (use git commit time for reproducible builds)",
    )
    ap.add_argument(
        "--image-id",
        default=None,
        help="OCI image SHA-256 digest (docker variant)",
    )
    ap.add_argument(
        "--image-base",
        default=None,
        help="Base image digest (e.g. python:3.14-slim@sha256:...); used with --image-id",
    )
    ap.add_argument(
        "--image-libgmp",
        default=None,
        help="Pinned libgmp10 Debian version (e.g. 2:6.2.1+dfsg1-1.1); used with --image-id",
    )
    ap.add_argument("ghc_deps", nargs="*", type=Path, help="GHC runtime .so dependencies")
    args = ap.parse_args()

    image = (
        ImageInfo(
            image_id=cast("str", args.image_id),
            base=cast("str | None", args.image_base),
            libgmp=cast("str | None", args.image_libgmp),
        )
        if args.image_id is not None
        else None
    )

    sbom = build_sbom(
        cast("Path", args.repo).resolve(),
        [d.resolve() for d in cast("list[Path]", args.ghc_deps)],
        cast("Path | None", args.main_so),
        source_epoch=cast("int | None", args.source_epoch),
        image=image,
    )
    out_path = cast("Path", args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    _ = out_path.write_text(json.dumps(sbom, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    sha = sha256_file(out_path)
    emit(f"sbom-generate: wrote {out_path} ({len(sbom['components'])} components, sha256 {sha})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
