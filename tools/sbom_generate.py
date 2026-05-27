#!/usr/bin/env python3
"""tools/sbom_generate.py — Emit a CycloneDX 1.5 SBOM for a dist artifact.

Closes UR-3 (Reproducible build verification) sub-item "no SBOM per release"
and CICD-5.3.

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
import hashlib
import json
import re
import subprocess
import sys
import uuid
from pathlib import Path


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _run(cmd: list[str]) -> str:
    out = subprocess.run(cmd, check=True, capture_output=True, text=True)
    return out.stdout.strip()


def _git_commit(repo: Path) -> str:
    try:
        return _run(["git", "-C", str(repo), "rev-parse", "HEAD"])
    except subprocess.CalledProcessError:
        return "unknown"


def _agda_stdlib(repo: Path) -> str:
    lib_file = repo / "aletheia.agda-lib"
    for line in lib_file.read_text(encoding="utf-8").splitlines():
        if line.startswith("depend:"):
            return line.split(":", 1)[1].strip()
    return "unknown"


def _ghc_version() -> str:
    try:
        return _run(["ghc", "--numeric-version"])
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "unknown"


def _cabal_version() -> str:
    try:
        out = _run(["cabal", "--numeric-version"])
        return out
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "unknown"


def _agda_version() -> str:
    try:
        return _run(["agda", "--version"]).split(" ")[-1]
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "unknown"


def _python_version() -> str:
    return f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}"


def _aletheia_version(repo: Path) -> str:
    cabal_file = repo / "haskell-shim" / "aletheia.cabal"
    pat = re.compile(r"^version:\s*([\w.-]+)", re.MULTILINE)
    m = pat.search(cabal_file.read_text(encoding="utf-8"))
    return m.group(1) if m else "0.0.0"


def _ghc_libdir() -> str:
    try:
        return _run(["ghc", "--print-libdir"])
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "unknown"


def _ghc_dep_components(deps: list[Path]) -> list[dict]:
    """Each GHC runtime .so → one CycloneDX component.

    The hash field carries the post-strip + post-patchelf SHA-256 because
    those are the bytes shipped in the tarball.  Path is recorded as the
    in-tarball relative path under ``aletheia/lib/``.
    """
    components: list[dict] = []
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
                    {"alg": "SHA-256", "content": _sha256(so)},
                ],
            }
        )
    return components


def _toolchain_components(repo: Path) -> list[dict]:
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


def build_sbom(
    repo: Path,
    ghc_deps: list[Path],
    main_so: Path | None,
    source_epoch: int | None = None,
    image_id: str | None = None,
    image_base: str | None = None,
    image_libgmp: str | None = None,
) -> dict:
    """Emit a CycloneDX 1.5 SBOM.

    When ``image_id``/``image_base``/``image_libgmp`` are passed the SBOM
    additionally records OCI-image-layer pins as properties on the main
    component plus a top-level metadata property — this is the docker
    variant (CICD-A-5.4 R23 closure).  Without the image-* args the SBOM
    is the dist-variant (UR-3.2 / CICD-5.3).
    """
    aletheia_version = _aletheia_version(repo)
    git_commit = _git_commit(repo)

    # Reproducible serial number: UUID5 derived from git commit + version, so
    # the same source produces the same UUID.  Avoids uuid.uuid4()'s entropy
    # source (which would defeat artifact-level repro).  Image SBOMs get a
    # distinct namespace suffix so dist + image SBOMs from the same commit
    # don't collide on serial.
    serial_seed = f"aletheia/{aletheia_version}/{git_commit}"
    if image_id is not None:
        serial_seed += f"/image/{image_id}"
    serial_uuid = str(uuid.uuid5(uuid.NAMESPACE_URL, serial_seed))

    if source_epoch is None:
        source_epoch = int(datetime.datetime.now(datetime.UTC).timestamp())
    timestamp = datetime.datetime.fromtimestamp(source_epoch, datetime.UTC).isoformat(
        timespec="seconds"
    )

    components = _toolchain_components(repo) + _ghc_dep_components(ghc_deps)

    main_properties = [
        {"name": "aletheia:git-commit", "value": git_commit},
        {"name": "aletheia:agda-stdlib", "value": _agda_stdlib(repo)},
        {"name": "aletheia:ghc-libdir", "value": _ghc_libdir()},
    ]
    if image_id is not None:
        main_properties.append({"name": "aletheia:image-id", "value": image_id})
    if image_base is not None:
        main_properties.append({"name": "aletheia:image-base", "value": image_base})
    if image_libgmp is not None:
        main_properties.append({"name": "aletheia:image-libgmp-version", "value": image_libgmp})

    main_component = {
        "type": "container" if image_id is not None else "library",
        "bom-ref": f"pkg:aletheia/aletheia-ffi@{aletheia_version}",
        "name": "aletheia-ffi-image" if image_id is not None else "aletheia-ffi",
        "version": aletheia_version,
        "scope": "required",
        "purl": f"pkg:generic/aletheia/aletheia-ffi@{aletheia_version}",
        "description": (
            "Aletheia OCI runtime image — Debian-slim base + libgmp10 + Python 3.13 + aletheia-ffi."
            if image_id is not None
            else "Aletheia FFI shared library — formally verified CAN frame analysis."
        ),
        "properties": main_properties,
    }
    if main_so and main_so.is_file():
        main_component["hashes"] = [{"alg": "SHA-256", "content": _sha256(main_so)}]

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
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
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
        help="OCI image SHA-256 digest (docker variant; CICD-A-5.4)",
    )
    ap.add_argument(
        "--image-base",
        default=None,
        help="Base image digest (e.g. python:3.13-slim@sha256:...); used with --image-id",
    )
    ap.add_argument(
        "--image-libgmp",
        default=None,
        help="Pinned libgmp10 Debian version (e.g. 2:6.2.1+dfsg1-1.1); used with --image-id",
    )
    ap.add_argument("ghc_deps", nargs="*", type=Path, help="GHC runtime .so dependencies")
    args = ap.parse_args()

    sbom = build_sbom(
        args.repo.resolve(),
        [d.resolve() for d in args.ghc_deps],
        args.main_so,
        source_epoch=args.source_epoch,
        image_id=args.image_id,
        image_base=args.image_base,
        image_libgmp=args.image_libgmp,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(sbom, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    sha = hashlib.sha256(args.out.read_bytes()).hexdigest()
    print(f"sbom-generate: wrote {args.out} ({len(sbom['components'])} components, sha256 {sha})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
