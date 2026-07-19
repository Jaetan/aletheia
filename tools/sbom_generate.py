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

With ``--bindings-dir`` (the staged ``dist/aletheia/bindings`` tree) the
bill additionally covers the four bundled binding source trees: every
dependency their manifests (``pyproject.toml`` / ``go.mod``+``go.sum`` /
``Cargo.toml``+``Cargo.lock`` / ``CMakeLists.txt`` FetchContent pins)
declare becomes a component carrying an ``aletheia:binding`` property.
Scope of the binding components is RUNTIME-FETCH dependencies only — the
packages a bundle consumer's toolchain fetches when building/installing a
binding — never build-system or toolchain entries (setuptools, cmake, the
Go/Rust toolchains).  The parsers read the STAGED tree, not the worktree:
the SBOM must describe the bytes that ship.

Why a hand-rolled emitter (no syft / cyclonedx-cli dependency):
  * All the inputs are already known to Shake's `dist` rule.
  * The bill is intentionally narrow — runtime artifact plus the bundled
    manifests' declared dependencies, not a discovered source closure.
    Industry-grade scanners would over-discover.
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
import sys
import tomllib
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, NotRequired, TypedDict, cast

from tools._common import emit, run_capture, sha256_file

if TYPE_CHECKING:
    from collections.abc import Callable


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


# ─── Binding-manifest components ─────────────────────────────────────────
# The four bundled binding source trees' dependency manifests, parsed from the
# staged bindings tree.  Fail-loud discipline throughout: a manifest entry a
# parser cannot read raises SbomManifestError — an unreadable entry must fail
# the SBOM, never silently drop off the bill.


class SbomManifestError(Exception):
    """A binding manifest is missing or carries an entry the parser cannot read."""


# Every file the binding parsers read, relative to the bindings dir.  The
# coverage gate (tools/check_sbom_coverage.py) pre-checks these for existence
# so a missing file is its COULD-NOT-CHECK class, distinct from a
# present-but-unreadable manifest.
MANIFEST_FILES: tuple[str, ...] = (
    "cpp/CMakeLists.txt",
    "go/go.mod",
    "go/go.sum",
    "python/pyproject.toml",
    "rust/Cargo.toml",
    "rust/Cargo.lock",
)


def _require_file(path: Path) -> Path:
    """Return ``path`` if it is a file, else raise :class:`SbomManifestError`."""
    if not path.is_file():
        message = f"binding manifest missing: {path}"
        raise SbomManifestError(message)
    return path


def _table(value: object, context: str) -> dict[str, object]:
    """Shape-check ``value`` as a TOML table, or raise naming ``context``."""
    if not isinstance(value, dict):
        message = f"{context}: expected a table"
        raise SbomManifestError(message)
    return cast("dict[str, object]", value)


def _string(value: object, context: str) -> str:
    """Shape-check ``value`` as a non-empty string, or raise naming ``context``."""
    if not isinstance(value, str) or not value:
        message = f"{context}: expected a non-empty string"
        raise SbomManifestError(message)
    return value


def _string_list(value: object, context: str) -> list[str]:
    """Shape-check ``value`` as a list of strings, or raise naming ``context``."""
    if not isinstance(value, list) or not all(
        isinstance(item, str) for item in cast("list[object]", value)
    ):
        message = f"{context}: expected a list of strings"
        raise SbomManifestError(message)
    return cast("list[str]", value)


# A PEP 508 requirement head: name, optional [extras], optional version spec.
# Environment markers (``; ...``) are not matched — none of the binding's
# extras use them, and an unmatched entry fails loud rather than mis-parsing.
_PY_REQUIREMENT_RE = re.compile(
    r"^(?P<name>[A-Za-z0-9](?:[A-Za-z0-9._-]*[A-Za-z0-9])?)"
    + r"(?:\[[^\]]+\])?"
    + r"(?P<spec>\s*[<>=!~].*)?$"
)


def _normalize_pypi(name: str) -> str:
    """PEP 503 normalisation: runs of ``-``/``_``/``.`` collapse to ``-``, lowercased."""
    return re.sub(r"[-_.]+", "-", name).lower()


def _python_components(bindings_dir: Path) -> list[Component]:
    """Parse ``python/pyproject.toml`` optional extras into components.

    Every ``[project.optional-dependencies]`` requirement becomes one
    ``scope: optional`` component — the packages a consumer fetches with
    ``pip install aletheia[<extra>]``.  The core package has zero runtime
    dependencies by design, so the extras ARE the Python binding's entire
    runtime-fetch surface.  ``[build-system]`` requires are deliberately
    absent (build-system entries are out of scope for binding components).
    Self-referential extras (``aletheia[...]``, the version-pin SSOT trick)
    are not external packages and mint no component.  The version field
    carries the declared requirement range verbatim; a range is not a
    version, so the purl omits ``@version`` rather than invent a pin.
    """
    path = _require_file(bindings_dir / "python" / "pyproject.toml")
    data = cast("dict[str, object]", tomllib.loads(path.read_text(encoding="utf-8")))
    project = _table(data.get("project"), f"{path}: [project]")
    project_name = _string(project.get("name"), f"{path}: project.name")
    extras = _table(
        project.get("optional-dependencies"), f"{path}: [project.optional-dependencies]"
    )
    pulled: dict[tuple[str, str], set[str]] = {}  # (name, spec) -> extras that pull it
    for extra, entries in extras.items():
        for entry in _string_list(entries, f"{path}: optional-dependencies[{extra}]"):
            match = _PY_REQUIREMENT_RE.match(entry.strip())
            if match is None:
                message = f"{path}: cannot parse requirement {entry!r} in extra '{extra}'"
                raise SbomManifestError(message)
            name = match.group("name")
            if _normalize_pypi(name) == _normalize_pypi(project_name):
                continue  # self-referential extra, not an external package
            spec = (match.group("spec") or "").strip()
            pulled.setdefault((name, spec), set()).add(extra)
    return [
        {
            "type": "library",
            "name": name,
            "version": spec or "unspecified",
            "scope": "optional",
            "purl": f"pkg:pypi/{_normalize_pypi(name)}",
            "properties": [
                {"name": "aletheia:binding", "value": "python"},
                {"name": "aletheia:python-extra", "value": ",".join(sorted(extra_names))},
            ],
        }
        for (name, spec), extra_names in pulled.items()
    ]


# Field counts of the whitespace-split go.mod / go.sum line shapes.
_GO_REQUIRE_FIELDS = 2  # "<module> <version>"
_GO_SUM_FIELDS = 3  # "<module> <version> h1:<digest>"


def _split_go_require(entry: str, context: str) -> tuple[str, str]:
    """Split one require entry into (module, version), or raise."""
    parts = entry.split()
    if len(parts) != _GO_REQUIRE_FIELDS or not parts[1].startswith("v"):
        message = f"{context}: cannot parse require entry {entry!r}"
        raise SbomManifestError(message)
    return (parts[0], parts[1])


def _parse_go_requires(text: str, context: str) -> list[tuple[str, str]]:
    """Return (module, version) for every ``require`` directive in a go.mod.

    Handles both the single-line and the block form; ``//`` comments
    (including ``// indirect`` markers — indirect requires stay on the bill)
    are stripped first.
    """
    requires: list[tuple[str, str]] = []
    in_block = False
    for raw in text.splitlines():
        line = raw.split("//", 1)[0].strip()
        if not line:
            continue
        if in_block:
            if line == ")":
                in_block = False
            else:
                requires.append(_split_go_require(line, context))
        elif line == "require (":
            in_block = True
        elif line.startswith("require "):
            requires.append(_split_go_require(line.removeprefix("require "), context))
    if in_block:
        message = f"{context}: unterminated require block"
        raise SbomManifestError(message)
    return requires


def _parse_go_sum(text: str, context: str) -> dict[tuple[str, str], str]:
    """Map (module, version) to its ``h1:`` module digest from a go.sum.

    ``<version>/go.mod`` lines (the go.mod-only digests) are skipped — the
    module digest is the line whose version carries no suffix.
    """
    digests: dict[tuple[str, str], str] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != _GO_SUM_FIELDS or not parts[2].startswith("h1:"):
            message = f"{context}: cannot parse go.sum line {line!r}"
            raise SbomManifestError(message)
        module, version, digest = parts
        if not version.endswith("/go.mod"):
            digests[(module, version)] = digest
    return digests


def _go_components(bindings_dir: Path) -> list[Component]:
    """Parse ``go/go.mod`` requires into ``scope: required`` components.

    The ``h1:`` digest from ``go.sum`` rides along as the ``golang:h1``
    property, deliberately NOT as a CycloneDX ``hashes`` entry: an ``h1:``
    is a base64 Merkle tree hash over the extracted module tree
    (golang.org/x/mod dirhash), not a SHA-256 of any single artifact —
    emitting it under ``alg: SHA-256`` would be an attestation no validator
    could reproduce.  The optional ``go/excel`` module is a separate Go
    module the bundle does not stage, so it is out of scope here.
    """
    mod_path = _require_file(bindings_dir / "go" / "go.mod")
    sum_path = _require_file(bindings_dir / "go" / "go.sum")
    requires = _parse_go_requires(mod_path.read_text(encoding="utf-8"), str(mod_path))
    digests = _parse_go_sum(sum_path.read_text(encoding="utf-8"), str(sum_path))
    components: list[Component] = []
    for module, version in requires:
        digest = digests.get((module, version))
        if digest is None:
            message = f"{sum_path}: no h1: entry for {module} {version} — go.sum is stale"
            raise SbomManifestError(message)
        components.append(
            {
                "type": "library",
                "name": module,
                "version": version,
                "scope": "required",
                "purl": f"pkg:golang/{module}@{version}",
                "properties": [
                    {"name": "aletheia:binding", "value": "go"},
                    {"name": "golang:h1", "value": digest},
                ],
            }
        )
    return components


@dataclass(frozen=True)
class _LockPackage:
    """One ``[[package]]`` entry of a Cargo.lock (checksum absent for the root crate)."""

    name: str
    version: str
    checksum: str | None


def _rust_default_enabled_deps(cargo: dict[str, object], context: str) -> set[str]:
    """Return the optional-dependency keys enabled by the crate's default features.

    Walks the ``[features]`` graph from ``default``: ``dep:<key>`` entries
    enable the named optional dependency, plain names recurse into other
    features, ``pkg/feat`` implicitly enables the optional dependency
    ``pkg``, and the weak form ``pkg?/feat`` enables nothing by itself.
    """
    features_raw = cargo.get("features")
    features = _table(features_raw, f"{context}: [features]") if features_raw is not None else {}
    enabled: set[str] = set()
    seen: set[str] = set()
    stack = ["default"] if "default" in features else []
    while stack:
        feature = stack.pop()
        if feature in seen:
            continue
        seen.add(feature)
        for entry in _string_list(features.get(feature, []), f"{context}: features.{feature}"):
            if entry.startswith("dep:"):
                enabled.add(entry.removeprefix("dep:"))
            elif "/" in entry:
                base = entry.split("/", 1)[0]
                if not base.endswith("?"):
                    enabled.add(base)
            elif entry in features:
                stack.append(entry)
            else:
                message = f"{context}: features.{feature} entry {entry!r} names no feature or dep"
                raise SbomManifestError(message)
    return enabled


def _rust_lock_packages(lock_path: Path) -> list[_LockPackage]:
    """Parse every ``[[package]]`` entry of a Cargo.lock, shape-checked."""
    data = cast("dict[str, object]", tomllib.loads(lock_path.read_text(encoding="utf-8")))
    raw = data.get("package")
    if not isinstance(raw, list) or not raw:
        message = f"{lock_path}: missing or empty [[package]] list"
        raise SbomManifestError(message)
    packages: list[_LockPackage] = []
    for idx, entry_raw in enumerate(cast("list[object]", raw)):
        context = f"{lock_path}: package[{idx}]"
        entry = _table(entry_raw, context)
        checksum_raw = entry.get("checksum")
        checksum = None if checksum_raw is None else _string(checksum_raw, f"{context}.checksum")
        if checksum is not None and re.fullmatch(r"[0-9a-f]{64}", checksum) is None:
            message = f"{context}: checksum is not 64 lowercase hex chars (not a SHA-256)"
            raise SbomManifestError(message)
        packages.append(
            _LockPackage(
                name=_string(entry.get("name"), f"{context}.name"),
                version=_string(entry.get("version"), f"{context}.version"),
                checksum=checksum,
            )
        )
    return packages


def _rust_component(pkg: _LockPackage, scope: str, lock_path: Path, *, closure: bool) -> Component:
    """Build one Cargo.lock-backed component (real SHA-256 checksum required)."""
    if pkg.checksum is None:
        message = f"{lock_path}: package {pkg.name} {pkg.version} has no checksum — cannot attest"
        raise SbomManifestError(message)
    properties: list[NameValue] = [{"name": "aletheia:binding", "value": "rust"}]
    if closure:
        properties.append({"name": "aletheia:cargo-lock-closure", "value": "true"})
    return {
        "type": "library",
        "name": pkg.name,
        "version": pkg.version,
        "scope": scope,
        "purl": f"pkg:cargo/{pkg.name}@{pkg.version}",
        "properties": properties,
        "hashes": [{"alg": "SHA-256", "content": pkg.checksum}],
    }


def _rust_direct_dep(key: str, spec: object, toml_path: Path) -> tuple[str, bool]:
    """Return (lock name, optional flag) for one ``[dependencies]`` entry."""
    if isinstance(spec, str):
        return (key, False)
    table = _table(spec, f"{toml_path}: dependencies.{key}")
    optional_raw = table.get("optional", False)
    if not isinstance(optional_raw, bool):
        message = f"{toml_path}: dependencies.{key}.optional: expected a boolean"
        raise SbomManifestError(message)
    package_raw = table.get("package")
    if package_raw is None:
        return (key, optional_raw)
    return (_string(package_raw, f"{toml_path}: dependencies.{key}.package"), optional_raw)


def _rust_components(bindings_dir: Path) -> list[Component]:
    """Parse ``rust/Cargo.toml`` + ``Cargo.lock`` into components.

    Direct ``[dependencies]`` entries are classified by feature
    reachability: a non-optional dependency, or an optional one behind a
    default-enabled feature, is ``scope: required``; an optional dependency
    behind a default-off feature is ``scope: optional``.  Every remaining
    Cargo.lock package (the transitive closure, which Cargo.lock cannot
    split into runtime vs dev-only) is over-reported as ``scope: optional``
    with the ``aletheia:cargo-lock-closure`` property — over-report, never
    under-report.  Versions and SHA-256 checksums come from the lock (exact
    pins), never from Cargo.toml ranges.
    """
    toml_path = _require_file(bindings_dir / "rust" / "Cargo.toml")
    lock_path = _require_file(bindings_dir / "rust" / "Cargo.lock")
    cargo = cast("dict[str, object]", tomllib.loads(toml_path.read_text(encoding="utf-8")))
    package = _table(cargo.get("package"), f"{toml_path}: [package]")
    crate_name = _string(package.get("name"), f"{toml_path}: package.name")
    deps_raw = cargo.get("dependencies")
    deps = _table(deps_raw, f"{toml_path}: [dependencies]") if deps_raw is not None else {}
    packages = _rust_lock_packages(lock_path)
    by_name: dict[str, list[_LockPackage]] = {}
    for pkg in packages:
        by_name.setdefault(pkg.name, []).append(pkg)

    components, direct = _rust_direct_components(
        deps, _rust_default_enabled_deps(cargo, str(toml_path)), by_name, toml_path, lock_path
    )
    for pkg in packages:
        if pkg.name == crate_name and pkg.checksum is None:
            continue  # the bundle's own crate, not a dependency
        if (pkg.name, pkg.version) not in direct:
            components.append(_rust_component(pkg, "optional", lock_path, closure=True))
    return components


def _rust_direct_components(
    deps: dict[str, object],
    enabled: set[str],
    by_name: dict[str, list[_LockPackage]],
    toml_path: Path,
    lock_path: Path,
) -> tuple[list[Component], set[tuple[str, str]]]:
    """Classify the direct ``[dependencies]`` entries against the lock.

    Returns the direct components plus their (name, version) identities so
    the caller can bill the remaining lock packages as closure entries.
    """
    components: list[Component] = []
    direct: set[tuple[str, str]] = set()
    for key, spec in deps.items():
        lock_name, optional = _rust_direct_dep(key, spec, toml_path)
        entries = by_name.get(lock_name, [])
        if len(entries) != 1:
            message = (
                f"{lock_path}: expected exactly one lock package named {lock_name!r} for "
                + f"direct dependency {key!r}, found {len(entries)}"
            )
            raise SbomManifestError(message)
        scope = "required" if (not optional or key in enabled) else "optional"
        components.append(_rust_component(entries[0], scope, lock_path, closure=False))
        direct.add((entries[0].name, entries[0].version))
    return components, direct


# Catch2 is declared only inside the standalone-tests guard (BUILD_TESTING +
# top-level build + a present tests/ tree); the bundle ships no tests/ tree,
# so a bundle consumer can never fetch it — test-only, excluded from the bill.
_CPP_TEST_ONLY_FETCHES: frozenset[str] = frozenset({"Catch2"})

# The one FetchContent shape the C++ binding uses: URL + URL_HASH SHA256=.
_FETCH_DECLARE_RE = re.compile(
    r"FetchContent_Declare\(\s*([A-Za-z0-9_-]+)"
    + r"\s+URL\s+(\S+)"
    + r"\s+URL_HASH\s+SHA256=([0-9a-fA-F]{64})\b"
)
_FETCH_COUNT_RE = re.compile(r"FetchContent_Declare\s*\(")

# Pinned-version shapes a fetch URL can carry: a release-asset tag, an
# archive tag (optionally v-prefixed), or a pinned commit archive.
_CPP_URL_VERSION_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"/releases/download/v([0-9][\w.]*)/"),
    re.compile(r"/archive/refs/tags/v?([0-9][\w.]*)\.tar"),
    re.compile(r"/archive/([0-9a-f]{7,40})\.tar"),
)


def _cpp_pin_version(url: str, context: str) -> str:
    """Extract the pinned version (release tag or commit hash) from a fetch URL."""
    for pattern in _CPP_URL_VERSION_PATTERNS:
        match = pattern.search(url)
        if match:
            return match.group(1)
    message = f"{context}: cannot derive a pinned version from URL {url}"
    raise SbomManifestError(message)


def _cpp_components(bindings_dir: Path) -> list[Component]:
    """Parse ``cpp/CMakeLists.txt`` FetchContent pins into components.

    Every ``FetchContent_Declare`` must parse as the ``URL`` + ``URL_HASH
    SHA256=...`` shape — the parsed count is compared against the raw
    occurrence count, so a declare this parser cannot read fails the SBOM
    instead of silently dropping a pin.  The ``URL_HASH`` is a real SHA-256
    of the fetched source archive, so it lands in the CycloneDX ``hashes``
    list (unlike the Go ``h1:`` dirhash).
    """
    path = _require_file(bindings_dir / "cpp" / "CMakeLists.txt")
    text = path.read_text(encoding="utf-8")
    declares = _FETCH_DECLARE_RE.findall(text)
    total = len(_FETCH_COUNT_RE.findall(text))
    if len(declares) != total:
        parsed_names = ", ".join(name for name, _, _ in declares) or "none"
        message = (
            f"{path}: found {total} FetchContent_Declare occurrence(s) but parsed "
            f"{len(declares)} ({parsed_names}) — an unparsed declare would drop a pin from "
            "the SBOM; teach the parser the new shape or fix the declare"
        )
        raise SbomManifestError(message)
    components: list[Component] = []
    for name, url, sha in declares:
        if name in _CPP_TEST_ONLY_FETCHES:
            continue
        version = _cpp_pin_version(url, str(path))
        components.append(
            {
                "type": "library",
                "name": name,
                "version": version,
                "scope": "required",
                "purl": f"pkg:generic/{name}@{version}",
                "properties": [
                    {"name": "aletheia:binding", "value": "cpp"},
                    {"name": "aletheia:source-url", "value": url},
                ],
                "hashes": [{"alg": "SHA-256", "content": sha.lower()}],
            }
        )
    return components


# Alphabetical by binding name — this order, plus the per-binding sort in
# parse_binding_components, makes the emitted component list deterministic.
_BINDING_PARSERS: tuple[tuple[str, Callable[[Path], list[Component]]], ...] = (
    ("cpp", _cpp_components),
    ("go", _go_components),
    ("python", _python_components),
    ("rust", _rust_components),
)


def parse_binding_components(bindings_dir: Path) -> dict[str, list[Component]]:
    """Parse all four staged binding manifests, keyed by binding name.

    Shared by the SBOM emitter and by ``tools/check_sbom_coverage.py`` (the
    coverage gate re-runs these same parsers against the same tree and diffs
    the result against the SBOM document, so the two can never disagree on
    manifest interpretation).  Each binding's list is sorted by
    (name, version) so the emitted SBOM is byte-reproducible.
    """
    return {
        binding: sorted(parser(bindings_dir), key=lambda c: (c["name"], c["version"]))
        for binding, parser in _BINDING_PARSERS
    }


def binding_components(bindings_dir: Path) -> list[Component]:
    """Flatten the per-binding parses, refusing a vacuously empty binding.

    Every binding currently declares at least one dependency, so an empty
    parse means either the manifest lost them all or the parser rotted —
    refused either way rather than shipping a silently thinner bill.
    """
    components: list[Component] = []
    for binding, parsed in parse_binding_components(bindings_dir).items():
        if not parsed:
            message = (
                f"{bindings_dir}: binding '{binding}' parsed to zero dependency components — "
                "a vacuously empty SBOM section is refused"
            )
            raise SbomManifestError(message)
        components.extend(parsed)
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


@dataclass(frozen=True)
class SbomOptions:
    """Optional SBOM inputs beyond the core artifact.

    ``source_epoch`` pins the timestamp for reproducible builds; ``image``
    selects the docker variant (OCI-layer pins); ``bindings_dir`` (the
    staged bindings tree) adds the four binding manifests' dependency
    components.
    """

    source_epoch: int | None = None
    image: ImageInfo | None = None
    bindings_dir: Path | None = None


def build_sbom(
    repo: Path,
    ghc_deps: list[Path],
    main_so: Path | None,
    options: SbomOptions | None = None,
) -> Sbom:
    """Emit a CycloneDX 1.5 SBOM.

    When ``options.image`` is passed the SBOM additionally records
    OCI-image-layer pins as properties on the main component plus a
    top-level metadata property — this is the docker variant.  Without
    ``options.image`` the SBOM is the dist-variant.  When
    ``options.bindings_dir`` is passed (the staged bindings tree) the four
    binding manifests' dependency components are appended — see
    :func:`binding_components`.
    """
    opts = options if options is not None else SbomOptions()
    image = opts.image
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

    source_epoch = opts.source_epoch
    if source_epoch is None:
        source_epoch = int(datetime.datetime.now(datetime.UTC).timestamp())
    timestamp = datetime.datetime.fromtimestamp(source_epoch, datetime.UTC).isoformat(
        timespec="seconds"
    )

    components = _toolchain_components(repo) + _ghc_dep_components(ghc_deps)
    if opts.bindings_dir is not None:
        components += binding_components(opts.bindings_dir)

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
        "--bindings-dir",
        type=Path,
        default=None,
        help=(
            "staged bindings tree (dist/aletheia/bindings) — adds the four bundled "
            "binding source trees' manifest-declared dependencies to the SBOM"
        ),
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

    try:
        sbom = build_sbom(
            cast("Path", args.repo).resolve(),
            [d.resolve() for d in cast("list[Path]", args.ghc_deps)],
            cast("Path | None", args.main_so),
            SbomOptions(
                source_epoch=cast("int | None", args.source_epoch),
                image=image,
                bindings_dir=cast("Path | None", args.bindings_dir),
            ),
        )
    except SbomManifestError as exc:
        _ = sys.stderr.write(f"sbom-generate: ERROR — {exc}\n")
        return 1
    out_path = cast("Path", args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    _ = out_path.write_text(json.dumps(sbom, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    sha = sha256_file(out_path)
    emit(f"sbom-generate: wrote {out_path} ({len(sbom['components'])} components, sha256 {sha})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
