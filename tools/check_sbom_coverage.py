# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_sbom_coverage.py — SBOM ↔ binding-manifest coverage gate.

The release bundle stages the four language bindings' source trees, and the
SBOM (``tools/sbom_generate.py``) must bill every dependency their manifests
declare.  A dependency added to ``go.mod`` / ``Cargo.lock`` /
``pyproject.toml`` extras / a ``FetchContent_Declare`` pin that never reaches
the SBOM would ship silently unbilled — this gate closes that gap by
re-running the emitter's own manifest parsers (one interpretation, shared by
import) and diffing the result against the SBOM document.

Two explicit modes:

* ``--sbom <file> --bindings <dir>`` — the dist cross-check, run by the
  Shakefile ``dist`` rule against the STAGED bindings tree and the SBOM just
  written.  Asserts every manifest-declared dependency appears as a component
  (matched on the ``aletheia:binding`` property + name + version), that each
  binding contributes at least one component, and the Go hash discipline:
  a go.sum ``h1:`` is a Merkle dirhash, so it must ride the ``golang:h1``
  property and a Go component must never carry a CycloneDX ``hashes`` entry.
* ``--parse-only`` — the always-on CI mode (PR runners have no dist tree):
  runs the same parsers against the REPO manifests (``python/`` / ``go/`` /
  ``rust/`` / ``cpp/`` share the staged tree's layout), catching parser rot
  and manifest-shape drift on every PR without needing an SBOM.

Exit codes:
  0 — coverage holds (or, in parse-only mode, all parsers healthy).
  1 — divergence detected: a manifest entry missing from the SBOM, a binding
      absent from the bill, a hash-discipline violation, or a manifest entry
      the parsers cannot read (the drift this gate exists to catch).
  2 — could not check: missing manifest/SBOM file, malformed SBOM JSON, or a
      binding parsing to zero components (a vacuous pass is refused — every
      binding currently declares dependencies).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import cast

from tools._common import emit
from tools.sbom_generate import (
    MANIFEST_FILES,
    SbomManifestError,
    parse_binding_components,
)

REPO_ROOT = Path(__file__).resolve().parent.parent

COULD_NOT_CHECK = 2


class CoverageInputError(Exception):
    """The inputs cannot be checked (missing file / malformed SBOM document)."""


def load_sbom_components(sbom_path: Path) -> list[dict[str, object]]:
    """Load the SBOM document and return its components list, shape-checked.

    A missing file, non-JSON content, or a missing/empty ``components`` list
    raises :class:`CoverageInputError` (the could-not-check class).
    """
    if not sbom_path.is_file():
        message = f"SBOM not found: {sbom_path}"
        raise CoverageInputError(message)
    try:
        raw: object = json.loads(sbom_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        message = f"{sbom_path}: not valid JSON — {exc}"
        raise CoverageInputError(message) from exc
    if not isinstance(raw, dict):
        message = f"{sbom_path}: root must be a JSON object"
        raise CoverageInputError(message)
    components_raw = cast("dict[str, object]", raw).get("components")
    if not isinstance(components_raw, list) or not components_raw:
        message = f"{sbom_path}: missing or empty 'components' list"
        raise CoverageInputError(message)
    components: list[dict[str, object]] = []
    for idx, entry in enumerate(cast("list[object]", components_raw)):
        if not isinstance(entry, dict):
            message = f"{sbom_path}: components[{idx}] must be an object"
            raise CoverageInputError(message)
        components.append(cast("dict[str, object]", entry))
    return components


def component_property(component: dict[str, object], name: str) -> str | None:
    """Return the value of the named CycloneDX property, or None if absent."""
    properties = component.get("properties")
    if not isinstance(properties, list):
        return None
    for entry in cast("list[object]", properties):
        if isinstance(entry, dict):
            prop = cast("dict[str, object]", entry)
            if prop.get("name") == name:
                value = prop.get("value")
                if isinstance(value, str):
                    return value
    return None


def _go_hash_discipline(go_components: list[dict[str, object]]) -> list[str]:
    """Divergences for the Go hash rule: h1 rides a property, never ``hashes``."""
    diffs: list[str] = []
    for component in go_components:
        name = component.get("name")
        if component_property(component, "golang:h1") is None:
            diffs.append(f"go: component {name!r} lacks the golang:h1 property (go.sum dirhash)")
        if "hashes" in component:
            diffs.append(
                f"go: component {name!r} carries a hashes entry — a go.sum h1: is a Merkle "
                + "dirhash, not a SHA-256 of an artifact; it must ride the golang:h1 property only"
            )
    return diffs


def compare_coverage(
    expected: dict[str, list[dict[str, object]]], actual: list[dict[str, object]]
) -> list[str]:
    """Return the divergences between the manifest parses and the SBOM document.

    Membership is matched on (``aletheia:binding`` property, name, version) —
    the structural identity the emitter promises — so a stripped binding
    property makes a component invisible here by construction.
    """
    indexed: set[tuple[str, object, object]] = set()
    go_components: list[dict[str, object]] = []
    bindings_seen: set[str] = set()
    for component in actual:
        binding = component_property(component, "aletheia:binding")
        if binding is None:
            continue  # toolchain / GHC-runtime component — not a binding entry
        bindings_seen.add(binding)
        indexed.add((binding, component.get("name"), component.get("version")))
        if binding == "go":
            go_components.append(component)

    diffs: list[str] = []
    for binding, components in expected.items():
        if binding not in bindings_seen:
            diffs.append(
                f"no SBOM component carries aletheia:binding={binding} — "
                + "the whole binding is missing from the bill"
            )
            continue
        diffs.extend(
            f"{binding}: manifest declares {component['name']} {component['version']} "
            + "but the SBOM has no matching component"
            for component in components
            if (binding, component["name"], component["version"]) not in indexed
        )
    return diffs + _go_hash_discipline(go_components)


def _parse_manifests(bindings: Path) -> dict[str, list[dict[str, object]]] | int:
    """Parse the binding manifests, or return the exit code the failure maps to.

    Missing manifest files and a vacuously empty binding are COULD-NOT-CHECK
    (exit 2); a present-but-unreadable manifest is a detected divergence
    (exit 1) — that drift is what this gate exists to catch.
    """
    missing = [rel for rel in MANIFEST_FILES if not (bindings / rel).is_file()]
    if missing:
        _ = sys.stderr.write(
            "check-sbom-coverage: COULD NOT CHECK — missing manifest(s) under "
            + f"{bindings}: {', '.join(missing)}\n"
        )
        return COULD_NOT_CHECK
    try:
        expected = parse_binding_components(bindings)
    except SbomManifestError as exc:
        _ = sys.stderr.write(f"check-sbom-coverage: manifest drift — {exc}\n")
        return 1
    empty = sorted(binding for binding, components in expected.items() if not components)
    if empty:
        _ = sys.stderr.write(
            "check-sbom-coverage: COULD NOT CHECK — zero dependency components parsed for "
            + f"{', '.join(empty)}; every binding currently declares dependencies, so an "
            + "empty parse means parser rot (a vacuous pass is refused)\n"
        )
        return COULD_NOT_CHECK
    # The TypedDict components degrade to plain dicts here: the comparison
    # path treats manifest-derived and SBOM-document components uniformly.
    return cast("dict[str, list[dict[str, object]]]", expected)


def main() -> int:
    """Check SBOM ↔ manifest coverage (dist mode) or parser health (parse-only)."""
    parser = argparse.ArgumentParser(
        description="Enforce SBOM coverage of the bundled binding manifests."
    )
    _ = parser.add_argument(
        "--sbom", type=Path, default=None, help="generated SBOM JSON (dist cross-check mode)"
    )
    _ = parser.add_argument(
        "--bindings",
        type=Path,
        default=REPO_ROOT,
        help=(
            "bindings tree to parse: the staged dist/aletheia/bindings in dist mode; "
            "defaults to the repo root, whose python/ go/ rust/ cpp/ share the same layout"
        ),
    )
    _ = parser.add_argument(
        "--parse-only",
        action="store_true",
        help=(
            "always-on CI mode: run the manifest parsers only, no SBOM needed "
            "(PR runners have no dist tree)"
        ),
    )
    args = parser.parse_args()
    sbom_path = cast("Path | None", args.sbom)
    bindings = cast("Path", args.bindings)
    parse_only = bool(cast("bool", args.parse_only))
    if (sbom_path is None) != parse_only:
        parser.error("exactly one mode: --sbom <file> (dist cross-check) or --parse-only")

    expected = _parse_manifests(bindings)
    if isinstance(expected, int):
        return expected
    total = sum(len(components) for components in expected.values())

    if parse_only:
        emit(
            f"check-sbom-coverage: parse-only OK — {total} dependency components across "
            + f"{len(expected)} binding manifests (parsers healthy; no SBOM checked)"
        )
        return 0
    if sbom_path is None:  # unreachable after the mode check; narrows the type
        parser.error("--sbom is required outside --parse-only")

    try:
        actual = load_sbom_components(sbom_path)
    except CoverageInputError as exc:
        _ = sys.stderr.write(f"check-sbom-coverage: COULD NOT CHECK — {exc}\n")
        return COULD_NOT_CHECK

    diffs = compare_coverage(expected, actual)
    if diffs:
        _ = sys.stderr.write("check-sbom-coverage: divergences detected\n\n")
        for diff in diffs:
            _ = sys.stderr.write(f"  - {diff}\n")
        _ = sys.stderr.write(
            f"\nfound {len(diffs)} divergence(s) between the staged binding manifests and "
            + f"{sbom_path}.\nRegenerate the SBOM (tools/sbom_generate.py --bindings-dir) after "
            + "any manifest change — the dist rule does this; a hand-edited or stale SBOM "
            + "must never ship.\n"
        )
        return 1

    emit(
        f"check-sbom-coverage: {total} manifest-declared components across {len(expected)} "
        + f"bindings all present in {sbom_path.name} (binding property + Go h1 discipline hold)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
