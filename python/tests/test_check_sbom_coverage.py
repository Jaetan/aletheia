# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_sbom_coverage`` — the SBOM ↔ binding-manifest coverage gate.

The gate exists because a dependency added to a binding manifest could ship
in the bundle without ever reaching the SBOM.  Per the gate-teeth rule every
failure mode is proven to fail: a component dropped from the SBOM, a whole
binding stripped of its ``aletheia:binding`` property, a Go component
carrying a forbidden SHA-256 ``hashes`` entry, an unreadable manifest, and
each vacuous-input class (missing SBOM/manifest, malformed JSON, zero parsed
components) all exit non-zero.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, cast

import pytest
from _sbom_fixtures import make_bindings_tree

from tools.check_sbom_coverage import main
from tools.sbom_generate import binding_components

if TYPE_CHECKING:
    from pathlib import Path

    from tools.sbom_generate import Component


def _write_sbom(path: Path, components: list[Component]) -> Path:
    """Write a minimal SBOM document carrying ``components`` and return its path."""
    doc = {"bomFormat": "CycloneDX", "specVersion": "1.5", "components": components}
    _ = path.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    return path


def _generated_sbom(tmp_path: Path) -> tuple[Path, Path, list[Component]]:
    """Build the fixture tree + a faithful SBOM over it; return (tree, sbom, components)."""
    tree = make_bindings_tree(tmp_path / "bindings")
    components = binding_components(tree)
    sbom = _write_sbom(tmp_path / "sbom.json", components)
    return tree, sbom, components


def _run(monkeypatch: pytest.MonkeyPatch, sbom: Path, bindings: Path) -> int:
    """Invoke the gate's ``main`` in dist mode against the given SBOM + tree."""
    monkeypatch.setattr(
        "sys.argv",
        ["check_sbom_coverage", "--sbom", str(sbom), "--bindings", str(bindings)],
    )
    return main()


def test_faithful_sbom_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """An SBOM carrying every manifest-declared component exits 0."""
    tree, sbom, _ = _generated_sbom(tmp_path)
    assert _run(monkeypatch, sbom, tree) == 0


def test_parse_only_mode_passes_on_the_real_repo(monkeypatch: pytest.MonkeyPatch) -> None:
    """The always-on CI mode parses the actual repo manifests (default --bindings)."""
    monkeypatch.setattr("sys.argv", ["check_sbom_coverage", "--parse-only"])
    assert main() == 0


def test_dropped_go_component_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a go.mod require missing from the SBOM fails, naming the module."""
    tree, sbom, components = _generated_sbom(tmp_path)
    thinned = [c for c in components if c["name"] != "gopkg.in/yaml.v3"]
    assert len(thinned) == len(components) - 1  # the filter really dropped it
    _ = _write_sbom(sbom, thinned)
    assert _run(monkeypatch, sbom, tree) == 1
    assert "gopkg.in/yaml.v3" in capsys.readouterr().err


def test_dropped_cargo_lock_entry_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a Cargo.lock closure entry missing from the SBOM fails."""
    tree, sbom, components = _generated_sbom(tmp_path)
    _ = _write_sbom(sbom, [c for c in components if c["name"] != "cfg-if"])
    assert _run(monkeypatch, sbom, tree) == 1
    assert "cfg-if" in capsys.readouterr().err


def test_stripped_binding_property_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: components without aletheia:binding are invisible — the binding is missing."""
    tree, sbom, components = _generated_sbom(tmp_path)
    for component in components:
        props = component.get("properties", [])
        if any(p["name"] == "aletheia:binding" and p["value"] == "python" for p in props):
            component["properties"] = [p for p in props if p["name"] != "aletheia:binding"]
    _ = _write_sbom(sbom, components)
    assert _run(monkeypatch, sbom, tree) == 1
    assert "aletheia:binding=python" in capsys.readouterr().err


def test_go_component_with_sha256_hashes_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a go.sum h1 smuggled into hashes/SHA-256 fails (it is a dirhash)."""
    tree, sbom, components = _generated_sbom(tmp_path)
    for component in components:
        props = component.get("properties", [])
        if any(p["name"] == "aletheia:binding" and p["value"] == "go" for p in props):
            component["hashes"] = [{"alg": "SHA-256", "content": "00" * 32}]
    _ = _write_sbom(sbom, components)
    assert _run(monkeypatch, sbom, tree) == 1
    assert "dirhash" in capsys.readouterr().err


def test_unreadable_manifest_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a manifest entry the parsers cannot read is manifest drift (exit 1)."""
    tree, sbom, _ = _generated_sbom(tmp_path)
    cmake = tree / "cpp" / "CMakeLists.txt"
    doctored = cmake.read_text(encoding="utf-8")
    doctored += "\nFetchContent_Declare(weird GIT_REPOSITORY https://example.com/w)\n"
    _ = cmake.write_text(doctored, encoding="utf-8")
    assert _run(monkeypatch, sbom, tree) == 1
    assert "manifest drift" in capsys.readouterr().err


def test_missing_sbom_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: no SBOM file = COULD-NOT-CHECK (exit 2), never a silent pass."""
    tree = make_bindings_tree(tmp_path / "bindings")
    assert _run(monkeypatch, tmp_path / "absent.json", tree) == 2


def test_malformed_sbom_json_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: non-JSON SBOM content is COULD-NOT-CHECK (exit 2)."""
    tree = make_bindings_tree(tmp_path / "bindings")
    sbom = tmp_path / "sbom.json"
    _ = sbom.write_text("not json {", encoding="utf-8")
    assert _run(monkeypatch, sbom, tree) == 2


def test_missing_manifest_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a staged tree missing a manifest is COULD-NOT-CHECK (exit 2)."""
    tree, sbom, _ = _generated_sbom(tmp_path)
    (tree / "go" / "go.mod").unlink()
    assert _run(monkeypatch, sbom, tree) == 2


def test_zero_parsed_components_is_vacuous(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a binding parsing to zero components refuses with exit 2, not a pass."""
    tree, sbom, _ = _generated_sbom(tmp_path)
    no_extras = '[project]\nname = "aletheia"\nversion = "1.2.3"\n'
    no_extras += "\n[project.optional-dependencies]\n"
    _ = (tree / "python" / "pyproject.toml").write_text(no_extras, encoding="utf-8")
    assert _run(monkeypatch, sbom, tree) == 2
    assert "vacuous" in capsys.readouterr().err


def test_parse_only_missing_manifests_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """TEETH: parse-only over a tree without manifests is COULD-NOT-CHECK (exit 2)."""
    monkeypatch.setattr(
        "sys.argv", ["check_sbom_coverage", "--parse-only", "--bindings", str(tmp_path)]
    )
    assert main() == 2


def test_exactly_one_mode_is_required(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """Neither mode, or both modes, is an argparse usage error (exit 2)."""
    monkeypatch.setattr("sys.argv", ["check_sbom_coverage"])
    with pytest.raises(SystemExit) as neither:
        _ = main()
    assert neither.value.code == 2
    monkeypatch.setattr(
        "sys.argv",
        ["check_sbom_coverage", "--parse-only", "--sbom", str(tmp_path / "sbom.json")],
    )
    with pytest.raises(SystemExit) as both:
        _ = main()
    assert both.value.code == 2


def test_generated_components_json_roundtrip(tmp_path: Path) -> None:
    """The emitter's components survive a JSON round-trip identically.

    The coverage gate reads components back from the SBOM document, so the
    identity it matches on must be exactly what ``json.dumps`` preserved.
    """
    tree = make_bindings_tree(tmp_path / "bindings")
    components = binding_components(tree)
    rendered = json.dumps(components)
    assert cast("list[Component]", json.loads(rendered)) == components
