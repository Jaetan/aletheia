# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.sbom_generate``'s binding-manifest parsers.

Per the gate-teeth rule each parser is exercised in BOTH directions: the
fixture tree yields the expected components, and an injected unreadable
manifest entry raises instead of silently dropping off the bill.  The
byte-determinism test pins the reproducibility contract the dist rule
depends on (two runs over the same inputs must byte-match), and the Go test
pins the hash discipline: a go.sum ``h1:`` dirhash rides a property, never a
CycloneDX SHA-256 ``hashes`` entry.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import TYPE_CHECKING, cast

import pytest
from _sbom_fixtures import (
    CFG_IF_SHA,
    CMAKELISTS,
    GO_SUM,
    JSON_SHA,
    OPENXLSX_COMMIT,
    PYPROJECT,
    make_bindings_tree,
)

from tools.sbom_generate import (
    SbomManifestError,
    binding_components,
    main,
    parse_binding_components,
)

if TYPE_CHECKING:
    from tools.sbom_generate import Component

REPO_ROOT = Path(__file__).resolve().parents[2]


def _by_name(components: list[Component]) -> dict[str, Component]:
    """Index a parser's output by component name (names are unique per binding)."""
    indexed = {component["name"]: component for component in components}
    assert len(indexed) == len(components)
    return indexed


def _properties(component: Component) -> dict[str, str]:
    """Flatten a component's CycloneDX property list into a name→value map."""
    return {prop["name"]: prop["value"] for prop in component.get("properties", [])}


def test_python_extras_become_optional_components(tmp_path: Path) -> None:
    """Each external optional-extra dep is one optional component; self-refs mint none."""
    tree = make_bindings_tree(tmp_path)
    python = _by_name(parse_binding_components(tree)["python"])
    # ``all`` and ``dev`` reference ``aletheia[...]`` itself (the version-pin
    # SSOT trick) — no external package, so no component; every external dep
    # across every extra is billed (over-report, never under-report).
    assert set(python) == {"python-can", "pyyaml", "pytest"}
    can = python["python-can"]
    assert can["scope"] == "optional"
    assert can["version"] == ">=4.6.1"
    assert can["purl"] == "pkg:pypi/python-can"  # a range is not a version — no @version
    props = _properties(can)
    assert props["aletheia:binding"] == "python"
    assert props["aletheia:python-extra"] == "can"
    assert _properties(python["pytest"])["aletheia:python-extra"] == "dev"


def test_python_unparseable_requirement_fails(tmp_path: Path) -> None:
    """TEETH: a requirement the regex cannot read raises, naming the extra."""
    tree = make_bindings_tree(tmp_path)
    doctored = PYPROJECT.replace('"python-can>=4.6.1"', '"???bogus"')
    assert doctored != PYPROJECT  # the replace really rewrote the fixture
    _ = (tree / "python" / "pyproject.toml").write_text(doctored, encoding="utf-8")
    with pytest.raises(SbomManifestError, match="'can'"):
        _ = parse_binding_components(tree)


def test_go_requires_become_required_components_with_h1_property(tmp_path: Path) -> None:
    """Go requires are required-scope; the h1 dirhash is a property, never ``hashes``."""
    tree = make_bindings_tree(tmp_path)
    go = _by_name(parse_binding_components(tree)["go"])
    assert set(go) == {"gopkg.in/yaml.v3", "example.com/other"}  # // indirect still billed
    yaml3 = go["gopkg.in/yaml.v3"]
    assert yaml3["scope"] == "required"
    assert yaml3["version"] == "v3.0.1"
    assert yaml3["purl"] == "pkg:golang/gopkg.in/yaml.v3@v3.0.1"
    assert _properties(yaml3)["golang:h1"].startswith("h1:")
    # An h1: is a Merkle dirhash over the module tree, not a SHA-256 of any
    # artifact — emitting it under hashes/SHA-256 would be an unverifiable lie.
    assert "hashes" not in yaml3


def test_go_missing_gosum_entry_fails(tmp_path: Path) -> None:
    """TEETH: a require with no go.sum h1 line (stale go.sum) raises."""
    tree = make_bindings_tree(tmp_path)
    doctored = "\n".join(
        line for line in GO_SUM.splitlines() if not line.startswith("gopkg.in/yaml.v3 v3.0.1 h1:")
    )
    assert doctored != GO_SUM.rstrip("\n")  # the filter really dropped the h1 line
    _ = (tree / "go" / "go.sum").write_text(doctored + "\n", encoding="utf-8")
    with pytest.raises(SbomManifestError, match="stale"):
        _ = parse_binding_components(tree)


def test_rust_scopes_follow_feature_reachability(tmp_path: Path) -> None:
    """Direct deps: required unless optional behind a default-off feature."""
    tree = make_bindings_tree(tmp_path)
    rust = _by_name(parse_binding_components(tree)["rust"])
    assert rust["libloading"]["scope"] == "required"  # non-optional direct dep
    assert rust["yaml-rust2"]["scope"] == "required"  # optional, behind default-on 'yaml'
    assert rust["futures-channel"]["scope"] == "optional"  # optional, behind default-off 'async'
    assert rust["libloading"]["version"] == "0.8.9"  # exact pin from the lock, not the range
    assert "aletheia" not in rust  # the crate itself is not a dependency


def test_rust_lock_closure_entries_marked_and_hashed(tmp_path: Path) -> None:
    """Non-direct lock entries: optional + closure property + real SHA-256 hash."""
    tree = make_bindings_tree(tmp_path)
    rust = _by_name(parse_binding_components(tree)["rust"])
    cfg_if = rust["cfg-if"]
    assert cfg_if["scope"] == "optional"
    assert _properties(cfg_if)["aletheia:cargo-lock-closure"] == "true"
    assert cfg_if.get("hashes") == [{"alg": "SHA-256", "content": CFG_IF_SHA}]
    # The dev-only dep is on the bill too: Cargo.lock cannot split dev from
    # runtime, so the closure is over-reported rather than under-reported.
    assert rust["futures"]["scope"] == "optional"
    # Direct deps are never closure-marked.
    assert "aletheia:cargo-lock-closure" not in _properties(rust["libloading"])


def test_rust_direct_dep_missing_from_lock_fails(tmp_path: Path) -> None:
    """TEETH: a Cargo.toml direct dep with no lock entry raises, naming it."""
    tree = make_bindings_tree(tmp_path)
    lock_path = tree / "rust" / "Cargo.lock"
    original = lock_path.read_text(encoding="utf-8")
    blocks = original.split("\n[[package]]\n")
    doctored = "\n[[package]]\n".join(block for block in blocks if '"libloading"' not in block)
    assert doctored != original  # the filter really dropped the lock entry
    _ = lock_path.write_text(doctored, encoding="utf-8")
    with pytest.raises(SbomManifestError, match="libloading"):
        _ = parse_binding_components(tree)


def test_cpp_pins_become_components_with_sha256(tmp_path: Path) -> None:
    """FetchContent pins are billed with URL-derived versions + archive SHA-256."""
    tree = make_bindings_tree(tmp_path)
    cpp = _by_name(parse_binding_components(tree)["cpp"])
    # Catch2 sits behind the standalone-tests guard, which the bundle never
    # takes (no tests/ tree staged) — test-only, allowlisted off the bill.
    assert set(cpp) == {"json", "yaml-cpp", "OpenXLSX"}
    assert cpp["json"]["version"] == "3.11.3"  # release-asset URL shape
    assert cpp["yaml-cpp"]["version"] == "0.8.0"  # tag-archive URL shape
    assert cpp["OpenXLSX"]["version"] == OPENXLSX_COMMIT  # commit-archive URL shape
    assert cpp["json"].get("hashes") == [{"alg": "SHA-256", "content": JSON_SHA}]
    props = _properties(cpp["json"])
    assert props["aletheia:binding"] == "cpp"
    assert props["aletheia:source-url"].endswith("json.tar.xz")


def test_cpp_unparsed_declare_fails(tmp_path: Path) -> None:
    """TEETH: a FetchContent_Declare shape the parser cannot read raises."""
    tree = make_bindings_tree(tmp_path)
    doctored = CMAKELISTS + "\nFetchContent_Declare(weird GIT_REPOSITORY https://example.com/w)\n"
    _ = (tree / "cpp" / "CMakeLists.txt").write_text(doctored, encoding="utf-8")
    with pytest.raises(SbomManifestError, match="FetchContent_Declare"):
        _ = parse_binding_components(tree)


def test_vacuously_empty_binding_refused(tmp_path: Path) -> None:
    """TEETH: a binding parsing to zero components is refused, never a thin bill."""
    tree = make_bindings_tree(tmp_path)
    no_extras = '[project]\nname = "aletheia"\nversion = "1.2.3"\n'
    no_extras += "\n[project.optional-dependencies]\n"
    _ = (tree / "python" / "pyproject.toml").write_text(no_extras, encoding="utf-8")
    with pytest.raises(SbomManifestError, match="python"):
        _ = binding_components(tree)


def _run_cli(monkeypatch: pytest.MonkeyPatch, tree: Path, out: Path) -> int:
    """Invoke the generator CLI against the fixture tree and the real repo root."""
    monkeypatch.setattr(
        "sys.argv",
        [
            "sbom_generate",
            "--repo",
            str(REPO_ROOT),
            "--out",
            str(out),
            "--source-epoch",
            "1700000000",
            "--bindings-dir",
            str(tree),
        ],
    )
    return main()


def test_cli_emits_binding_components_byte_deterministically(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Two CLI runs over the same inputs byte-match, and the bill carries all bindings."""
    tree = make_bindings_tree(tmp_path / "bindings")
    out_first = tmp_path / "sbom-first.json"
    out_second = tmp_path / "sbom-second.json"
    assert _run_cli(monkeypatch, tree, out_first) == 0
    assert _run_cli(monkeypatch, tree, out_second) == 0
    assert out_first.read_bytes() == out_second.read_bytes()
    doc = cast("dict[str, object]", json.loads(out_first.read_text(encoding="utf-8")))
    components = cast("list[dict[str, object]]", doc["components"])
    names = {component["name"] for component in components}
    assert {"python-can", "gopkg.in/yaml.v3", "libloading", "json"} <= names


def test_cli_manifest_error_exits_nonzero(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: an unreadable manifest fails the CLI (and the dist rule with it)."""
    tree = make_bindings_tree(tmp_path / "bindings")
    doctored = PYPROJECT.replace('"python-can>=4.6.1"', '"???bogus"')
    _ = (tree / "python" / "pyproject.toml").write_text(doctored, encoding="utf-8")
    out = tmp_path / "sbom.json"
    assert _run_cli(monkeypatch, tree, out) == 1
    assert "ERROR" in capsys.readouterr().err
    assert not out.exists()  # no partial SBOM lands on disk
