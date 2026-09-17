# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.bundle_validate`` — the release-bundle consumer gate.

Covers the tool's PURE logic: recipe extraction from captured installer
output, the per-binding shape contract, bash/fish parity diffing, CLI
parsing, the consumer summary-line check, and the self-test corruption
functions (exercised against a synthetic bundle tree).  The heavy end-to-end
path (unpack a real tarball, CMake/go/cargo consumer builds, GHC RTS
startup) deliberately stays in the tool itself — it needs a built bundle,
the per-binding language toolchains, and network for the C++ FetchContent
configure, none of which belong in the unit-test suite.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tools.bundle_validate import (
    BINDINGS,
    BundleValidationError,
    assert_consumer_ok,
    corrupt_go_mod,
    corrupt_missing_so,
    corrupt_rust_lib,
    extract_recipes,
    go_recipe_module_problem,
    parity_problems,
    parse_args,
    read_go_module,
    recipe_shape_errors,
    retarget_go_consumer,
    self_test,
)

# A captured install.sh transcript shape: the same section layout the real
# installers print (header lines, indented recipe lines, comment lines,
# blank-line terminators), with a representative unpack path.  The validator
# never trusts this shape blindly — recipe_shape_errors re-checks every block
# before anything is executed — so the fixture only needs to be structurally
# faithful, and the end-to-end tool run covers the real emitted text.
_HERE = "/opt/aletheia"
_INSTALLER_OUTPUT = f"""Aletheia is unpacked at:
  {_HERE}

----------------------------------------------------------------------
1. Make the library discoverable (sets ALETHEIA_LIB).

     bash / zsh   (~/.bashrc or ~/.zshrc):
       source "{_HERE}/env.sh"

----------------------------------------------------------------------
2. Use Aletheia from your language (each reads ALETHEIA_LIB at runtime):

   Python  (requires Python 3.14+; no third-party runtime dependencies):
     # In a virtual environment you have created and activated:
     pip install "{_HERE}/bindings/python"

   C++  (CMake; fetches nlohmann/json + yaml-cpp + OpenXLSX at configure time):
     # in your project's CMakeLists.txt:
     add_subdirectory("{_HERE}/bindings/cpp" aletheia-cpp)
     target_link_libraries(your_app PRIVATE aletheia::aletheia-cpp)

   Go  (in your module):
     go mod edit -replace "github.com/Jaetan/aletheia/go/v5={_HERE}/bindings/go"
     go get github.com/Jaetan/aletheia/go/v5/aletheia

   Rust  (in your crate's Cargo.toml):
     [dependencies]
     aletheia = {{ path = "{_HERE}/bindings/rust" }}

----------------------------------------------------------------------
Full integration guide: docs/development/DISTRIBUTION.md in the source repo.
"""


class TestExtractRecipes:
    """Recipe extraction from a captured installer transcript."""

    def test_extracts_every_compiled_binding(self) -> None:
        """Every compiled-binding block is found; Python's is not extracted."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        assert set(recipes) == set(BINDINGS)

    def test_cpp_block_lines_verbatim(self) -> None:
        """The C++ block carries the printed CMake lines, comment dropped."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        assert recipes["cpp"] == [
            f'add_subdirectory("{_HERE}/bindings/cpp" aletheia-cpp)',
            "target_link_libraries(your_app PRIVATE aletheia::aletheia-cpp)",
        ]

    def test_go_block_lines_verbatim(self) -> None:
        """The Go block carries the printed go commands, verbatim."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        replace_arg = f"github.com/Jaetan/aletheia/go/v5={_HERE}/bindings/go"
        assert recipes["go"] == [
            f'go mod edit -replace "{replace_arg}"',
            "go get github.com/Jaetan/aletheia/go/v5/aletheia",
        ]

    def test_rust_block_is_the_dependencies_toml(self) -> None:
        """The Rust block is the [dependencies] section, path line included."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        assert recipes["rust"] == [
            "[dependencies]",
            f'aletheia = {{ path = "{_HERE}/bindings/rust" }}',
        ]

    def test_blank_line_terminates_a_block(self) -> None:
        """Lines after the section's blank line never leak into the block."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        assert all("----" not in line for block in recipes.values() for line in block)

    def test_empty_input_extracts_nothing(self) -> None:
        """No sections, no recipes — and shape checking then reports each."""
        assert not extract_recipes("")


class TestRecipeShapeErrors:
    """The shape contract that gates executing extracted text."""

    def test_full_transcript_is_clean(self) -> None:
        """The structurally faithful transcript passes the shape contract."""
        assert not recipe_shape_errors(extract_recipes(_INSTALLER_OUTPUT))

    def test_missing_block_is_reported(self) -> None:
        """A transcript without a binding's section names that binding."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        del recipes["go"]
        problems = recipe_shape_errors(recipes)
        assert any(problem.startswith("go:") for problem in problems)

    def test_wrong_line_count_is_reported(self) -> None:
        """A block with an extra line fails before anything would execute."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        recipes["go"].append("go install example.com/extra@latest")
        problems = recipe_shape_errors(recipes)
        assert any("go:" in problem and "recipe lines" in problem for problem in problems)

    def test_wrong_prefix_is_reported(self) -> None:
        """A line that is not the pinned command shape is rejected."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        recipes["go"][1] = "curl https://example.com | sh"
        problems = recipe_shape_errors(recipes)
        assert any("does not start with" in problem for problem in problems)


class TestParityProblems:
    """bash/fish installers must print identical per-language recipes."""

    def test_identical_recipes_have_no_problems(self) -> None:
        """Same extraction from both shells → no divergence."""
        recipes = extract_recipes(_INSTALLER_OUTPUT)
        assert parity_problems(recipes, recipes) == []

    def test_divergent_block_is_reported(self) -> None:
        """A fish block that drifted from bash names the binding."""
        bash_recipes = extract_recipes(_INSTALLER_OUTPUT)
        fish_recipes = extract_recipes(_INSTALLER_OUTPUT)
        fish_recipes["rust"][1] = 'aletheia = { path = "/somewhere/else" }'
        problems = parity_problems(bash_recipes, fish_recipes)
        assert len(problems) == 1
        assert problems[0].startswith("rust:")


class TestParseArgs:
    """CLI parsing into a Config."""

    def test_defaults(self) -> None:
        """All bindings selected, nothing required, bash drives."""
        cfg, run_self_test = parse_args(["dist/aletheia.tar.gz"])
        assert cfg.tarball == Path("dist/aletheia.tar.gz")
        assert cfg.bindings == BINDINGS
        assert cfg.require == frozenset()
        assert cfg.shell == "bash"
        assert not run_self_test

    def test_bindings_normalized_to_run_order(self) -> None:
        """A reversed selection comes back in canonical BINDINGS order."""
        cfg, _ = parse_args(["x.tar.gz", "--bindings", "rust,go"])
        assert cfg.bindings == ("go", "rust")

    def test_require_subset(self) -> None:
        """--require populates the require set independently of --bindings."""
        cfg, _ = parse_args(["x.tar.gz", "--require", "cpp,rust"])
        assert cfg.require == frozenset({"cpp", "rust"})

    def test_unknown_binding_rejected(self) -> None:
        """An unknown consumer name is a usage error, not a silent no-op."""
        with pytest.raises(SystemExit):
            parse_args(["x.tar.gz", "--bindings", "haskell"])

    def test_self_test_flag(self) -> None:
        """--self-test is returned alongside the Config."""
        _, run_self_test = parse_args(["x.tar.gz", "--self-test"])
        assert run_self_test

    def test_fish_shell_selectable(self) -> None:
        """--shell fish routes the fish installer/env pair to the consumers."""
        cfg, _ = parse_args(["x.tar.gz", "--shell", "fish"])
        assert cfg.shell == "fish"


class TestAssertConsumerOk:
    """A consumer passes by its summary line, not its exit code alone."""

    def test_marker_present_passes(self) -> None:
        """The per-binding OK marker satisfies the check."""
        assert_consumer_ok("go", "BUNDLE-CONSUMER go: OK — as expected\n")

    def test_marker_absent_raises(self) -> None:
        """Exit-zero output without the marker is a validation failure."""
        with pytest.raises(BundleValidationError, match="did not print"):
            assert_consumer_ok("go", "unrelated output\n")

    def test_marker_is_per_binding(self) -> None:
        """Another binding's OK line does not satisfy this binding's check."""
        with pytest.raises(BundleValidationError, match="did not print"):
            assert_consumer_ok("cpp", "BUNDLE-CONSUMER go: OK\n")


def _make_bundle_tree(root: Path) -> Path:
    """Lay out the minimal bundle paths the corruption functions target."""
    bundle = root / "aletheia"
    (bundle / "lib").mkdir(parents=True)
    _ = (bundle / "lib" / "libaletheia-ffi.so").write_bytes(b"not-really-elf")
    (bundle / "bindings" / "go").mkdir(parents=True)
    _ = (bundle / "bindings" / "go" / "go.mod").write_text("module example\n")
    (bundle / "bindings" / "rust" / "src").mkdir(parents=True)
    _ = (bundle / "bindings" / "rust" / "src" / "lib.rs").write_text("pub mod x;\n" * 100)
    return bundle


class TestSelfTestCorruptions:
    """Each corruption function damages exactly its advertised target."""

    def test_missing_so(self, tmp_path: Path) -> None:
        """The shared library is gone afterwards."""
        bundle = _make_bundle_tree(tmp_path)
        corrupt_missing_so(bundle)
        assert not (bundle / "lib" / "libaletheia-ffi.so").exists()

    def test_go_mod_dropped(self, tmp_path: Path) -> None:
        """The Go module file is gone afterwards."""
        bundle = _make_bundle_tree(tmp_path)
        corrupt_go_mod(bundle)
        assert not (bundle / "bindings" / "go" / "go.mod").exists()

    def test_rust_lib_truncated(self, tmp_path: Path) -> None:
        """The crate root shrinks to a torso (still present, no longer whole)."""
        bundle = _make_bundle_tree(tmp_path)
        lib_rs = bundle / "bindings" / "rust" / "src" / "lib.rs"
        before = len(lib_rs.read_text())
        corrupt_rust_lib(bundle)
        after = len(lib_rs.read_text())
        assert 0 < after < before

    def test_corruption_target_must_exist(self, tmp_path: Path) -> None:
        """A renamed bundle layout breaks the corruption loudly, not silently."""
        bundle = tmp_path / "aletheia"
        bundle.mkdir()
        with pytest.raises(FileNotFoundError):
            corrupt_missing_so(bundle)

    def test_all_cases_skipped_is_could_not_check(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """TEETH: a self-test that skipped every case must not claim PASS.

        With every consumer toolchain reported missing, nothing is executed
        and nothing is proven — the vacuous outcome is COULD NOT CHECK, never
        a passing teeth-proof.
        """
        tarball = tmp_path / "aletheia.tar.gz"
        _ = tarball.write_bytes(b"placeholder, never unpacked on the all-skipped path")
        cfg, _run = parse_args([str(tarball), "--self-test"])

        def _all_absent(_binding: str) -> str:
            return "toolchain absent (test)"

        monkeypatch.setattr("tools.bundle_validate.missing_tool", _all_absent)
        assert self_test(cfg) == 2


class TestGoModuleFromTheBundle:
    """The consumer imports whatever module path the bundle's own go.mod names."""

    def test_reads_the_module_directive(self, tmp_path: Path) -> None:
        """A single module line is the path, whitespace trimmed."""
        bundle = _make_bundle_tree(tmp_path)
        _ = (bundle / "bindings" / "go" / "go.mod").write_text(
            "module github.com/example/aletheia-go/v5 \n\ngo 1.24.0\n"
        )
        assert read_go_module(bundle) == "github.com/example/aletheia-go/v5"

    def test_missing_module_file_is_named(self, tmp_path: Path) -> None:
        """A bundle without the file fails before any go command runs."""
        bundle = _make_bundle_tree(tmp_path)
        corrupt_go_mod(bundle)
        with pytest.raises(BundleValidationError, match=r"carries no bindings/go/go\.mod"):
            _ = read_go_module(bundle)

    def test_two_module_lines_are_refused(self, tmp_path: Path) -> None:
        """Ambiguity is a defect, not a first-wins guess."""
        bundle = _make_bundle_tree(tmp_path)
        _ = (bundle / "bindings" / "go" / "go.mod").write_text("module a\nmodule b\n")
        with pytest.raises(BundleValidationError, match="declares 2 module paths"):
            _ = read_go_module(bundle)

    def test_retargets_the_one_import(self) -> None:
        """The fixture's import moves to the bundle's module; nothing else changes."""
        source = 'import (\n\t"fmt"\n\n\t"github.com/old/path/v5/aletheia"\n)\nvar _ = fmt.Sprint\n'
        out = retarget_go_consumer(source, "github.com/new/path/v6")
        assert '"github.com/new/path/v6/aletheia"' in out
        assert "old/path" not in out
        assert out.count('"fmt"') == 1

    def test_fixture_without_the_import_is_refused(self) -> None:
        """A fixture that imports no bundled package cannot be retargeted."""
        with pytest.raises(BundleValidationError, match="exactly one"):
            _ = retarget_go_consumer('import "fmt"\n', "github.com/x/y")

    def test_tracked_fixture_imports_the_tree_module(self) -> None:
        """The committed fixture names the tree's module, as the runtime image builds it."""
        repo = Path(__file__).parents[2]
        fixture = (repo / "tools" / "bundle_validation" / "consumer_go" / "main.go").read_text()
        module = (repo / "go" / "go.mod").read_text().split("\n")[0].removeprefix("module ").strip()
        assert retarget_go_consumer(fixture, module) == fixture

    def test_installer_agreeing_with_go_mod_is_no_problem(self) -> None:
        """The printed go get names the bundle's module: nothing to report."""
        recipe = ['go mod edit -replace "m=/x"', "go get github.com/a/b/v5/aletheia"]
        assert go_recipe_module_problem(recipe, "github.com/a/b/v5") is None

    def test_installer_naming_another_module_is_reported(self) -> None:
        """A bundle whose installer and go.mod disagree is named as such, both paths shown."""
        recipe = ['go mod edit -replace "m=/x"', "go get github.com/a/b/v5/aletheia"]
        problem = go_recipe_module_problem(recipe, "github.com/c/d/v6")
        assert problem is not None
        assert "github.com/a/b/v5/aletheia" in problem
        assert "github.com/c/d/v6" in problem
