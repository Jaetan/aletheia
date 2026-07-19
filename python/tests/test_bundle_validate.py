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
    parity_problems,
    parse_args,
    recipe_shape_errors,
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
     go mod edit -replace "github.com/aletheia-automotive/aletheia-go={_HERE}/bindings/go"
     go get github.com/aletheia-automotive/aletheia-go/aletheia

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
        replace_arg = f"github.com/aletheia-automotive/aletheia-go={_HERE}/bindings/go"
        assert recipes["go"] == [
            f'go mod edit -replace "{replace_arg}"',
            "go get github.com/aletheia-automotive/aletheia-go/aletheia",
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
