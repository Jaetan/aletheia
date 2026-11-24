# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The bundle's Rust manifest names no target the bundle lacks, and the consumers build at PR time.

``tools/bundle_rust_manifest.py`` writes the crate's manifest without its
``[[example]]`` tables, which the dist step applies to the staged crate; the
consumer gate (``tools/check_bundle_consumers.py``) builds the Go, C++ and Rust
consumers against the tree in their bindings' lanes, the crate staged as dist
stages it.
"""

from __future__ import annotations

import tomllib
from pathlib import Path
from typing import TYPE_CHECKING

from _ci_runner import ci_runner

from tools import bundle_rust_manifest, check_bundle_consumers
from tools._ci_steps import register_all_steps
from tools._common import CPP_CONFIGURE_STEP, CommandWord, RelPath
from tools.bundle_rust_manifest import ManifestText, staged_manifest

if TYPE_CHECKING:
    import pytest

_REPO = Path(__file__).resolve().parents[2]
_MANIFEST = _REPO / "rust" / "Cargo.toml"
_DIST_RULE = _REPO / "shake" / "Rules" / "Dist.hs"

_WITH_EXAMPLES = ManifestText(
    '[package]\nname = "x"\n\n# the first example\n[[example]]\nname = "a"\ntest = true\n\n'
    + '# kept\n[dependencies]\nserde = "1"\n\n[[example]]\nname = "b"\n'
)


def test_the_repository_manifest_is_staged_without_its_examples() -> None:
    """The staged manifest drops every [[example]] table and keeps every other key."""
    text = ManifestText(_MANIFEST.read_text(encoding="utf-8"))
    repo = tomllib.loads(text)
    staged = tomllib.loads(staged_manifest(text))
    assert "example" in repo
    assert "example" not in staged
    _ = repo.pop("example")
    assert staged == repo


def test_a_table_after_an_example_is_kept_and_the_example_s_comment_goes() -> None:
    """Tables after an example survive; comments directly above it do not, others do."""
    staged = str(staged_manifest(_WITH_EXAMPLES))
    assert tomllib.loads(staged) == {"package": {"name": "x"}, "dependencies": {"serde": "1"}}
    assert "# the first example" not in staged
    assert "# kept" in staged
    assert staged.endswith('serde = "1"\n')


def test_the_tool_rewrites_a_manifest_in_place(tmp_path: Path) -> None:
    """Run on a file, the tool leaves the staged manifest there; a missing file is exit 2."""
    manifest = tmp_path / "Cargo.toml"
    _ = manifest.write_text(_WITH_EXAMPLES, encoding="utf-8")
    assert bundle_rust_manifest.main([CommandWord(str(manifest))]) == 0
    assert manifest.read_text(encoding="utf-8") == staged_manifest(_WITH_EXAMPLES)
    assert bundle_rust_manifest.main([CommandWord(str(tmp_path / "absent.toml"))]) == 2


def test_the_dist_rule_stages_the_manifest_without_examples() -> None:
    """Dist rewrites the staged manifest with the tool right after staging the Rust binding."""
    rule = _DIST_RULE.read_text(encoding="utf-8")
    staged = rule.index('stageBinding "rust"')
    call = rule.index('"tools.bundle_rust_manifest" (distBindings </> "rust" </> "Cargo.toml")')
    assert staged < call


def test_a_branch_reaches_each_consumer_by_its_binding_or_the_gate() -> None:
    """No diff, or an empty one, builds every consumer; a change elsewhere builds none."""
    for binding in check_bundle_consumers.BINDINGS:
        assert check_bundle_consumers.in_scope(binding, None)
        assert check_bundle_consumers.in_scope(binding, [])
        assert check_bundle_consumers.in_scope(
            binding, [RelPath("tools/check_bundle_consumers.py")]
        )
        assert not check_bundle_consumers.in_scope(binding, [RelPath("docs/README.md")])
    assert check_bundle_consumers.in_scope("go", [RelPath("go/aletheia/ltl.go")])
    assert not check_bundle_consumers.in_scope("go", [RelPath("rust/src/lib.rs")])
    assert check_bundle_consumers.in_scope("cpp", [RelPath("cpp/include/aletheia/ltl.hpp")])
    assert check_bundle_consumers.in_scope("rust", [RelPath("shake/Rules/Dist.hs")])


def test_the_rust_consumer_builds_against_the_crate_as_staged(tmp_path: Path) -> None:
    """The staged crate carries the staged manifest, and the consumer depends on it by path."""
    steps = check_bundle_consumers.rust_steps(tmp_path)
    crate = tmp_path / "bindings" / "rust"
    assert "example" not in tomllib.loads((crate / "Cargo.toml").read_text(encoding="utf-8"))
    assert (crate / "Cargo.lock").is_file()
    assert (crate / "src" / "lib.rs").is_file()
    consumer = tomllib.loads(
        (tmp_path / "consumer_rust" / "Cargo.toml").read_text(encoding="utf-8")
    )
    assert consumer["dependencies"] == {"aletheia": {"path": str(crate)}}
    lock = (crate / "Cargo.lock").read_bytes()
    assert (tmp_path / "consumer_rust" / "Cargo.lock").read_bytes() == lock
    assert [(step.argv[1:], step.cwd) for step in steps] == [
        (["check", "--locked"], crate),
        (["check"], tmp_path / "consumer_rust"),
    ]


def test_the_go_consumer_builds_against_the_tree_s_module(tmp_path: Path) -> None:
    """The consumer imports go.mod's module, which the module of its own replaces with go/."""
    module = check_bundle_consumers.go_module()
    steps = check_bundle_consumers.go_steps(tmp_path)
    source = (tmp_path / "consumer_go" / "main.go").read_text(encoding="utf-8")
    assert f'"{module}/aletheia"' in source
    words = [word for step in steps for word in step.argv[1:]]
    assert f"-replace={module}={_REPO / 'go'}" in words
    assert steps[-1].argv[1] == "build"


def test_the_cpp_consumer_is_checked_against_the_tree_s_headers(tmp_path: Path) -> None:
    """One syntax-only compile of the consumer, the tree's include directory first on its path."""
    (step,) = check_bundle_consumers.cpp_steps(tmp_path)
    assert "-fsyntax-only" in step.argv
    assert "-std=c++23" in step.argv
    assert f"-I{_REPO / 'cpp' / 'include'}" in step.argv
    assert step.argv[-1].endswith("tools/bundle_validation/consumer_cpp/main.cpp")


def test_every_sweep_builds_each_consumer_in_its_binding_s_lane(tmp_path: Path) -> None:
    """The three consumer steps and the installed package's, each in its lane."""
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    steps = {step.name: step for step in runner.registered_steps}
    for binding, lane in (("go", "misc"), ("cpp", "cpp"), ("rust", "rust")):
        step = steps[f"check-bundle-consumer-{binding}"]
        assert step.cmd == [
            runner.python,
            "-m",
            "tools.check_bundle_consumers",
            "--binding",
            binding,
        ]
        assert step.lane == lane
    installed = steps["check-cpp-installed-consumer"]
    assert installed.lane == "cpp"
    assert CPP_CONFIGURE_STEP in installed.needs


def _changes_elsewhere(_root: Path) -> list[RelPath]:
    """Answer the changes of a branch moving a document alone."""
    return [RelPath("docs/x.md")]


def test_a_branch_reaching_no_consumer_builds_nothing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Out of scope, the gate says so and exits 0 without staging anything."""
    monkeypatch.setattr(check_bundle_consumers, "branch_changes", _changes_elsewhere)
    for binding in check_bundle_consumers.BINDINGS:
        assert check_bundle_consumers.main([CommandWord("--binding"), CommandWord(binding)]) == 0
