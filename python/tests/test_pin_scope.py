# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A pin gate runs when the branch moves what its fact rests on, and wherever that cannot be read.

``tools/pin_scope.py`` answers, for each gate holding a fact about an exactly
pinned tool, whether the branch moved the pin's line, a file the fact is about,
the gate itself or the scoping.  The branch's diff is replaced here by one the
test writes, so each answer is held without a repository; the table's paths are
held to the tree, since a scope naming a path nothing tracks can never fire.
"""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

import pytest

from tools import pin_scope
from tools._branch_diff import DiffText, GitDiffOption
from tools._common import RelPath, git_ls_files
from tools.pin_scope import PIN_SCOPES, PinGate, changed_lines, gate_runs, pin_change

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

_ROOT = Path("/repo")
_REPO = Path(__file__).resolve().parents[2]
# The variable a reader sets to run every gate, by the name the docs give it.
_RUN_ALL = "ALETHEIA_PIN_GATES_RUN"


class _Asked(NamedTuple):
    """One reading of the branch's lines: the options git was given and the paths it read."""

    options: tuple[GitDiffOption, ...]
    paths: tuple[RelPath, ...]


def _hunk(path: RelPath, removed: Prose, added: Prose) -> DiffText:
    """Return a zero-context diff of one line of ``path`` replaced."""
    return DiffText(
        f"diff --git a/{path} b/{path}\n--- a/{path}\n+++ b/{path}\n"
        + f"@@ -5 +5 @@\n-{removed}\n+{added}\n"
    )


_WORKFLOWS = (RelPath(".github/workflows/a.yml"), RelPath(".github/workflows/b.yml"))
_AGDA_BUMP = _hunk(
    _WORKFLOWS[0], Prose("      AGDA_VERSION: '2.8.0'"), Prose("      AGDA_VERSION: '2.9.0'")
)
_AGDA_MENTION = _hunk(
    _WORKFLOWS[0],
    Prose("          key: agda${{ env.AGDA_VERSION }}-v3"),
    Prose("          key: agda${{ env.AGDA_VERSION }}-v4"),
)
_CMAKE = RelPath("cpp/CMakeLists.txt")
_JSON_BUMP = _hunk(
    _CMAKE,
    Prose("    URL https://github.com/nlohmann/json/releases/download/v3.12.0/json.tar.xz"),
    Prose("    URL https://github.com/nlohmann/json/releases/download/v3.13.0/json.tar.xz"),
)
_OTHER_BUMP = _hunk(
    _CMAKE,
    Prose("    URL https://github.com/jbeder/yaml-cpp/archive/refs/tags/0.8.0.tar.gz"),
    Prose("    URL https://github.com/jbeder/yaml-cpp/archive/refs/tags/0.9.0.tar.gz"),
)
_PREFIX_MAP_MOVE = _hunk(
    _CMAKE,
    Prose('        "-ffile-prefix-map=${CMAKE_SOURCE_DIR}=.")'),
    Prose('        "-ffile-prefix-map=${CMAKE_SOURCE_DIR}=src")'),
)
_BENCH = RelPath("docs/MUTATION_BENCH.yaml")
_CARGO_MUTANTS_BUMP = _hunk(_BENCH, Prose('    version: "27.1.0"'), Prose('    version: "27.2.0"'))
# The other two tools' releases in the same record: mutmut's carries its `==`,
# Mull's the LLVM it is built against.
_OTHER_RELEASE_BUMPS = DiffText(
    _hunk(_BENCH, Prose('    version: "==3.8.0"'), Prose('    version: "==3.9.0"'))
    + _hunk(_BENCH, Prose('    version: "0.34.1 LLVM-23"'), Prose('    version: "0.35.0 LLVM-23"'))
)
_PYPROJECT = RelPath("python/pyproject.toml")
_MUTMUT_BUMP = _hunk(
    _PYPROJECT, Prose('mutation = ["mutmut==3.8.0"]'), Prose('mutation = ["mutmut==3.9.0"]')
)
_PLUGIN_PATCH = RelPath("tools/mull/libirm-void-call-mutator.patch")


def _branch(
    monkeypatch: pytest.MonkeyPatch,
    changed: list[RelPath] | None,
    diffs: Mapping[RelPath, DiffText | None] | None = None,
) -> list[_Asked]:
    """Make the branch change ``changed``, each path's lines as ``diffs`` gives; return the asks."""
    asked: list[_Asked] = []

    def changes(root: Path) -> list[RelPath] | None:
        assert root == _ROOT
        return changed

    def diff(
        root: Path, *options: GitDiffOption, paths: tuple[RelPath, ...] = ()
    ) -> DiffText | None:
        assert root == _ROOT
        asked.append(_Asked(options, paths))
        given = [(diffs or {}).get(path, DiffText("")) for path in paths]
        if any(text is None for text in given):
            return None
        return DiffText("".join(text or "" for text in given))

    monkeypatch.delenv(_RUN_ALL, raising=False)
    monkeypatch.setattr(pin_scope, "branch_changes", changes)
    monkeypatch.setattr(pin_scope, "branch_diff", diff)
    return asked


def test_a_changed_line_is_read_inside_a_hunk_only() -> None:
    """File headers are not changed lines, and a removed line opening on ``--`` still is one."""
    diff = DiffText(
        "diff --git a/x b/x\n--- a/x\n+++ b/x\n@@ -1,2 +1 @@\n--- a comment\n-old\n+new\n"
        + "\\ No newline at end of file\n"
        + "diff --git a/y b/y\n--- a/y\n+++ b/y\n"
    )
    assert list(changed_lines(diff)) == [Prose("-- a comment"), Prose("old"), Prose("new")]


def test_a_moved_pin_line_runs_the_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    """A workflow moving the Agda release re-arms the Agda gate, read with no context or colour."""
    asked = _branch(monkeypatch, [*_WORKFLOWS, RelPath("docs/A.md")], {_WORKFLOWS[0]: _AGDA_BUMP})
    assert pin_change(PinGate.AGDA_INTERFACE_REUSE, _ROOT) == Prose(
        "the branch moves \"AGDA_VERSION: '2.8.0'\" in"
        + " .github/workflows/a.yml, .github/workflows/b.yml"
    )
    assert asked == [_Asked((GitDiffOption("-U0"), GitDiffOption("--no-color")), _WORKFLOWS)]


def test_a_line_only_naming_the_pin_leaves_the_gate_out(monkeypatch: pytest.MonkeyPatch) -> None:
    """A workflow edit that moves no release is not the Agda gate's business."""
    _ = _branch(monkeypatch, [_WORKFLOWS[0]], {_WORKFLOWS[0]: _AGDA_MENTION})
    assert pin_change(PinGate.AGDA_INTERFACE_REUSE, _ROOT) is None


def test_the_json_library_s_release_line_runs_its_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    """The JSON library's fetch line moving re-arms its gate; another library's does not."""
    _ = _branch(monkeypatch, [_CMAKE], {_CMAKE: _JSON_BUMP})
    assert pin_change(PinGate.JSON_CLEANUP_ABORT, _ROOT) is not None
    _ = _branch(monkeypatch, [_CMAKE], {_CMAKE: _OTHER_BUMP})
    assert pin_change(PinGate.JSON_CLEANUP_ABORT, _ROOT) is None


def test_the_cargo_mutants_release_line_runs_its_gate_and_the_other_releases_do_not(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Of the three releases the bench record pins, only cargo-mutants' is a bare version."""
    _ = _branch(monkeypatch, [_BENCH], {_BENCH: _CARGO_MUTANTS_BUMP})
    assert pin_change(PinGate.CARGO_MUTANTS_SHARDS, _ROOT) == Prose(
        "the branch moves 'version: \"27.1.0\"' in docs/MUTATION_BENCH.yaml"
    )
    _ = _branch(monkeypatch, [_BENCH], {_BENCH: _OTHER_RELEASE_BUMPS})
    assert pin_change(PinGate.CARGO_MUTANTS_SHARDS, _ROOT) is None


def test_the_mutmut_pin_runs_its_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    """The [mutation] extra's exact pin moving re-arms the mutmut gate."""
    _ = _branch(monkeypatch, [_PYPROJECT], {_PYPROJECT: _MUTMUT_BUMP})
    assert pin_change(PinGate.MUTMUT_OPERATORS, _ROOT) == Prose(
        "the branch moves 'mutation = [\"mutmut==3.8.0\"]' in python/pyproject.toml"
    )


def test_the_prefix_map_line_runs_the_plugin_gate_and_another_line_does_not(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The flag the build withholds from the plugin is the plugin gate's line in the build file."""
    _ = _branch(monkeypatch, [_CMAKE], {_CMAKE: _PREFIX_MAP_MOVE})
    assert pin_change(PinGate.MULL_PLUGIN_FACTS, _ROOT) is not None
    _ = _branch(monkeypatch, [_CMAKE], {_CMAKE: _OTHER_BUMP})
    assert pin_change(PinGate.MULL_PLUGIN_FACTS, _ROOT) is None


def test_a_plugin_patch_runs_both_gates_on_the_plugin(monkeypatch: pytest.MonkeyPatch) -> None:
    """What the plugin emits and which mutants a slice carries both rest on its patches."""
    _ = _branch(monkeypatch, [_PLUGIN_PATCH])
    for gate in (PinGate.MULL_PLUGIN_FACTS, PinGate.CPP_SLICES_CENSUS):
        assert pin_change(gate, _ROOT) == Prose(f"the branch changes {_PLUGIN_PATCH}")


def test_lines_git_cannot_give_run_the_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    """A pin's file changed and its lines unreadable is never a reason to skip."""
    _ = _branch(monkeypatch, [_WORKFLOWS[0]], {_WORKFLOWS[0]: None})
    assert pin_change(PinGate.AGDA_INTERFACE_REUSE, _ROOT) == Prose(
        "git cannot give the lines the branch changed in .github/workflows/a.yml"
    )


def test_a_file_scoped_whole_runs_the_gate_on_any_change(monkeypatch: pytest.MonkeyPatch) -> None:
    """Any change to the configuration a fact is about re-arms its gate."""
    _ = _branch(monkeypatch, [RelPath("cpp/.clang-tidy")])
    assert pin_change(PinGate.CLANG_TIDY_FACTS, _ROOT) == Prose(
        "the branch changes cpp/.clang-tidy"
    )


def test_a_branch_touching_nothing_a_gate_rests_on_leaves_it_out(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Another gate's configuration, or a document, moves none of this one's facts."""
    _ = _branch(monkeypatch, [RelPath("cpp/.clang-tidy"), RelPath("docs/README.md")])
    assert pin_change(PinGate.JSON_CLEANUP_ABORT, _ROOT) is None


@pytest.mark.parametrize("module", ["tools/_branch_diff.py", "tools/pin_scope.py"])
def test_a_change_to_the_scoping_runs_every_gate(
    monkeypatch: pytest.MonkeyPatch, module: RelPath
) -> None:
    """How a gate is scoped is something every gate rests on."""
    _ = _branch(monkeypatch, [RelPath(module)])
    for gate in PinGate:
        assert pin_change(gate, _ROOT) == Prose(f"the branch changes {module}")


def test_a_diff_git_cannot_give_runs_the_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    """No diff to read is never a reason to skip."""
    _ = _branch(monkeypatch, None)
    assert pin_change(PinGate.AGDA_INTERFACE_REUSE, _ROOT) == Prose(
        "git cannot give the branch's diff against main"
    )


def test_an_empty_branch_runs_the_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    """A push to main changes nothing against main, and is the run every gate backs."""
    _ = _branch(monkeypatch, [])
    assert pin_change(PinGate.CLANG_TIDY_FACTS, _ROOT) == Prose(
        "the branch changes nothing against main, which is the backstop run"
    )


def test_the_escape_variable_runs_the_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    """Set to 1, every gate runs whatever the branch moved; any other value leaves the scope."""
    _ = _branch(monkeypatch, [RelPath("docs/README.md")])
    monkeypatch.setenv(_RUN_ALL, "1")
    assert pin_change(PinGate.JSON_CLEANUP_ABORT, _ROOT) == Prose(f"{_RUN_ALL}=1")
    monkeypatch.setenv(_RUN_ALL, "0")
    assert pin_change(PinGate.JSON_CLEANUP_ABORT, _ROOT) is None


def test_the_decision_is_said_either_way(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The log of a run states whether each gate ran, why, and what it rests on."""
    _ = _branch(monkeypatch, [RelPath("docs/README.md")])
    assert gate_runs(PinGate.CLANG_TIDY_FACTS, _ROOT) is False
    assert capsys.readouterr().err == (
        "[pin] clang-tidy-facts: the branch moves nothing it rests on (cpp/toolchain/"
        + "check_upstream.sh, cpp/.clang-tidy, tools/check_clang_tidy_facts.py),"
        + " so it does not run\n"
    )
    _ = _branch(monkeypatch, [RelPath("cpp/.clang-tidy")])
    assert gate_runs(PinGate.CLANG_TIDY_FACTS, _ROOT) is True
    assert capsys.readouterr().err == (
        "[pin] clang-tidy-facts: runs, since the branch changes cpp/.clang-tidy\n"
    )


def test_each_gate_is_named_in_the_log_as_its_step_is() -> None:
    """A gate's log name is its run_ci step's name without the ``check-`` prefix."""
    assert [gate.value for gate in PinGate] == [
        "agda-interface-reuse",
        "cargo-mutants-shards",
        "clang-tidy-facts",
        "cpp-slices-census",
        "json-cleanup-abort",
        "mull-plugin-facts",
        "mutmut-operators",
    ]


def test_every_gate_has_a_scope() -> None:
    """A gate the table forgot would raise rather than run."""
    assert set(PIN_SCOPES) == set(PinGate)


@pytest.mark.process("which paths the tree tracks is git's own answer, not a glob of the work tree")
def test_every_scope_names_a_tracked_path() -> None:
    """A scope naming a path nothing tracks can never re-arm its gate."""
    tracked = set(git_ls_files(_REPO))

    def is_tracked(path: RelPath) -> bool:
        if path.endswith("/"):
            return any(file.startswith(path) for file in tracked)
        return path in tracked

    scoped = {scope.path for scopes in PIN_SCOPES.values() for scope in scopes}
    untracked = {path for path in scoped if not is_tracked(path)}
    assert sorted(untracked) == []


def test_a_line_before_any_hunk_is_not_content() -> None:
    """Text ahead of the first hunk is not a changed line, whatever sign it opens on."""
    assert not list(changed_lines(DiffText("+stray\n-also stray\n")))


def test_every_file_a_scope_touches_is_named(monkeypatch: pytest.MonkeyPatch) -> None:
    """A reason names each file the branch moved under the scope, in the diff's order."""
    _ = _branch(monkeypatch, [*_WORKFLOWS], {_WORKFLOWS[0]: None, _WORKFLOWS[1]: None})
    assert pin_change(PinGate.AGDA_INTERFACE_REUSE, _ROOT) == Prose(
        "git cannot give the lines the branch changed in"
        + " .github/workflows/a.yml, .github/workflows/b.yml"
    )
    whole_directory = {gate: (pin_scope.PinScope(RelPath("conf/")),) for gate in PinGate}
    monkeypatch.setattr(pin_scope, "PIN_SCOPES", whole_directory)
    _ = _branch(monkeypatch, [RelPath("conf/a"), RelPath("conf/b")])
    assert pin_change(PinGate.CLANG_TIDY_FACTS, _ROOT) == Prose("the branch changes conf/a, conf/b")
