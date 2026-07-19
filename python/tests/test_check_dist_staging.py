# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_dist_staging`` — the always-on release bundle-staging gate.

The gate exists because ``cabal run shake -- dist`` exercises its inputs only
at release time: a renamed pathspec target, a dead ``:(exclude)`` glob (which
``git archive`` passes over SILENTLY), a leaked ``go.work``, or a broken
``packaging/`` entry script would otherwise surface — or ship — when a tag is
cut.  Per the gate-teeth rule, every test here proves a failure mode actually
fails: each broken staging input exits non-zero, and each unparseable /
misconfigured input is COULD-NOT-CHECK, never a hollow pass.

Forward-revert verified empirically 2026-07-19 against the real repository via
the ``--shakefile`` seam (doctored COPIES of ``Shakefile.hs`` — the real file
was never modified): a renamed positive pathspec, a dead exclude glob, and go
positives widened to select ``go/go.work`` each exit 1 naming the input; a
multiline-gap string literal exits 2 as a refused partial parse; the untouched
tree exits 0.
"""

from __future__ import annotations

import shutil
from typing import TYPE_CHECKING

import pytest

from tools._common import find_executable, run_capture
from tools.check_dist_staging import COULD_NOT_CHECK, main, parse_stage_bindings

if TYPE_CHECKING:
    from pathlib import Path

# Mirrors the real Shakefile's call-site shape, including the local definition
# lines the call-site regex must skip (no quoted argument on them).
GOOD_SHAKEFILE = """\
-- minimal staging fixture mirroring the real Shakefile's call-site shape
main :: IO ()
main = do
        let stageBinding :: String -> [String] -> Action ()
            stageBinding name paths = do
                pure ()
        stageBinding "python"
            [ "python/pyproject.toml" ]
        stageBinding "cpp"
            [ "cpp/CMakeLists.txt" ]
        stageBinding "go"
            [ "go/go.mod", "go/aletheia"
            , ":(exclude)go/aletheia/*_test.go", ":(exclude)go/aletheia/testdata" ]
        stageBinding "rust"
            [ "rust/Cargo.toml" ]
"""

# One tracked file per fixture pathspec target, plus the packaging scripts
# (syntax-valid) and the license file.
GOOD_FILES: dict[str, str] = {
    "python/pyproject.toml": "[project]\n",
    "cpp/CMakeLists.txt": "cmake_minimum_required(VERSION 3.25)\n",
    "go/go.mod": "module example.com/aletheia\n",
    "go/aletheia/client.go": "package aletheia\n",
    "go/aletheia/client_test.go": "package aletheia\n",
    "go/aletheia/testdata/fixture.txt": "fixture\n",
    "rust/Cargo.toml": "[package]\n",
    "packaging/env.sh": 'export ALETHEIA_LIB="/tmp/lib"\n',
    "packaging/env.fish": "set -gx ALETHEIA_LIB /tmp/lib\n",
    "packaging/install.sh": 'echo "install"\n',
    "packaging/install.fish": 'echo "install"\n',
    "LICENSE.md": "BSD-2-Clause\n",
}


def _repo(tmp_path: Path, files: dict[str, str], skip_add: tuple[str, ...] = ()) -> Path:
    """Create a temp git repo containing ``files``, adding all but ``skip_add``."""
    repo = tmp_path / "repo"
    for rel, content in files.items():
        path = repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text(content, encoding="utf-8")
    git = find_executable("git")
    _ = run_capture([git, "init", "-q"], cwd=repo, check=True)
    to_add = [rel for rel in files if rel not in skip_add]
    _ = run_capture([git, "add", "--", *to_add], cwd=repo, check=True)
    return repo


def _write_shakefile(tmp_path: Path, text: str = GOOD_SHAKEFILE) -> Path:
    """Write a fixture Shakefile and return its path."""
    shakefile = tmp_path / "Shakefile.hs"
    _ = shakefile.write_text(text, encoding="utf-8")
    return shakefile


def _run(monkeypatch: pytest.MonkeyPatch, shakefile: Path, repo: Path, *extra: str) -> int:
    """Invoke the gate's ``main`` against the fixture via its DI seams.

    Clears ``GITHUB_ACTIONS`` so the fish policy behaves identically on a CI
    runner and a dev box; the CI fail-closed branch has its own test.
    """
    monkeypatch.delenv("GITHUB_ACTIONS", raising=False)
    monkeypatch.setattr(
        "sys.argv",
        ["check_dist_staging", "--shakefile", str(shakefile), "--repo-root", str(repo), *extra],
    )
    return main()


def test_parse_extracts_positives_and_excludes() -> None:
    """The parser reads each call site's name, positives, and exclude inner globs."""
    bindings = {b.name: b for b in parse_stage_bindings(GOOD_SHAKEFILE)}
    assert set(bindings) == {"python", "cpp", "go", "rust"}
    assert bindings["go"].positives == ("go/go.mod", "go/aletheia")
    assert bindings["go"].excludes == ("go/aletheia/*_test.go", "go/aletheia/testdata")
    assert bindings["rust"].positives == ("rust/Cargo.toml",)
    assert bindings["rust"].excludes == ()


def test_fixture_happy_path_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A fixture repo satisfying every check exits 0 (the teeth tests perturb THIS)."""
    repo = _repo(tmp_path, GOOD_FILES)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 0


def test_real_tree_passes(monkeypatch: pytest.MonkeyPatch) -> None:
    """The gate passes against the actual repository (default paths)."""
    monkeypatch.delenv("GITHUB_ACTIONS", raising=False)
    monkeypatch.setattr("sys.argv", ["check_dist_staging"])
    assert main() == 0


def test_no_stage_binding_blocks_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a Shakefile with no stageBinding call sites is COULD-NOT-CHECK."""
    repo = _repo(tmp_path, GOOD_FILES)
    shakefile = _write_shakefile(tmp_path, "main :: IO ()\nmain = pure ()\n")
    assert _run(monkeypatch, shakefile, repo) == COULD_NOT_CHECK
    assert "stageBinding" in capsys.readouterr().err


def test_partial_parse_multiline_gap_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a string the scanner cannot capture (Haskell gap syntax) exits 2.

    The residual hazard of literal-parsing Haskell is a PARTIAL parse — a
    literal the extractor misses while the rest still checks green.  The gate
    must refuse the whole read instead.
    """
    gapped = GOOD_SHAKEFILE.replace('"rust/Cargo.toml"', '"rust/\\\n            \\Cargo.toml"')
    assert gapped != GOOD_SHAKEFILE  # the replace really rewrote the fixture
    repo = _repo(tmp_path, GOOD_FILES)
    assert _run(monkeypatch, _write_shakefile(tmp_path, gapped), repo) == COULD_NOT_CHECK
    assert "rust" in capsys.readouterr().err


def test_unknown_pathspec_magic_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: pathspec magic the gate does not model is COULD-NOT-CHECK."""
    doctored = GOOD_SHAKEFILE.replace(":(exclude)go/aletheia/testdata", ":!go/aletheia/testdata")
    assert doctored != GOOD_SHAKEFILE
    repo = _repo(tmp_path, GOOD_FILES)
    assert _run(monkeypatch, _write_shakefile(tmp_path, doctored), repo) == COULD_NOT_CHECK
    assert "magic" in capsys.readouterr().err


def test_missing_shakefile_could_not_check(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a missing Shakefile is COULD-NOT-CHECK, never a silent pass."""
    repo = _repo(tmp_path, GOOD_FILES)
    assert _run(monkeypatch, tmp_path / "absent.hs", repo) == COULD_NOT_CHECK


def test_repo_root_not_a_git_repo_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """TEETH: a repo root git cannot query is COULD-NOT-CHECK, not an empty match."""
    not_a_repo = tmp_path / "plain-dir"
    not_a_repo.mkdir()
    assert _run(monkeypatch, _write_shakefile(tmp_path), not_a_repo) == COULD_NOT_CHECK


def test_untracked_positive_path_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a positive pathspec matching no tracked file fails, naming binding+spec."""
    repo = _repo(tmp_path, GOOD_FILES, skip_add=("rust/Cargo.toml",))
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    err = capsys.readouterr().err
    assert "'rust'" in err
    assert "rust/Cargo.toml" in err


def test_dead_exclude_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: an exclude glob matching no tracked file fails — git archive would not.

    This is the gate's new coverage: empirically ``git archive`` passes
    silently over a dead exclude, so the files it was meant to keep out would
    silently ship.
    """
    doctored = GOOD_SHAKEFILE.replace("*_test.go", "*_moved_test.go")
    assert doctored != GOOD_SHAKEFILE
    repo = _repo(tmp_path, GOOD_FILES)
    assert _run(monkeypatch, _write_shakefile(tmp_path, doctored), repo) == 1
    err = capsys.readouterr().err
    assert ":(exclude)go/aletheia/*_moved_test.go" in err


def test_go_work_selected_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: go positives that select go/go.work fail (module-resolution hijack)."""
    doctored = GOOD_SHAKEFILE.replace('"go/go.mod", "go/aletheia"', '"go"')
    assert doctored != GOOD_SHAKEFILE
    repo = _repo(tmp_path, {**GOOD_FILES, "go/go.work": "go 1.26\n"})
    assert _run(monkeypatch, _write_shakefile(tmp_path, doctored), repo) == 1
    assert "go.work" in capsys.readouterr().err


def test_bash_syntax_error_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a packaging .sh script that fails ``bash -n`` fails the gate."""
    files = {**GOOD_FILES, "packaging/install.sh": "if [ -z broken ]; then\n"}
    repo = _repo(tmp_path, files)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    err = capsys.readouterr().err
    assert "install.sh" in err
    assert "syntax" in err


@pytest.mark.skipif(shutil.which("fish") is None, reason="fish not installed")
def test_fish_syntax_error_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a packaging .fish script that fails ``fish --no-execute`` fails the gate."""
    files = {**GOOD_FILES, "packaging/env.fish": "if true\n"}
    repo = _repo(tmp_path, files)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    err = capsys.readouterr().err
    assert "env.fish" in err
    assert "syntax" in err


def test_untracked_packaging_script_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a packaging script present on disk but untracked fails.

    dist copies the script from the worktree, but a release runs on a clean
    checkout, which only has tracked files — so untracked means broken there.
    """
    repo = _repo(tmp_path, GOOD_FILES, skip_add=("packaging/env.sh",))
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    err = capsys.readouterr().err
    assert "env.sh" in err
    assert "not git-tracked" in err


def test_untracked_license_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: an untracked LICENSE.md fails — dist ships it with the bundle."""
    repo = _repo(tmp_path, GOOD_FILES, skip_add=("LICENSE.md",))
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    assert "LICENSE.md" in capsys.readouterr().err


def test_fish_absent_on_ci_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: no fish + GITHUB_ACTIONS set = COULD-NOT-CHECK (runner misconfiguration)."""
    repo = _repo(tmp_path, GOOD_FILES)
    shakefile = _write_shakefile(tmp_path)
    monkeypatch.setattr("tools.check_dist_staging.find_fish", lambda: None)
    monkeypatch.setenv("GITHUB_ACTIONS", "true")
    monkeypatch.setattr(
        "sys.argv",
        ["check_dist_staging", "--shakefile", str(shakefile), "--repo-root", str(repo)],
    )
    assert main() == COULD_NOT_CHECK
    assert "fish" in capsys.readouterr().err


def test_fish_absent_with_require_flag_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """TEETH: no fish + --require-fish = COULD-NOT-CHECK even off CI."""
    repo = _repo(tmp_path, GOOD_FILES)
    monkeypatch.setattr("tools.check_dist_staging.find_fish", lambda: None)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo, "--require-fish") == COULD_NOT_CHECK


def test_fish_absent_locally_skips_loudly(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """No fish off CI: the .fish syntax checks skip with a printed notice, rest runs."""
    repo = _repo(tmp_path, GOOD_FILES)
    monkeypatch.setattr("tools.check_dist_staging.find_fish", lambda: None)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 0
    out = capsys.readouterr().out
    assert "skipping" in out
    assert "fish absent" in out
