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

A test starts only the processes its claim rests on: git where the claim is
the index's answer, bash and fish where it is a script's syntax.  The checks a
claim does not judge answer through stand-ins, and a stand-in that must never
be reached raises ``AssertionError``, which the gate does not catch.
"""

from __future__ import annotations

import io
import shutil
import subprocess
from pathlib import Path
from typing import TYPE_CHECKING, NoReturn

import pytest

from tools._common import find_executable, read_shake_program, run_capture
from tools.check_dist_staging import (
    COULD_NOT_CHECK,
    find_fish,
    main,
    parse_stage_bindings,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from _processes import CommandWord

# Mirrors the dist rule's call-site shape, including the local definition
# lines the call-site regex must skip (no quoted argument on them).
GOOD_SHAKEFILE = """\
-- minimal staging fixture mirroring the dist rule's call-site shape
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
GOOD_FILES = {
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


def _write_files(tmp_path: Path, files: dict[str, str]) -> Path:
    """Write ``files`` under ``tmp_path / "repo"``, with no git, and return that directory."""
    repo = tmp_path / "repo"
    for rel, content in files.items():
        path = repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text(content, encoding="utf-8")
    return repo


def _repo(tmp_path: Path, files: dict[str, str], skip_add: tuple[str, ...] = ()) -> Path:
    """Create a temp git repo containing ``files``, adding all but ``skip_add``."""
    repo = _write_files(tmp_path, files)
    git = find_executable("git")
    _ = run_capture([git, "init", "-q"], cwd=repo, check=True)
    to_add = [rel for rel in files if rel not in skip_add]
    _ = run_capture([git, "add", "--", *to_add], cwd=repo, check=True)
    return repo


def _write_shakefile(tmp_path: Path, text: str = GOOD_SHAKEFILE) -> Path:
    """Write a fixture build program, its Shakefile.hs alone, and return the directory."""
    _ = (tmp_path / "Shakefile.hs").write_text(text, encoding="utf-8")
    return tmp_path


def _run(monkeypatch: pytest.MonkeyPatch, build_root: Path, repo: Path, *extra: str) -> int:
    """Invoke the gate's ``main`` against the fixture via its DI seams.

    Clears ``GITHUB_ACTIONS`` so the fish policy behaves identically on a CI
    runner and a dev box; the CI fail-closed branch has its own test.
    """
    monkeypatch.delenv("GITHUB_ACTIONS", raising=False)
    monkeypatch.setattr(
        "sys.argv",
        ["check_dist_staging", "--build-root", str(build_root), "--repo-root", str(repo), *extra],
    )
    return main()


def _skip_script_checks(
    monkeypatch: pytest.MonkeyPatch,
) -> list[tuple[Path, CommandWord | None]]:
    """Answer the packaging-script check with no failure and no shell; return its calls."""
    calls: list[tuple[Path, CommandWord | None]] = []

    def no_script_failure(repo_root: Path, fish: CommandWord | None) -> list[Prose]:
        calls.append((repo_root, fish))
        return []

    monkeypatch.setattr("tools.check_dist_staging.check_packaging_scripts", no_script_failure)
    return calls


def _every_pathspec_tracked(
    _repo_root: Path, pathspecs: tuple[CommandWord, ...]
) -> list[CommandWord]:
    """Answer ``git ls-files`` as if each pathspec matched one tracked file, itself."""
    return list(pathspecs)


def _refuse_git(monkeypatch: pytest.MonkeyPatch) -> None:
    """Make any ``git ls-files`` query fail the test, past the gate's own except clause."""

    def git_queried(_repo_root: Path, _pathspecs: tuple[CommandWord, ...]) -> NoReturn:
        message = "git queried before the refusal"
        raise AssertionError(message)

    monkeypatch.setattr("tools.check_dist_staging.git_ls_files", git_queried)


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


def test_call_sites_in_a_module_under_shake_are_read(tmp_path: Path) -> None:
    """The call sites of a module under ``shake/`` parse to the bindings they would in the main.

    A path moved in that module is the path the checks receive.
    """
    build_root = _write_shakefile(tmp_path, "main :: IO ()\nmain = distRules\n")
    rules = build_root / "shake" / "Rules"
    rules.mkdir(parents=True)
    _ = (rules / "Dist.hs").write_text(GOOD_SHAKEFILE, encoding="utf-8")
    assert parse_stage_bindings(read_shake_program(build_root)) == parse_stage_bindings(
        GOOD_SHAKEFILE
    )
    moved_text = GOOD_SHAKEFILE.replace('"rust/Cargo.toml"', '"rust/Moved.toml"')
    assert moved_text != GOOD_SHAKEFILE
    _ = (rules / "Dist.hs").write_text(moved_text, encoding="utf-8")
    moved = parse_stage_bindings(read_shake_program(build_root))
    assert moved == parse_stage_bindings(moved_text)
    assert {b.name: b for b in moved}["rust"].positives == ("rust/Moved.toml",)


def test_real_tree_passes(monkeypatch: pytest.MonkeyPatch) -> None:
    """The gate passes against the actual repository (default paths)."""
    monkeypatch.delenv("GITHUB_ACTIONS", raising=False)
    monkeypatch.setattr("sys.argv", ["check_dist_staging"])
    assert main() == 0


def test_no_stage_binding_blocks_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a build program with no stageBinding call sites is COULD-NOT-CHECK, before git."""
    _refuse_git(monkeypatch)
    build_root = _write_shakefile(tmp_path, "main :: IO ()\nmain = pure ()\n")
    assert _run(monkeypatch, build_root, tmp_path / "unused") == COULD_NOT_CHECK
    assert "stageBinding" in capsys.readouterr().err


def test_partial_parse_multiline_gap_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a string the scanner cannot capture (Haskell gap syntax) exits 2, before git.

    The residual hazard of literal-parsing Haskell is a PARTIAL parse — a
    literal the extractor misses while the rest still checks green.  The gate
    must refuse the whole read instead.
    """
    gapped = GOOD_SHAKEFILE.replace('"rust/Cargo.toml"', '"rust/\\\n            \\Cargo.toml"')
    assert gapped != GOOD_SHAKEFILE  # the replace really rewrote the fixture
    _refuse_git(monkeypatch)
    build_root = _write_shakefile(tmp_path, gapped)
    assert _run(monkeypatch, build_root, tmp_path / "unused") == COULD_NOT_CHECK
    assert "rust" in capsys.readouterr().err


def test_unknown_pathspec_magic_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: pathspec magic the gate does not model is COULD-NOT-CHECK, before git."""
    doctored = GOOD_SHAKEFILE.replace(":(exclude)go/aletheia/testdata", ":!go/aletheia/testdata")
    assert doctored != GOOD_SHAKEFILE
    _refuse_git(monkeypatch)
    build_root = _write_shakefile(tmp_path, doctored)
    assert _run(monkeypatch, build_root, tmp_path / "unused") == COULD_NOT_CHECK
    assert "magic" in capsys.readouterr().err


def test_missing_shakefile_could_not_check(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a missing build program is COULD-NOT-CHECK before git, never a silent pass."""
    _refuse_git(monkeypatch)
    assert _run(monkeypatch, tmp_path / "absent", tmp_path / "unused") == COULD_NOT_CHECK


def test_repo_root_not_a_git_repo_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """TEETH: a repo root git cannot query is COULD-NOT-CHECK, not an empty match.

    The stand-in answers the gate's first ``git ls-files`` as git answers it
    outside any repository: status 128 and its ``fatal:`` line.
    """
    not_a_repo = tmp_path / "plain-dir"
    not_a_repo.mkdir()
    asked: list[list[CommandWord]] = []
    asked_in: list[Path | None] = []

    def git_outside_a_repo(
        cmd: list[CommandWord], *, cwd: Path | None = None
    ) -> subprocess.CompletedProcess[Prose]:
        asked.append(cmd)
        asked_in.append(cwd)
        fatal = Prose("fatal: not a git repository (or any of the parent directories): .git\n")
        return subprocess.CompletedProcess(cmd, 128, Prose(""), fatal)

    monkeypatch.setattr("tools.check_dist_staging.run_capture", git_outside_a_repo)
    err = io.StringIO()
    monkeypatch.setattr("sys.stderr", err)
    assert _run(monkeypatch, _write_shakefile(tmp_path), not_a_repo) == COULD_NOT_CHECK
    assert asked == [[find_executable("git"), "ls-files", "--", "python/pyproject.toml"]]
    assert asked_in == [not_a_repo]
    assert "not a git repository" in err.getvalue()
    assert "matches no tracked file" not in err.getvalue()


def test_untracked_positive_path_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a positive pathspec matching no tracked file fails, naming binding+spec."""
    repo = _repo(tmp_path, GOOD_FILES, skip_add=("rust/Cargo.toml",))
    script_checks = _skip_script_checks(monkeypatch)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    err = capsys.readouterr().err
    assert "'rust'" in err
    assert "rust/Cargo.toml" in err
    assert script_checks == [(repo, find_fish())]


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
    script_checks = _skip_script_checks(monkeypatch)
    assert _run(monkeypatch, _write_shakefile(tmp_path, doctored), repo) == 1
    err = capsys.readouterr().err
    assert ":(exclude)go/aletheia/*_moved_test.go" in err
    assert script_checks == [(repo, find_fish())]


def test_go_work_selected_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: go positives that select go/go.work fail (module-resolution hijack)."""
    doctored = GOOD_SHAKEFILE.replace('"go/go.mod", "go/aletheia"', '"go"')
    assert doctored != GOOD_SHAKEFILE
    repo = _repo(tmp_path, {**GOOD_FILES, "go/go.work": "go 1.26\n"})
    script_checks = _skip_script_checks(monkeypatch)
    assert _run(monkeypatch, _write_shakefile(tmp_path, doctored), repo) == 1
    assert "go.work" in capsys.readouterr().err
    assert script_checks == [(repo, find_fish())]


def test_bash_syntax_error_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a packaging .sh script that fails ``bash -n`` is the gate's one failure."""
    files = {**GOOD_FILES, "packaging/install.sh": "if [ -z broken ]; then\n"}
    repo = _write_files(tmp_path, files)
    monkeypatch.setattr("tools.check_dist_staging.git_ls_files", _every_pathspec_tracked)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    err = capsys.readouterr().err
    assert "install.sh" in err
    assert "syntax" in err
    assert "found 1 broken" in err


@pytest.mark.skipif(shutil.which("fish") is None, reason="fish not installed")
def test_fish_syntax_error_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a .fish packaging script failing ``fish --no-execute`` is the gate's one failure."""
    files = {**GOOD_FILES, "packaging/env.fish": "if true\n"}
    repo = _write_files(tmp_path, files)
    monkeypatch.setattr("tools.check_dist_staging.git_ls_files", _every_pathspec_tracked)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    err = capsys.readouterr().err
    assert "env.fish" in err
    assert "syntax" in err
    assert "found 1 broken" in err


def test_untracked_packaging_script_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a packaging script present on disk but untracked fails, and is never checked.

    dist copies the script from the worktree, but a release runs on a clean
    checkout, which only has tracked files — so untracked means broken there.
    """
    repo = _repo(tmp_path, GOOD_FILES, skip_add=("packaging/env.sh",))
    checkers: list[list[CommandWord]] = []

    def git_alone_runs(
        cmd: list[CommandWord], *, cwd: Path | None = None
    ) -> subprocess.CompletedProcess[Prose]:
        if Path(cmd[0]).name == "git":
            done = run_capture([*cmd], cwd=cwd)
            return subprocess.CompletedProcess(
                cmd, done.returncode, Prose(done.stdout), Prose(done.stderr)
            )
        checkers.append(cmd)
        return subprocess.CompletedProcess(cmd, 0, Prose(""), Prose(""))

    monkeypatch.setattr("tools.check_dist_staging.run_capture", git_alone_runs)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    err = capsys.readouterr().err
    assert "env.sh" in err
    assert "not git-tracked" in err
    untracked = str(repo / "packaging/env.sh")
    assert all(untracked not in argv for argv in checkers)
    assert [find_executable("bash"), "-n", str(repo / "packaging/install.sh")] in checkers


def test_untracked_license_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: an untracked LICENSE.md fails — dist ships it with the bundle."""
    repo = _repo(tmp_path, GOOD_FILES, skip_add=("LICENSE.md",))
    script_checks = _skip_script_checks(monkeypatch)
    assert _run(monkeypatch, _write_shakefile(tmp_path), repo) == 1
    assert "LICENSE.md" in capsys.readouterr().err
    assert script_checks == [(repo, find_fish())]


def test_fish_absent_on_ci_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: no fish + GITHUB_ACTIONS set = COULD-NOT-CHECK (runner misconfiguration)."""
    _refuse_git(monkeypatch)
    build_root = _write_shakefile(tmp_path)
    monkeypatch.setattr("tools.check_dist_staging.find_fish", lambda: None)
    monkeypatch.setenv("GITHUB_ACTIONS", "true")
    monkeypatch.setattr(
        "sys.argv",
        [
            "check_dist_staging",
            "--build-root",
            str(build_root),
            "--repo-root",
            str(tmp_path / "unused"),
        ],
    )
    assert main() == COULD_NOT_CHECK
    assert "fish" in capsys.readouterr().err


def test_fish_absent_with_require_flag_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """TEETH: no fish + --require-fish = COULD-NOT-CHECK even off CI."""
    _refuse_git(monkeypatch)
    monkeypatch.setattr("tools.check_dist_staging.find_fish", lambda: None)
    build_root = _write_shakefile(tmp_path)
    unused = tmp_path / "unused"
    assert _run(monkeypatch, build_root, unused, "--require-fish") == COULD_NOT_CHECK


def test_fish_absent_locally_skips_loudly(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """No fish off CI: the .fish syntax checks skip with a printed notice, rest runs."""
    root = tmp_path / "repo"
    monkeypatch.setattr("tools.check_dist_staging.find_fish", lambda: None)
    monkeypatch.setattr("tools.check_dist_staging.git_ls_files", _every_pathspec_tracked)
    checkers: list[list[CommandWord]] = []

    def syntax_clean(cmd: list[CommandWord]) -> subprocess.CompletedProcess[Prose]:
        checkers.append(cmd)
        return subprocess.CompletedProcess(cmd, 0, Prose(""), Prose(""))

    monkeypatch.setattr("tools.check_dist_staging.run_capture", syntax_clean)
    assert _run(monkeypatch, _write_shakefile(tmp_path), root) == 0
    out = capsys.readouterr().out
    assert "skipping" in out
    assert "fish absent" in out
    bash = find_executable("bash")
    assert checkers == [
        [bash, "-n", str(root / "packaging/env.sh")],
        [bash, "-n", str(root / "packaging/install.sh")],
    ]
