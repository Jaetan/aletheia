# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Guards for the generated git-hook bodies in ``tools/install_hooks.py``.

The hook bodies are f-strings, so any literal ``{`` in the embedded shell / git
commands must be doubled (``{{``) or the f-string silently substitutes it.  A
``stash@{0}`` that rendered as ``stash@0`` once disabled the whole pre-commit
stash-restore path (an invalid git ref → no restore → lost unstaged work), and
``compile()`` does NOT catch it (``stash@0`` is valid string content).  Pin the
rendered bodies here.
"""

from __future__ import annotations

import importlib.util
import os
import re
import stat
import subprocess
import sys
from enum import Enum
from typing import TYPE_CHECKING, NamedTuple, NewType, cast

import pytest

from tools._common import find_executable
from tools.install_hooks import (
    PRE_COMMIT_BODY,
    PRE_COMMIT_SUMMARY,
    PRE_PUSH_BODY,
    PRE_PUSH_SUMMARY,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path


def test_hook_bodies_are_valid_python() -> None:
    """Both generated hook bodies compile (an f-string typo can break them)."""
    compile(PRE_COMMIT_BODY, "<pre-commit>", "exec")
    compile(PRE_PUSH_BODY, "<pre-push>", "exec")


# The Python source of a hook as the installer writes it.
HookSource = NewType("HookSource", str)


@pytest.mark.parametrize(
    ("body", "summary"),
    [
        (HookSource(PRE_COMMIT_BODY), Prose(PRE_COMMIT_SUMMARY)),
        (HookSource(PRE_PUSH_BODY), Prose(PRE_PUSH_SUMMARY)),
    ],
    ids=["pre-commit", "pre-push"],
)
def test_each_hook_s_summary_names_every_tool_its_body_runs(
    body: HookSource, summary: Prose
) -> None:
    """The line printed at install names each ``python -m tools.X`` the hook runs."""
    run = set(re.findall(r'"tools\.(\w+)"', body))
    assert run
    assert {tool for tool in run if f"tools/{tool}.py" not in summary} == set()


def test_pre_commit_stash_ref_survived_the_fstring() -> None:
    """The stash ref renders as ``stash@{0}`` — the f-string must not eat the braces.

    ``stash@{0}`` in an f-string body renders the ``{0}`` field as ``0`` unless
    doubled to ``{{0}}``; the resulting ``stash@0`` is an invalid git ref that
    silently disables the hook's stash restore. Compilation can't catch it.
    """
    assert "stash@{0}" in PRE_COMMIT_BODY
    assert "stash@0" not in PRE_COMMIT_BODY


def _load_pre_commit(tmp_path: Path) -> dict[str, object]:
    """Import the rendered pre-commit body as a module and return its namespace.

    The body guards ``main`` behind ``__main__``, so importing it runs nothing
    and yields a namespace whose entries a test can replace, ``_run`` included.
    """
    script = tmp_path / "pre_commit.py"
    script.write_text(PRE_COMMIT_BODY, encoding="utf-8")
    spec = importlib.util.spec_from_file_location("aletheia_pre_commit_under_test", script)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return vars(module)


def _gate(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    iwyu: subprocess.CompletedProcess[str],
) -> tuple[int, str, list[str]]:
    """Run the hook's IWYU gate with one staged file and a canned IWYU result.

    Returns the gate's exit code, what it wrote to stderr, and the IWYU command
    line it built.
    """
    staged = tmp_path / "src" / "Aletheia" / "Staged.agda"
    staged.parent.mkdir(parents=True)
    staged.write_text("", encoding="utf-8")
    hook = _load_pre_commit(tmp_path)
    iwyu_args: list[str] = []

    def fake_run(args: list[str], cwd: object = None) -> subprocess.CompletedProcess[str]:
        del cwd
        assert args[:2] == ["git", "diff"], args
        return subprocess.CompletedProcess(args, 0, "src/Aletheia/Staged.agda\n", "")

    def fake_run_iwyu(rels: list[str], cwd: object) -> subprocess.CompletedProcess[str]:
        del cwd
        iwyu_args.extend(rels)
        return iwyu

    hook["_run"] = fake_run
    hook["_run_iwyu"] = fake_run_iwyu
    gate = cast("Callable[[Path], int]", hook["_iwyu_gate"])
    rc = gate(tmp_path)
    assert iwyu_args == ["Aletheia/Staged.agda"]
    return rc, capsys.readouterr().err, iwyu_args


def test_pre_commit_iwyu_gate_refuses_a_run_that_never_happened(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A non-zero exit with nothing on stdout is a run that never reached a verdict.

    Its reason went to the terminal live, so the hook names that, refuses the
    commit, and never dresses the absence of a report up as findings.
    """
    rc, err, _ = _gate(tmp_path, capsys, subprocess.CompletedProcess([], 1, "", None))
    assert rc == 1
    assert "could not run" in err
    assert "refused" in err
    assert "flagged" not in err
    assert "tools.iwyu --check Aletheia/Staged.agda" in err


def test_pre_commit_iwyu_gate_refuses_findings_with_their_report(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A non-zero exit with a report on stdout is findings, and they block."""
    report = (
        "  DEAD Aletheia/Staged.agda: foo (unused named import — remove)\n"
        "=== iwyu: 1 finding(s) ===\n"
    )
    rc, err, _ = _gate(tmp_path, capsys, subprocess.CompletedProcess([], 1, report, None))
    assert rc == 1
    assert "flagged" in err
    assert "DEAD Aletheia/Staged.agda" in err
    assert "refused" in err
    assert "could not run" not in err


def test_pre_commit_iwyu_gate_passes_a_clean_run(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A zero exit passes and says nothing beyond announcing the gate."""
    rc, err, _ = _gate(tmp_path, capsys, subprocess.CompletedProcess([], 0, "", None))
    assert rc == 0
    assert "flagged" not in err
    assert "could not run" not in err


def test_pre_commit_iwyu_gate_queues_behind_the_agda_lock() -> None:
    """The hook's IWYU command carries the wait flag: a sweep delays a commit, never fails it."""
    assert '"--check", "--wait-lock"' in PRE_COMMIT_BODY


_GIT_ENV = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}


def _git(repo: Path, *args: str) -> str:
    """Run git in *repo* with the caller's global config shut out, returning stdout.

    The global config could sign every commit and would then hang the test
    repository's commit on a passphrase prompt.
    """
    return subprocess.run(
        [find_executable("git"), *args],
        cwd=repo,
        env=_GIT_ENV,
        capture_output=True,
        text=True,
        check=True,
    ).stdout


_NOTES_BASE = "l1\nl2\nl3\nl4\nl5\nl6\n"
_NOTES_STAGED = "l1\nL2\nl3\nl4\nl5\nl6\n"
_NOTES_WORKTREE = "l1\nL2\nL3\nl4\nl5\nl6\n"


def _hooked_repo(tmp_path: Path) -> Path:
    """Build a repository with the rendered pre-commit hook installed and a gate stub.

    The stub `tools/run_ci.py` passes at once, so the commit exercises the
    hook's stash and restore around a gate that finds nothing. It is committed
    in the base, because an untracked stub would be parked with the rest, and
    the bytecode its run writes is ignored so the status read back is the
    change the test made.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "config", "user.name", "hook test")
    _git(repo, "config", "user.email", "hook@test")
    (repo / ".gitignore").write_text("__pycache__/\n", encoding="utf-8")
    (repo / "tools").mkdir()
    (repo / "tools" / "__init__.py").write_text("", encoding="utf-8")
    (repo / "tools" / "run_ci.py").write_text("raise SystemExit(0)\n", encoding="utf-8")
    (repo / "notes.txt").write_text(_NOTES_BASE, encoding="utf-8")
    (repo / "gone.txt").write_text("gone\n", encoding="utf-8")
    _git(repo, "add", ".")
    _git(repo, "commit", "-q", "-m", "base")
    hook = repo / ".git" / "hooks" / "pre-commit"
    body = PRE_COMMIT_BODY.split("\n", 1)[1]
    hook.write_text("#!" + sys.executable + "\n" + body, encoding="utf-8")
    hook.chmod(hook.stat().st_mode | stat.S_IXUSR)
    return repo


def test_pre_commit_writes_a_file_staged_in_part_back_whole(tmp_path: Path) -> None:
    """A commit of half a file's hunks lands the half, and the tree comes back whole.

    The index holds one hunk of the file and the worktree holds two, the
    shape a commit from a patch leaves. The hook parks the unstaged hunk, an
    unstaged deletion and an untracked file while its gates run, and writes
    them back file by file: a merge of the parked tree against the partial
    index stops unmerged on the shared region, after the gates have passed.
    """
    repo = _hooked_repo(tmp_path)
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    _git(repo, "add", "notes.txt")
    (repo / "notes.txt").write_text(_NOTES_WORKTREE, encoding="utf-8")
    (repo / "gone.txt").unlink()
    (repo / "scratch.txt").write_text("scratch\n", encoding="utf-8")
    staged = _git(repo, "diff", "--cached")

    _git(repo, "commit", "-q", "-m", "half")

    assert _git(repo, "show", "HEAD:notes.txt") == _NOTES_STAGED
    assert _git(repo, "diff", "HEAD~1", "HEAD") == staged
    assert (repo / "notes.txt").read_text(encoding="utf-8") == _NOTES_WORKTREE
    assert not (repo / "gone.txt").exists()
    assert (repo / "scratch.txt").read_text(encoding="utf-8") == "scratch\n"
    assert _git(repo, "status", "--porcelain") == " D gone.txt\n M notes.txt\n?? scratch.txt\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_restore_failure_keeps_the_stash_and_prints_the_recipe(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A restore that fails leaves the stash in place and prints the commands that write it back."""
    hook = _load_pre_commit(tmp_path)
    sha = "0123456789abcdef0123456789abcdef01234567"
    git_calls: list[list[str]] = []

    def fake_run(args: list[str], cwd: object = None) -> subprocess.CompletedProcess[str]:
        del cwd
        git_calls.append(args)
        listing = "stash@{0} " + sha + "\n" if args[:3] == ["git", "stash", "list"] else ""
        return subprocess.CompletedProcess(args, 0, listing, "")

    def fake_restore(root: object, source: str, paths: str) -> subprocess.CompletedProcess[str]:
        del root
        return subprocess.CompletedProcess([source, paths], 1, "", "boom\n")

    def fake_stash_paths(root: object, sha: str) -> tuple[str, str]:
        del root, sha
        return ("notes.txt\0", "")

    hook["_run"] = fake_run
    hook["_stash_paths"] = fake_stash_paths
    hook["_restore_worktree"] = fake_restore
    cast("Callable[[Path, str], None]", hook["_restore_stash"])(tmp_path, sha)
    err = capsys.readouterr().err
    assert "SAFE in stash commit " + sha in err
    assert "git restore --source=" + sha + " --worktree" in err
    assert "git restore --source=" + sha + "^3 --worktree" in err
    assert "boom" in err
    assert ["git", "stash", "drop", "stash@{0}"] not in git_calls


class Evidence(Enum):
    """What the evidence stub answers when the hook asks about the pushed commits."""

    RECORDED = "a sweep of the pushed tree is on record before the push"
    AFTER_SWEEP = "the hook's own sweep records the pushed tree"
    NEVER = "no sweep ever records the pushed tree, as for a dirty working tree"


_EVIDENCE_EXIT = {
    Evidence.RECORDED: "0",
    Evidence.AFTER_SWEEP: "0 if pathlib.Path('swept').exists() else 1",
    Evidence.NEVER: "1",
}


def _pushing_repo(tmp_path: Path, evidence: Evidence) -> Path:
    """Build a repository with the rendered pre-push hook and stubs for its two tools.

    The evidence stub answers as ``evidence`` says and writes down, one line
    per question, the commits it was asked about; the sweep stub passes and
    writes down that it ran.  Neither needs a remote: the hook is run
    directly, with the ref lines git would hand it on stdin.
    """
    repo = tmp_path / "repo"
    (repo / "tools").mkdir(parents=True)
    _git(repo, "init", "-q")
    (repo / "tools" / "__init__.py").write_text("", encoding="utf-8")
    stub = [
        "import pathlib, sys",
        "with pathlib.Path('asked').open('a') as asked:",
        "    asked.write(' '.join(sys.argv[1:]) + '\\n')",
        f"raise SystemExit({_EVIDENCE_EXIT[evidence]})",
        "",
    ]
    (repo / "tools" / "sweep_evidence.py").write_text("\n".join(stub), encoding="utf-8")
    (repo / "tools" / "run_ci.py").write_text(
        "import pathlib\npathlib.Path('swept').write_text('yes')\n", encoding="utf-8"
    )
    hook = repo / ".git" / "hooks" / "pre-push"
    body = PRE_PUSH_BODY.split("\n", 1)[1]
    hook.write_text("#!" + sys.executable + "\n" + body, encoding="utf-8")
    hook.chmod(hook.stat().st_mode | stat.S_IXUSR)
    return repo


# The ref lines git hands a pre-push hook on stdin, a file the hook runs, and
# the commits one question to the evidence stub named.
RefLines = NewType("RefLines", str)
ToolFile = NewType("ToolFile", str)
Question = NewType("Question", str)


class Pushed(NamedTuple):
    """What the pre-push hook answered: its exit status and what it wrote to stderr."""

    returncode: ExitStatus
    stderr: Prose


def _push(repo: Path, refs: RefLines) -> Pushed:
    """Run the pre-push hook as git would, with ``refs`` on its stdin."""
    done = subprocess.run(
        [str(repo / ".git" / "hooks" / "pre-push"), "origin", "git@example:repo.git"],
        cwd=repo,
        input=refs,
        env=_GIT_ENV,
        capture_output=True,
        text=True,
        check=False,
    )
    return Pushed(ExitStatus(done.returncode), Prose(done.stderr))


def _asked(repo: Path) -> list[Question]:
    """Read back the questions the evidence stub was asked, one per line."""
    asked = repo / "asked"
    lines = asked.read_text(encoding="utf-8").splitlines() if asked.exists() else []
    return [Question(line) for line in lines]


_PUSHED = "a" * 40
_OTHER = "b" * 40
_REFS = RefLines(
    "".join(
        [
            f"refs/heads/b {_PUSHED} refs/heads/b {'0' * 40}\n",
            f"refs/tags/t {_OTHER} refs/tags/t {'0' * 40}\n",
        ]
    )
)


def test_pre_push_allows_at_once_a_push_whose_trees_passed_a_recorded_sweep(
    tmp_path: Path,
) -> None:
    """With every pushed ref's tree on record, the push goes without a sweep."""
    repo = _pushing_repo(tmp_path, Evidence.RECORDED)
    done = _push(repo, _REFS)
    assert done.returncode == 0, done.stderr
    assert _asked(repo) == [f"{_PUSHED} {_OTHER}"]
    assert not (repo / "swept").exists()
    assert "push allowed" in done.stderr


def test_pre_push_sweeps_then_allows_once_its_sweep_records_the_pushed_tree(
    tmp_path: Path,
) -> None:
    """A tree no sweep covers makes the hook sweep, then ask again before it allows."""
    repo = _pushing_repo(tmp_path, Evidence.AFTER_SWEEP)
    done = _push(repo, _REFS)
    assert done.returncode == 0, done.stderr
    assert (repo / "swept").read_text(encoding="utf-8") == "yes"
    assert _asked(repo) == [f"{_PUSHED} {_OTHER}"] * 2
    assert "push allowed" in done.stderr


def test_pre_push_refuses_when_its_sweep_passed_on_another_tree(tmp_path: Path) -> None:
    """A passing sweep of a working tree that is not the pushed one allows nothing."""
    repo = _pushing_repo(tmp_path, Evidence.NEVER)
    done = _push(repo, _REFS)
    assert done.returncode == 1, done.stderr
    assert (repo / "swept").read_text(encoding="utf-8") == "yes"
    assert len(_asked(repo)) == 2
    assert "push refused" in done.stderr


def test_pre_push_allows_a_deletion_which_pushes_no_commit(tmp_path: Path) -> None:
    """A ref line whose local id is all zeros deletes a remote ref and needs no sweep."""
    repo = _pushing_repo(tmp_path, Evidence.NEVER)
    done = _push(repo, RefLines(f"(delete) {'0' * 40} refs/heads/b {_PUSHED}\n"))
    assert done.returncode == 0, done.stderr
    assert not _asked(repo)
    assert not (repo / "swept").exists()


@pytest.mark.parametrize("tool", [ToolFile("run_ci.py"), ToolFile("sweep_evidence.py")])
def test_pre_push_refuses_when_a_tool_it_runs_is_missing(tmp_path: Path, tool: ToolFile) -> None:
    """Without the sweep or its evidence the hook cannot vouch for the push, so it refuses."""
    repo = _pushing_repo(tmp_path, Evidence.RECORDED)
    (repo / "tools" / tool).unlink()
    done = _push(repo, _REFS)
    assert done.returncode == 1, done.stderr
    assert f"{tool} not found" in done.stderr
    assert not _asked(repo)
    assert not (repo / "swept").exists()
