# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Guards for the git-hook bodies ``tools/install_hooks.py`` renders.

What they render, and what the rendered hooks do to a repository.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import re
import stat
import subprocess
import sys
from enum import Enum
from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

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


def test_pre_commit_dict_braces_survived_the_fstring() -> None:
    """The private-index environment renders as a dict: the f-string must not eat its braces.

    A ``{`` in the body is an f-string field unless doubled, and a brace eaten
    there leaves text ``compile()`` may still accept.
    """
    assert "env = {**os.environ, " in PRE_COMMIT_BODY


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

# A path relative to the test repository's root, a file's text, git's short
# status of the whole tree, one word of a git command line, a NUL-separated
# list of paths as the hook hands git, what a git process wrote, the sha of a
# stash commit, and a revision git resolves (a sha, or one with a suffix).
RelPath = NewType("RelPath", str)
FileText = NewType("FileText", str)
PorcelainStatus = NewType("PorcelainStatus", str)
GitWord = NewType("GitWord", str)
NulPaths = NewType("NulPaths", str)
GitOutput = NewType("GitOutput", str)
StashSha = NewType("StashSha", str)
Revision = NewType("Revision", str)
GitDone = subprocess.CompletedProcess[GitOutput]

# The gate stub: it writes down what a gate run by the hook sees, git's status,
# every file's text and every directory, to the path the test bakes in outside
# the repository, then passes.
_GATE_STUB = """\
import json
import pathlib
import subprocess

status = subprocess.run(
    ["git", "status", "--porcelain", "--untracked-files=all"],
    capture_output=True,
    text=True,
    check=True,
).stdout
paths = [
    path
    for path in sorted(pathlib.Path().rglob("*"))
    if ".git" not in path.parts and path.parts[0] != "tools" and path.name[0] != "."
]
files = {str(path): path.read_text(encoding="utf-8") for path in paths if path.is_file()}
dirs = [str(path) for path in paths if path.is_dir()]
seen = {"status": status, "files": files, "dirs": dirs}
pathlib.Path(SEEN).write_text(json.dumps(seen), encoding="utf-8")
"""


class GateView(TypedDict):
    """What the gate stub saw while the hook ran it, as the stub's JSON spells it."""

    status: PorcelainStatus
    files: dict[RelPath, FileText]
    dirs: list[RelPath]


def _seen(tmp_path: Path) -> GateView:
    """Read back what the gate stub saw during the last commit through the hook."""
    return cast("GateView", json.loads((tmp_path / "seen.json").read_text(encoding="utf-8")))


def _hooked_repo(tmp_path: Path) -> Path:
    """Build a repository with the rendered pre-commit hook installed and a gate stub.

    The stub `tools/run_ci.py` writes down what it sees and passes, so the
    commit exercises the hook's stash and restore around a gate that finds
    nothing, and the test reads what the gate was shown. It is committed in
    the base, because an untracked stub would be parked with the rest, and
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
    stub = _GATE_STUB.replace("SEEN", repr(str(tmp_path / "seen.json")))
    (repo / "tools" / "run_ci.py").write_text(stub, encoding="utf-8")
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
    seen = _seen(tmp_path)
    assert seen["status"] == "M  notes.txt\n"
    assert seen["files"] == {
        RelPath("gone.txt"): FileText("gone\n"),
        RelPath("notes.txt"): FileText(_NOTES_STAGED),
    }
    assert (repo / "notes.txt").read_text(encoding="utf-8") == _NOTES_WORKTREE
    assert not (repo / "gone.txt").exists()
    assert (repo / "scratch.txt").read_text(encoding="utf-8") == "scratch\n"
    assert _git(repo, "status", "--porcelain") == " D gone.txt\n M notes.txt\n?? scratch.txt\n"
    assert _git(repo, "stash", "list") == ""


# A modification time no machine running the tests would write, in
# nanoseconds since the epoch.
_OLD_STAMP = 978_307_200_000_000_000


def test_pre_commit_leaves_a_staged_file_s_modification_time_alone(tmp_path: Path) -> None:
    """A commit through the hook leaves a staged file where it was, its mtime included.

    A stash of the whole tree with `--keep-index` checks every staged file out
    again, contents unchanged, which moves every committed file's mtime to
    the commit's time and makes every consumer that reads mtimes (ninja,
    CMake, the slices probe) rebuild from sources it has already built. The
    hook writes only the paths it parks, so a file that is only staged, or
    untouched, keeps its time.
    """
    repo = _hooked_repo(tmp_path)
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    _git(repo, "add", "notes.txt")
    (repo / "gone.txt").unlink()
    for name in ("notes.txt", "tools/__init__.py"):
        os.utime(repo / name, ns=(_OLD_STAMP, _OLD_STAMP))

    _git(repo, "commit", "-q", "-m", "whole")

    assert _git(repo, "show", "HEAD:notes.txt") == _NOTES_STAGED
    assert _seen(tmp_path)["status"] == "M  notes.txt\n"
    assert [(repo / name).stat().st_mtime_ns for name in ("notes.txt", "tools/__init__.py")] == [
        _OLD_STAMP,
        _OLD_STAMP,
    ]
    assert _git(repo, "status", "--porcelain") == " D gone.txt\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_parks_an_untracked_file_by_its_name_not_as_a_pathspec(tmp_path: Path) -> None:
    """An untracked `:x.txt` or `x[1].txt` is parked as that file: a name, never a pathspec.

    Read as a pathspec, the colon is magic git cannot resolve and refuses,
    and the bracket a pattern that carries the staged `x1.txt` along.
    """
    repo = _hooked_repo(tmp_path)
    (repo / "x1.txt").write_text("b\n", encoding="utf-8")
    _git(repo, "add", "x1.txt")
    _git(repo, "commit", "-q", "-m", "tracked")
    (repo / "x1.txt").write_text("B\n", encoding="utf-8")
    _git(repo, "add", "x1.txt")
    (repo / "x[1].txt").write_text("u\n", encoding="utf-8")
    (repo / ":x.txt").write_text("v\n", encoding="utf-8")

    _git(repo, "commit", "-q", "-m", "named")

    assert _git(repo, "show", "HEAD:x1.txt") == "B\n"
    assert _seen(tmp_path)["status"] == "M  x1.txt\n"
    assert (repo / "x1.txt").read_text(encoding="utf-8") == "B\n"
    assert (repo / "x[1].txt").read_text(encoding="utf-8") == "u\n"
    assert (repo / ":x.txt").read_text(encoding="utf-8") == "v\n"
    assert _git(repo, "status", "--porcelain") == "?? :x.txt\n?? x[1].txt\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_keeps_a_staged_deletion_whose_file_stays_on_disk(tmp_path: Path) -> None:
    """A file removed from the index but kept on disk is committed as deleted and stays on disk.

    `git rm --cached` leaves the file untracked at a staged-deleted path; a
    stash push that stages what it parks would re-add it, and the commit
    would keep the file.
    """
    repo = _hooked_repo(tmp_path)
    _git(repo, "rm", "--cached", "-q", "gone.txt")

    _git(repo, "commit", "-q", "-m", "untracked")

    assert _git(repo, "ls-tree", "--name-only", "HEAD", "gone.txt") == ""
    assert _seen(tmp_path)["status"] == "D  gone.txt\n"
    assert (repo / "gone.txt").read_text(encoding="utf-8") == "gone\n"
    assert _git(repo, "status", "--porcelain") == "?? gone.txt\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_keeps_an_unstaged_deletion_of_a_staged_new_file(tmp_path: Path) -> None:
    """A file added to the index then deleted from the tree is committed, and stays deleted.

    git's own stash tree records the parked paths against HEAD, where a
    deleted file that HEAD lacks is nothing, so the file came back after the
    hook; the hook's tree records the parked paths as they stand.
    """
    repo = _hooked_repo(tmp_path)
    (repo / "new.txt").write_text("new\n", encoding="utf-8")
    _git(repo, "add", "new.txt")
    (repo / "new.txt").unlink()

    _git(repo, "commit", "-q", "-m", "added")

    assert _git(repo, "show", "HEAD:new.txt") == "new\n"
    assert _seen(tmp_path)["files"][RelPath("new.txt")] == "new\n"
    assert not (repo / "new.txt").exists()
    assert _git(repo, "status", "--porcelain") == " D new.txt\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_keeps_a_worktree_reverted_to_head_beside_its_staged_change(
    tmp_path: Path,
) -> None:
    """A staged change whose worktree copy was put back by hand is committed, and the copy stays.

    git's own stash tree records nothing for a path whose worktree equals
    HEAD, so the staged version was written over the copy after the hook.
    """
    repo = _hooked_repo(tmp_path)
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    _git(repo, "add", "notes.txt")
    (repo / "notes.txt").write_text(_NOTES_BASE, encoding="utf-8")

    _git(repo, "commit", "-q", "-m", "reverted")

    assert _git(repo, "show", "HEAD:notes.txt") == _NOTES_STAGED
    assert _seen(tmp_path)["files"][RelPath("notes.txt")] == _NOTES_STAGED
    assert (repo / "notes.txt").read_text(encoding="utf-8") == _NOTES_BASE
    assert _git(repo, "status", "--porcelain") == " M notes.txt\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_leaves_a_stash_beneath_its_own_alone(tmp_path: Path) -> None:
    """An entry already on the stack is neither written over the tree nor dropped."""
    repo = _hooked_repo(tmp_path)
    (repo / "notes.txt").write_text("theirs\n", encoding="utf-8")
    _git(repo, "stash", "push", "-q", "-m", "theirs")
    theirs = _git(repo, "rev-parse", "stash@{0}")
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    _git(repo, "add", "notes.txt")
    (repo / "notes.txt").write_text(_NOTES_WORKTREE, encoding="utf-8")

    _git(repo, "commit", "-q", "-m", "half")

    assert _git(repo, "show", "HEAD:notes.txt") == _NOTES_STAGED
    assert (repo / "notes.txt").read_text(encoding="utf-8") == _NOTES_WORKTREE
    assert _git(repo, "stash", "list", "--format=%H") == theirs


def test_pre_commit_parks_a_file_whose_name_is_not_utf_8(tmp_path: Path) -> None:
    """An untracked file whose name is not UTF-8 is parked and comes back, never a crash."""
    repo = _hooked_repo(tmp_path)
    name = b"caf\xe9.txt".decode("utf-8", "surrogateescape")
    (repo / name).write_text("u\n", encoding="utf-8")
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    _git(repo, "add", "notes.txt")

    _git(repo, "commit", "-q", "-m", "named")

    assert _git(repo, "show", "HEAD:notes.txt") == _NOTES_STAGED
    assert _seen(tmp_path)["status"] == "M  notes.txt\n"
    assert (repo / name).read_text(encoding="utf-8") == "u\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_parks_an_untracked_file_with_the_directories_it_leaves_empty(
    tmp_path: Path,
) -> None:
    """An untracked file in a directory of its own is parked with the directory, and both return."""
    repo = _hooked_repo(tmp_path)
    (repo / "u" / "v").mkdir(parents=True)
    (repo / "u" / "v" / "two.txt").write_text("2\n", encoding="utf-8")
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    _git(repo, "add", "notes.txt")

    _git(repo, "commit", "-q", "-m", "nested")

    seen = _seen(tmp_path)
    assert seen["status"] == "M  notes.txt\n"
    assert seen["dirs"] == []
    assert (repo / "u" / "v" / "two.txt").read_text(encoding="utf-8") == "2\n"
    assert _git(repo, "status", "--porcelain") == "?? u/\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_leaves_a_nested_repository_where_it_is(tmp_path: Path) -> None:
    """A repository nested in the tree, untracked, is not parked: git lists it as a directory."""
    repo = _hooked_repo(tmp_path)
    nested = repo / "vendor" / "sub"
    nested.mkdir(parents=True)
    _git(nested, "init", "-q")
    (nested / "inner.txt").write_text("inner\n", encoding="utf-8")
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    _git(repo, "add", "notes.txt")

    _git(repo, "commit", "-q", "-m", "nested")

    assert _git(repo, "show", "HEAD:notes.txt") == _NOTES_STAGED
    assert _seen(tmp_path)["status"] == "M  notes.txt\n?? vendor/sub/\n"
    assert (nested / "inner.txt").read_text(encoding="utf-8") == "inner\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_serves_a_commit_of_all_tracked_changes(tmp_path: Path) -> None:
    """`git commit -a` hands the hook the index it builds; the untracked file is parked."""
    repo = _hooked_repo(tmp_path)
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    (repo / "scratch.txt").write_text("scratch\n", encoding="utf-8")

    _git(repo, "commit", "-q", "-a", "-m", "all")

    assert _git(repo, "show", "HEAD:notes.txt") == _NOTES_STAGED
    assert _seen(tmp_path)["status"] == "M  notes.txt\n"
    assert _git(repo, "status", "--porcelain") == "?? scratch.txt\n"
    assert _git(repo, "stash", "list") == ""


def test_pre_commit_serves_a_commit_of_named_paths(tmp_path: Path) -> None:
    """`git commit -- <path>` hands the hook a temporary index; the other edit stays in the tree."""
    repo = _hooked_repo(tmp_path)
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    (repo / "gone.txt").write_text("edited\n", encoding="utf-8")
    (repo / "scratch.txt").write_text("scratch\n", encoding="utf-8")

    _git(repo, "commit", "-q", "-m", "one", "--", "notes.txt")

    assert _git(repo, "show", "HEAD:notes.txt") == _NOTES_STAGED
    assert _git(repo, "show", "HEAD:gone.txt") == "gone\n"
    assert _seen(tmp_path)["status"] == "M  notes.txt\n"
    assert (repo / "gone.txt").read_text(encoding="utf-8") == "edited\n"
    assert _git(repo, "status", "--porcelain") == " M gone.txt\n?? scratch.txt\n"
    assert _git(repo, "stash", "list") == ""


class Parked(Enum):
    """Which kinds of work a recipe test parks."""

    TRACKED = "an unstaged edit"
    UNTRACKED = "an untracked file"
    BOTH = "an unstaged edit and an untracked file"


@pytest.mark.parametrize("parked", list(Parked), ids=lambda p: p.name.lower())
def test_pre_commit_s_recipe_writes_the_parked_work_back(tmp_path: Path, parked: Parked) -> None:
    """The commands the hook prints when a restore fails write the parked work back, run as printed.

    One line per tree that holds parked files: a line for a tree that holds
    none would fail, since git restore refuses an empty list of paths.
    """
    repo = _hooked_repo(tmp_path)
    hook = _load_pre_commit(tmp_path)
    (repo / "notes.txt").write_text(_NOTES_STAGED, encoding="utf-8")
    _git(repo, "add", "notes.txt")
    if parked is not Parked.UNTRACKED:
        (repo / "notes.txt").write_text(_NOTES_WORKTREE, encoding="utf-8")
    if parked is not Parked.TRACKED:
        (repo / "scratch.txt").write_text("scratch\n", encoding="utf-8")
    before = _git(repo, "status", "--porcelain")
    parked_paths = cast("Callable[[Path], tuple[NulPaths, NulPaths]]", hook["_parked_paths"])
    create_stash = cast("Callable[[Path, NulPaths, NulPaths], StashSha]", hook["_create_stash"])
    stash_paths = cast(
        "Callable[[Path, StashSha], tuple[NulPaths, NulPaths]]", hook["_stash_paths"]
    )
    recipe_of = cast("Callable[[StashSha, NulPaths, NulPaths], Prose]", hook["_recipe"])
    unstaged, untracked = parked_paths(repo)
    sha = create_stash(repo, unstaged, untracked)
    assert cast("Callable[[Path, Revision, NulPaths, NulPaths], bool]", hook["_isolate"])(
        repo, Revision(sha + "^2"), unstaged, untracked
    )
    assert _git(repo, "status", "--porcelain") == "M  notes.txt\n"

    commands = [
        line.removeprefix("pre-commit:   ")
        for line in recipe_of(sha, *stash_paths(repo, sha)).splitlines()[1:]
    ]
    for command in commands:
        subprocess.run([find_executable("bash"), "-c", command], cwd=repo, env=_GIT_ENV, check=True)

    assert len(commands) == (2 if parked is Parked.BOTH else 1)
    assert _git(repo, "status", "--porcelain") == before
    if parked is not Parked.UNTRACKED:
        assert (repo / "notes.txt").read_text(encoding="utf-8") == _NOTES_WORKTREE
    if parked is not Parked.TRACKED:
        assert (repo / "scratch.txt").read_text(encoding="utf-8") == "scratch\n"


def test_pre_commit_s_entry_is_one_git_stash_pop_reads(tmp_path: Path) -> None:
    """The entry the hook records is laid out as git's own, so `git stash pop` writes it back.

    From a clean index: git's pop merges the entry against the index, and
    stops on a file staged in part, which is why the hook restores by hand.
    """
    repo = _hooked_repo(tmp_path)
    hook = _load_pre_commit(tmp_path)
    (repo / "notes.txt").write_text(_NOTES_WORKTREE, encoding="utf-8")
    (repo / "gone.txt").unlink()
    (repo / "scratch.txt").write_text("scratch\n", encoding="utf-8")
    before = _git(repo, "status", "--porcelain")
    parked_paths = cast("Callable[[Path], tuple[NulPaths, NulPaths]]", hook["_parked_paths"])
    create_stash = cast("Callable[[Path, NulPaths, NulPaths], StashSha]", hook["_create_stash"])
    unstaged, untracked = parked_paths(repo)
    sha = create_stash(repo, unstaged, untracked)
    assert cast("Callable[[Path, Revision, NulPaths, NulPaths], bool]", hook["_isolate"])(
        repo, Revision(sha + "^2"), unstaged, untracked
    )
    assert _git(repo, "status", "--porcelain") == ""

    _git(repo, "stash", "pop", "-q")

    assert _git(repo, "status", "--porcelain") == before
    assert (repo / "notes.txt").read_text(encoding="utf-8") == _NOTES_WORKTREE
    assert not (repo / "gone.txt").exists()
    assert (repo / "scratch.txt").read_text(encoding="utf-8") == "scratch\n"
    assert _git(repo, "stash", "list") == ""


class HookRun(NamedTuple):
    """What a hook answered: its exit status and what it wrote to stderr."""

    returncode: ExitStatus
    stderr: Prose


class PathCall(NamedTuple):
    """One git command the hook ran over a list of paths."""

    args: list[GitWord]
    paths: NulPaths


class FakedHook(NamedTuple):
    """A pre-commit hook loaded with its parking faked, and what it asked git for."""

    main: Callable[[], ExitStatus]
    git_calls: list[list[GitWord]]
    restores: list[PathCall]


_OURS = StashSha("0123456789abcdef0123456789abcdef01234567")
_THEIRS = StashSha("89abcdef0123456789abcdef0123456789abcdef")


def _faked_hook(
    tmp_path: Path, *, stash: StashSha | None, isolated: bool, restored: bool
) -> FakedHook:
    """Load the hook with a gate stub that passes and its parking faked.

    The parked paths are one tracked and one untracked file; recording them
    answers ``stash``, isolating the tree answers ``isolated``, and each
    worktree restore succeeds or fails as ``restored`` says. git itself
    answers only what the gate and the drop read, with a foreign entry on top
    of the stack and the hook's own beneath it.
    """
    hook = _load_pre_commit(tmp_path)
    (tmp_path / "tools").mkdir()
    (tmp_path / "tools" / "__init__.py").write_text("", encoding="utf-8")
    (tmp_path / "tools" / "run_ci.py").write_text("", encoding="utf-8")
    git_calls: list[list[GitWord]] = []
    restores: list[PathCall] = []

    def fake_run(args: list[GitWord], cwd: Path | None = None) -> GitDone:
        del cwd
        git_calls.append(args)
        out = GitOutput("")
        if args == ["git", "rev-parse", "--show-toplevel"]:
            out = GitOutput(str(tmp_path))
        elif args[:3] == ["git", "stash", "list"]:
            out = GitOutput("stash@{0} " + _THEIRS + "\nstash@{1} " + _OURS + "\n")
        return subprocess.CompletedProcess(args, 0, out, GitOutput(""))

    def fake_parked_paths(root: Path) -> tuple[NulPaths, NulPaths]:
        del root
        return NulPaths("notes.txt\0"), NulPaths("scratch.txt\0")

    def fake_create_stash(root: Path, unstaged: NulPaths, untracked: NulPaths) -> StashSha | None:
        del root, unstaged, untracked
        return stash

    def fake_isolate(root: Path, i_tree: Revision, unstaged: NulPaths, untracked: NulPaths) -> bool:
        del root, i_tree, unstaged, untracked
        return isolated

    def fake_stash_paths(root: Path, sha: StashSha) -> tuple[NulPaths, NulPaths]:
        del root, sha
        return NulPaths("notes.txt\0"), NulPaths("scratch.txt\0")

    def fake_restore(root: Path, source: Revision, paths: NulPaths) -> GitDone:
        del root
        restores.append(PathCall([GitWord(source)], paths))
        complaint = GitOutput("" if restored else "boom\n")
        return subprocess.CompletedProcess([source], int(not restored), GitOutput(""), complaint)

    hook["_run"] = fake_run
    hook["_parked_paths"] = fake_parked_paths
    hook["_create_stash"] = fake_create_stash
    hook["_isolate"] = fake_isolate
    hook["_stash_paths"] = fake_stash_paths
    hook["_restore_worktree"] = fake_restore
    return FakedHook(cast("Callable[[], ExitStatus]", hook["main"]), git_calls, restores)


def _main(faked: FakedHook) -> HookRun:
    """Run the faked hook's ``main`` with its stderr captured."""
    captured = io.StringIO()
    with contextlib.redirect_stderr(captured):
        rc = faked.main()
    return HookRun(rc, Prose(captured.getvalue()))


def test_pre_commit_refuses_when_the_parked_work_cannot_be_recorded(tmp_path: Path) -> None:
    """With no entry made nothing is parked, and the gates would read more than what is staged."""
    faked = _faked_hook(tmp_path, stash=None, isolated=True, restored=True)
    done = _main(faked)
    assert done.returncode == 1
    assert "refused" in done.stderr
    assert "FAST static gates" not in done.stderr
    assert faked.restores == []
    assert [call for call in faked.git_calls if call[1] == "stash"] == []


def test_pre_commit_refuses_when_the_tree_cannot_be_isolated_and_writes_the_work_back(
    tmp_path: Path,
) -> None:
    """An isolation step that fails refuses the commit, the work written back, the entry dropped."""
    faked = _faked_hook(tmp_path, stash=_OURS, isolated=False, restored=True)
    done = _main(faked)
    assert done.returncode == 1
    assert "refused" in done.stderr
    assert "FAST static gates" not in done.stderr
    assert faked.restores == [
        PathCall([GitWord(_OURS)], NulPaths("notes.txt\0")),
        PathCall([GitWord(_OURS + "^3")], NulPaths("scratch.txt\0")),
    ]
    assert ["git", "stash", "drop", "stash@{1}"] in faked.git_calls
    assert "SAFE" not in done.stderr


def test_pre_commit_drops_its_own_entry_and_not_the_one_on_top(tmp_path: Path) -> None:
    """The entry dropped is the hook's own, found by its sha, never the top of the stack."""
    faked = _faked_hook(tmp_path, stash=_OURS, isolated=True, restored=True)
    done = _main(faked)
    assert done.returncode == 0
    assert ["git", "stash", "drop", "stash@{1}"] in faked.git_calls
    assert ["git", "stash", "drop", "stash@{0}"] not in faked.git_calls


def test_pre_commit_restore_failure_keeps_the_stash_and_prints_the_recipe(tmp_path: Path) -> None:
    """A restore that fails leaves the stash in place and prints the commands that write it back.

    The gates passed, so the commit goes ahead; the parked work is still in
    the stash commit the message names.
    """
    faked = _faked_hook(tmp_path, stash=_OURS, isolated=True, restored=False)
    done = _main(faked)
    assert done.returncode == 0
    assert "FAILED to restore" in done.stderr
    assert "boom" in done.stderr
    assert "SAFE in stash commit " + _OURS in done.stderr
    assert "git --literal-pathspecs restore --source=" + _OURS + " --worktree" in done.stderr
    assert "git --literal-pathspecs restore --source=" + _OURS + "^3 --worktree" in done.stderr
    assert [call for call in faked.git_calls if call[1:3] == ["stash", "drop"]] == []


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


def _push(repo: Path, refs: RefLines) -> HookRun:
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
    return HookRun(ExitStatus(done.returncode), Prose(done.stderr))


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
