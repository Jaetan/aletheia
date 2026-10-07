#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_sweep_cache.py.
# Claim: every file a sweep of the C++ mutation trees reads from the tree is
# one the sweep key names, so a kept sweep is served only while nothing it
# read has changed. For each tree the probe runs the lane's own command, in
# the lane's environment and directory, as a dry run under strace: the runner
# reads its configuration and the sources it copies into its report, and runs
# the unmutated binary once, which is the run every mutant repeats with one
# mutant switched on. LeakSanitizer refuses to run under ptrace, so leak
# detection is off under the trace; it reads nothing from the tree. Every
# path the runner or the tests touch inside the repository, found or only
# looked for, is resolved against the directory its process was in when it
# touched it, a new process starting in its parent's, and has to be a file
# the key names or a directory above one.
# Non-zero exit: a file inside the tree that a sweep touched and the key does
# not name, listed with the calls that touched it. Exits 2 without the venv,
# or when a traced dry run fails or never starts the test binary. Exits 0 with
# a note without strace, the runner or a built tree, since the claim is
# untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
command -v strace > /dev/null || { echo "strace is not installed, claim untestable"; exit 0; }

exec "$py" - << 'EOF'
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple, NewType

from tools.mutation_cpp import REPO_ROOT, CppRun, cpp_lane_command, cpp_sweep_directory, cpp_sweep_environment
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_sweep_cache import MULL_RUNNER, key_inputs, tree_binary, tree_build_dir

if shutil.which(MULL_RUNNER) is None:
    print(f"{MULL_RUNNER} is not installed, claim untestable")
    sys.exit(0)

# A line of the trace, a process as strace names it, a call it made, and a
# path as it prints one.
TraceLine = NewType("TraceLine", str)
Pid = NewType("Pid", int)
Call = NewType("Call", str)
TracedPath = NewType("TracedPath", str)


class Origin(NamedTuple):
    """The process a new one was cloned from, and whether the two share one working directory."""

    parent: Pid
    shares_directory: bool


named = set(key_inputs())
above = {parent for path in named for parent in path.parents if parent.is_relative_to(REPO_ROOT)}

# A path argument either follows a directory descriptor, which -y prints with
# the path it holds, AT_FDCWD with the process's directory at that call, or is
# the first argument of a call that takes none, resolved against the
# directory the process was last seen in.
LEADING = re.compile(r'^\d+ +(\w+)\("((?:[^"\\]|\\.)*)"')
AFTER_FD = re.compile(r'(?:AT_FDCWD|\d+)(?:<([^>]*)>)?, "((?:[^"\\]|\\.)*)"')
CALL = re.compile(r"^(\d+) +(?:<\.\.\. )?(\w+)")
AT_CWD = re.compile(r"AT_FDCWD<([^>]*)>")
FCHDIR = re.compile(r"fchdir\(\d+<([^>]*)>")
RESULT_OK = re.compile(r"\) += 0\b")
CLONES = ("clone", "clone3", "fork", "vfork")
CHILD = re.compile(r"\) += (\d+)$")


def resolve(base: Path, path: TracedPath) -> Path:
    return Path(os.path.normpath(base / path))


def origins(lines: list[TraceLine]) -> dict[Pid, Origin]:
    """Map every process the trace shows being cloned to the one it was cloned from.

    strace prints a clone's flags where the call starts and the new process
    where it returns, which are two lines when another process ran between.
    """
    flags: dict[Pid, bool] = {}
    found: dict[Pid, Origin] = {}
    for line in lines:
        match = CALL.match(line)
        if match is None or match.group(2) not in CLONES:
            continue
        pid = Pid(int(match.group(1)))
        if "<unfinished" in line:
            flags[pid] = "CLONE_FS" in line
            continue
        shares = flags.pop(pid, False) if "resumed>" in line else "CLONE_FS" in line
        child = CHILD.search(line)
        if child is not None:
            found[Pid(int(child.group(1)))] = Origin(pid, shares)
    return found


def touched(log: Path) -> dict[Path, set[Call]]:
    """Map every path inside the tree the trace shows to the calls that touched it.

    A working directory belongs to a group of processes: a clone that shares
    it joins its parent's group, any other starts a group of its own at the
    parent's directory as it stood.
    """
    lines = [TraceLine(line) for line in log.read_text(errors="replace").splitlines()]
    parents = origins(lines)
    group: dict[Pid, Pid] = {}
    cwd: dict[Pid, Path] = {}

    def group_of(pid: Pid) -> Pid:
        if pid not in group:
            origin = parents.get(pid)
            if origin is None:
                group[pid], cwd[pid] = pid, cpp_sweep_directory()
            elif origin.shares_directory:
                group[pid] = group_of(origin.parent)
            else:
                group[pid], cwd[pid] = pid, cwd[group_of(origin.parent)]
        return group[pid]

    pending: dict[Pid, Path] = {}
    seen: dict[Path, set[Call]] = {}
    for line in lines:
        match = CALL.match(line)
        if match is None:
            continue
        pid, call = Pid(int(match.group(1))), Call(match.group(2))
        own = group_of(pid)
        paths: list[Path] = []
        leading = LEADING.match(line)
        if leading is not None and leading.group(1) != "getcwd":
            paths.append(resolve(cwd[own], TracedPath(leading.group(2))))
        paths.extend(
            resolve(Path(base) if base else cwd[own], TracedPath(path)) for base, path in AFTER_FD.findall(line)
        )
        at_cwd = AT_CWD.search(line)
        if at_cwd is not None:
            cwd[own] = Path(at_cwd.group(1))
        if call in ("chdir", "fchdir"):
            fd = FCHDIR.search(line)
            target = (paths[0] if paths else None) if call == "chdir" else (None if fd is None else Path(fd.group(1)))
            if "<unfinished" in line:
                if target is not None:
                    pending[pid] = target
            elif "resumed>" in line:
                target = pending.pop(pid, None)
                if target is not None and RESULT_OK.search(line):
                    cwd[own] = target
            elif target is not None and RESULT_OK.search(line):
                cwd[own] = target
        for path in paths:
            if path.is_relative_to(REPO_ROOT):
                seen.setdefault(path, set()).add(call)
    return seen


failed = False
for tree in CppTree:
    leg = CppLeg(tree)
    build_dir = tree_build_dir(tree)
    if not os.access(tree_binary(tree), os.X_OK):
        print(f"the {tree.value} mutation tree is not built, claim untestable")
        sys.exit(0)
    with tempfile.TemporaryDirectory(prefix="sweep-trace-") as scratch:
        argv = cpp_lane_command(MULL_RUNNER, build_dir, Path(scratch), leg, CppRun(dry_run=True))
        log = Path(scratch) / "trace.log"
        env = cpp_sweep_environment(leg, build_dir).variables()
        env["ASAN_OPTIONS"] = env["LSAN_OPTIONS"] = "detect_leaks=0"
        run = subprocess.run(
            ["strace", "-f", "-qq", "-y", "-e", "trace=%file,%process,fchdir", "-o", str(log), *argv],
            cwd=cpp_sweep_directory(),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        seen = touched(log) if log.is_file() else {}
    # The runner opens the binary to read its mutants whether or not it runs
    # it, so the run the claim is about is the binary's own start.
    if run.returncode != 0 or "execve" not in seen.get(tree_binary(tree), set()):
        print(f"the {tree.value} tree's traced dry run failed (exit {run.returncode})")
        print(f"stdout: {run.stdout.strip()[-600:]}")
        print(f"stderr: {run.stderr.strip()[-600:]}")
        sys.exit(2)
    missing = {path: calls for path, calls in seen.items() if path not in named and path not in above}
    for path, calls in sorted(missing.items()):
        print(f"{tree.value}: {path.relative_to(REPO_ROOT)} ({', '.join(sorted(calls))}) is read and not keyed")
    failed = failed or bool(missing)
    print(f"{tree.value}: {len(seen)} paths inside the tree touched, {len(missing)} not keyed")
sys.exit(1 if failed else 0)
EOF
