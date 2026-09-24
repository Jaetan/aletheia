#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the clang-tidy gate over cpp/src, cpp/tests and cpp/benchmarks.
# Claim: the gate reports a defect it is configured to catch, in a library
# source, a test source and a benchmark source alike, and a run that enabled
# no checks is not mistaken for a clean one. A discarded nodiscard return is
# injected into each tree in turn and removed again by the same step. Each
# injection carries the pid of the run that wrote it, a run killed between an
# injection and its restore leaves that line behind, and the next run refuses
# on it naming the run rather than capturing the injected text as its own
# original. Two runs cannot overlap: a run holds a lock under cpp/build for
# its whole body, and a second run reports it as held.
# Non-zero exit: 1 when the gate accepts the injected defect in any tree, a
# tree is not clean to begin with, or a run from the repository root, where no
# configuration is found, passes the same output test as a real run; 2 when
# the toolchain is missing, a source still carries an earlier run's injection,
# or another run holds the lock.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v run-clang-tidy-23 > /dev/null || { echo "run-clang-tidy-23 not installed"; exit 0; }
[ -f cpp/build/compile_commands.json ] || { echo "no compile database; configure cpp/build"; exit 2; }
python/.venv/bin/python - <<'PY'
import fcntl
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, ".")
from tools._common import process_alive  # noqa: E402

RUN = f"run pid {os.getpid()}"
BY = f"  // injected by the clang-tidy probe, {RUN}"

# One injection per tree the gate covers.  The test arm matters on its own,
# because the tests carry a configuration of their own and an over-wide
# disable there would be invisible from the library arm; the benchmark arm
# matters because the benchmarks are the tree most recently brought in and
# the one no other gate compiles.
INJECTIONS = (
    (Path("cpp/src/types.cpp"), "namespace aletheia {",
     f"\n\nvoid probe_discard() {{ Dlc::create(8); }}{BY}\n"),
    (Path("cpp/tests/unit_tests_dbc.cpp"), "using namespace aletheia;",
     f"\n\nstatic void probe_discard_in_test() {{ Dlc::create(8); }}{BY}\n"),
    (Path("cpp/benchmarks/stability_bench.cpp"), "static auto find_library() -> std::filesystem::path {",
     f"\n    aletheia::Dlc::create(8);{BY}"),
)
LEFTOVER = re.compile(r"probe_discard|Dlc::create\(8\);  // injected by the clang-tidy probe")
LEFTOVER_RUN = re.compile(r"injected by the clang-tidy probe, run pid (\d+)")

# The lock outlives this block on purpose: the process exit releases it.
lock_path = Path("cpp/build/probe-scratch/clang-tidy-injection.lock")
lock_path.parent.mkdir(parents=True, exist_ok=True)
lock = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o644)
try:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    holder = os.read(lock, 32).decode(errors="replace").strip() or "unknown"
    print(f"another run of this probe holds {lock_path} (pid {holder}); a second run "
          "started while the first injects would capture the injected text as its "
          "own original, so wait for it")
    raise SystemExit(2)
os.ftruncate(lock, 0)
os.write(lock, f"{os.getpid()}\n".encode())

originals = {}
for source, marker, _ in INJECTIONS:
    text = source.read_text(encoding="utf-8")
    if LEFTOVER.search(text):
        named = LEFTOVER_RUN.search(text)
        if named is None:
            who = "an unnamed run, from a probe older than this one"
        else:
            pid = int(named.group(1))
            who = f"pid {pid}, {'still alive' if process_alive(pid) else 'gone'}"
        print(f"{source} still carries the injection of an earlier run of this probe "
              f"({who}): that run was killed after injecting and before restoring; "
              "remove the injected line before running again")
        raise SystemExit(2)
    if marker not in text:
        print(f"the injection point is gone from {source}")
        raise SystemExit(2)
    originals[source] = text


def gate(cwd: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["run-clang-tidy-23", "-quiet", "-p", "build" if cwd == "cpp" else "cpp/build",
         "cpp/src/", "cpp/tests/", "cpp/benchmarks/"],
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
    )


clean = gate("cpp")
if "error:" in clean.stdout or "warning:" in clean.stdout:
    print(f"the tree is not clean before the injection:\n{clean.stdout[:400]}")
    raise SystemExit(1)

try:
    for source, marker, injection in INJECTIONS:
        source.write_text(
            originals[source].replace(marker, marker + injection, 1), encoding="utf-8"
        )
        injected = gate("cpp")
        source.write_text(originals[source], encoding="utf-8")
        if "clang-diagnostic-unused-result" not in injected.stdout:
            print(f"the gate did not report the discarded return in {source}:\n"
                  f"{injected.stdout[:400]}")
            raise SystemExit(1)
    from_root = gate(".")
finally:
    for source, text in originals.items():
        source.write_text(text, encoding="utf-8")

# The root-relative run enables no checks.  It must not look like the clean
# run above, or a reader grepping for a finding reads it as a pass.
if "No checks enabled" not in from_root.stdout + from_root.stderr:
    print("a run with no configuration in scope no longer says so")
    raise SystemExit(1)
if "error:" in from_root.stdout:
    print("a run with no configuration in scope unexpectedly reported findings")
    raise SystemExit(1)
sys.exit(0)
PY
