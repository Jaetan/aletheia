# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the clang-tidy gate over cpp/src, cpp/tests and cpp/benchmarks.
# Claim: the gate reports a defect it is configured to catch, in a library
# source, a test source and a benchmark source alike, and a run that enabled
# no checks is not mistaken for a clean one. A discarded nodiscard return is
# injected into each tree in turn and removed again by the same step.
# Non-zero exit: the gate accepts the injected defect in any tree, a tree is
# not clean to begin with, or a run from the repository root, where no
# configuration is found, passes the same output test as a real run.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v run-clang-tidy-22 > /dev/null || { echo "run-clang-tidy-22 not installed"; exit 0; }
[ -f cpp/build/compile_commands.json ] || { echo "no compile database; configure cpp/build"; exit 2; }
python/.venv/bin/python - <<'PY'
import subprocess
import sys
from pathlib import Path

# One injection per tree the gate covers.  The test arm matters on its own,
# because the tests carry a configuration of their own and an over-wide
# disable there would be invisible from the library arm; the benchmark arm
# matters because the benchmarks are the tree most recently brought in and
# the one no other gate compiles.
INJECTIONS = (
    (Path("cpp/src/types.cpp"), "namespace aletheia {",
     "\n\nvoid probe_discard() { Dlc::create(8); }\n"),
    (Path("cpp/tests/unit_tests_dbc.cpp"), "using namespace aletheia;",
     "\n\nstatic void probe_discard_in_test() { Dlc::create(8); }\n"),
    (Path("cpp/benchmarks/stability_bench.cpp"), "static auto find_library() -> std::filesystem::path {",
     "\n    aletheia::Dlc::create(8);"),
)

originals = {}
for source, marker, _ in INJECTIONS:
    text = source.read_text(encoding="utf-8")
    if marker not in text:
        print(f"the injection point is gone from {source}")
        raise SystemExit(2)
    originals[source] = text


def gate(cwd: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["run-clang-tidy-22", "-quiet", "-p", "build" if cwd == "cpp" else "cpp/build",
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
