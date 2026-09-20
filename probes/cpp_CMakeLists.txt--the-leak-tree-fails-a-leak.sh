#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: the leak tree of the mutation lane fails a program that leaks, by
# LeakSanitizer's exit code and report. The lane counts a mutant as a
# survivor only where both trees let it live, and the leak tree's reason to
# exist is a mutant whose removed call would have released memory; that
# reading is worth something only if the tree's own flags make a leak fail. A
# unit that leaks one block is compiled with the flags the tree records for
# its own sources and run.
# Non-zero exit: the leaking program exits other than 23, or exits 23
# without LeakSanitizer's report, or a program that leaks nothing fails under
# the same flags. Exits 0 with a note when the toolchain or the tree is not
# available.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
[ -f cpp/build-mutation/compile_commands.json ] || { echo "no leak mutation tree configured, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
scratch=cpp/build-mutation/probe-scratch/leak-tree-fails-a-leak
mkdir -p "$scratch" || exit 2
# The sanitizer flags of the tree's own library unit, and nothing else of its
# command line: the leaking unit is this probe's, not the library's.
flags=$("$py" - <<'PYEOF'
import json, shlex
for entry in json.load(open("cpp/build-mutation/compile_commands.json")):
    if entry["file"].endswith("/cpp/src/client.cpp"):
        print(" ".join(a for a in shlex.split(entry["command"]) if a.startswith("-fsanitize") or a == "-fno-omit-frame-pointer"))
        break
PYEOF
)
[ -n "$flags" ] || { echo "the leak tree's library unit carries no sanitizer flag"; exit 1; }
cat > "$scratch/leaks.cpp" <<'CPP'
#include <cstdlib>
auto main() -> int {
    void* block = std::malloc(64);
    return block == nullptr ? 1 : 0;
}
CPP
cat > "$scratch/clean.cpp" <<'CPP'
#include <cstdlib>
auto main() -> int {
    void* block = std::malloc(64);
    std::free(block);
    return 0;
}
CPP
# shellcheck disable=SC2086
clang++-23 $flags -O0 -o "$scratch/leaks" "$scratch/leaks.cpp" || exit 2
# shellcheck disable=SC2086
clang++-23 $flags -O0 -o "$scratch/clean" "$scratch/clean.cpp" || exit 2
"$scratch/clean" > "$scratch/clean.log" 2>&1 || { echo "a program that leaks nothing fails under $flags"; exit 1; }
"$scratch/leaks" > "$scratch/leaks.log" 2>&1
rc=$?
[ "$rc" -eq 23 ] || { echo "the leaking program exited $rc, not LeakSanitizer's 23"; exit 1; }
grep -q "ERROR: LeakSanitizer: detected memory leaks" "$scratch/leaks.log" ||
    { echo "the leaking program exited 23 without a LeakSanitizer report"; exit 1; }
echo "the leak tree's flags ($flags) fail a leak by LeakSanitizer's report"
