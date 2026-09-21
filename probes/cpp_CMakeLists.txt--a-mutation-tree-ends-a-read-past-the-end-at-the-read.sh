#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: both mutation trees run the standard library's debug mode, so a read
# past a container's end ends the run at the read, with the check's message,
# instead of reading what lies beyond. What lies beyond is not reproducible:
# the census recorded a mutant that skips a map lookup's guard reading a
# garbage string whose length decided between a bad_alloc a test caught and a
# signal, run by run. Debug mode changes the containers' layout, so the claim
# is over every C++ unit of the tree, the fetched libraries included: each
# entry of the tree's compilation database is read for the define. Then a
# program that reads past a map's end is compiled with the defines and
# sanitizer flags the tree records for its own library unit and run; the same
# program is compiled once more with the debug-mode define withheld, and must
# then run to its end, so that the define is shown to be what ends the read
# rather than anything else on the line.
# Non-zero exit: a C++ unit of a tree compiles without the define, or under a
# tree's flags the program exits zero or dies without the check's message, or
# without the define it does not run to its end. Exits 0 with a note when
# clang-23 or both trees are absent.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
trees=""
for tree in build-mutation build-mutation-plain; do
    [ -f "cpp/$tree/compile_commands.json" ] && trees="$trees $tree"
done
[ -n "$trees" ] || { echo "no mutation tree configured, claim untestable"; exit 0; }
scratch=cpp/build-mutation-probe-scratch/read-past-the-end
mkdir -p "$scratch" || exit 2
cat > "$scratch/past_the_end.cpp" <<'CPP'
#include <cstdio>
#include <map>
#include <string>
auto main(int argc, char**) -> int {
    std::map<std::string, std::string> cells;
    if (argc > 1)
        cells["present"] = "value";
    auto const it = cells.find("absent");
    // The guard a mutant skips: it is at end(), and the read goes ahead.
    if (it == cells.end() && argc > 2)
        return 2;
    std::printf("read %zu bytes past the end\n", it->second.size());
    return 0;
}
CPP
message="attempt to dereference a past-the-end iterator"
for tree in $trees; do
    # Every C++ unit of the tree carries the define, or the layouts differ
    # across the units and the claim is off.
    without=$("$py" - "cpp/$tree/compile_commands.json" <<'PYEOF'
import json, shlex, sys
units = [e for e in json.load(open(sys.argv[1])) if e["file"].endswith((".cpp", ".cc", ".cxx"))]
missing = [e["file"] for e in units if "-D_GLIBCXX_DEBUG" not in shlex.split(e["command"])]
print(f"{len(units)} {len(missing)}", *missing[:3])
PYEOF
    )
    read -r units missing rest <<< "$without"
    [ "$units" -gt 0 ] || { echo "$tree: the compilation database lists no C++ unit"; exit 1; }
    [ "$missing" -eq 0 ] || { echo "$tree: $missing of $units C++ units compile without _GLIBCXX_DEBUG: $rest"; exit 1; }
    # The defines and sanitizer flags of the tree's own library unit, and
    # nothing else of its command line: the program is this probe's.
    flags=$("$py" - "cpp/$tree/compile_commands.json" <<'PYEOF'
import json, shlex, sys
for entry in json.load(open(sys.argv[1])):
    if entry["file"].endswith("/cpp/src/client.cpp"):
        print(" ".join(a for a in shlex.split(entry["command"])
                       if a.startswith(("-D", "-fsanitize")) or a == "-fno-omit-frame-pointer"))
        break
PYEOF
    )
    case " $flags " in *" -D_GLIBCXX_DEBUG "*) ;; *) echo "$tree's library unit does not define _GLIBCXX_DEBUG: flags '$flags'"; exit 1 ;; esac
    # shellcheck disable=SC2086
    clang++-23 -std=c++23 -O0 $flags -o "$scratch/checked-$tree" "$scratch/past_the_end.cpp" || exit 2
    "$scratch/checked-$tree" > "$scratch/checked-$tree.log" 2>&1
    rc=$?
    [ "$rc" -ne 0 ] || { echo "$tree: the read past the end ran to the end and exited 0 under '$flags'"; exit 1; }
    grep -q "$message" "$scratch/checked-$tree.log" ||
        { echo "$tree: the program died (exit $rc) without the check's message under '$flags'"; exit 1; }
    unchecked=$(printf '%s\n' $flags | grep -v '^-D_GLIBCXX_DEBUG$' | tr '\n' ' ')
    # shellcheck disable=SC2086
    clang++-23 -std=c++23 -O0 $unchecked -o "$scratch/unchecked-$tree" "$scratch/past_the_end.cpp" || exit 2
    "$scratch/unchecked-$tree" > "$scratch/unchecked-$tree.log" 2>&1 ||
        { echo "$tree: without the define the program did not run to its end (exit $?), so the define is not what the checked arm shows"; exit 1; }
    echo "$tree: all $units C++ units carry the define; the read past the end dies at the read with '$message' under '$flags', and runs to its end without the define"
done
