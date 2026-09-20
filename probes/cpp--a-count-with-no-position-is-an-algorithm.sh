#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the C++ sources and the lint configuration, cpp/.clang-tidy and
# cpp/tests/.clang-tidy, against the shapes a loop that runs a fixed number of
# times can take when its body reads no position: the count is all it has, so
# std::views::enumerate has nothing to hand over and std::views::zip has no
# second sequence.
# Claim: such a count is written std::ranges::for_each over std::views::repeat,
# whose unnamed lambda parameter needs no annotation, and the tree holds no
# range-for over that view, because a range-for has to name a variable the body
# never reads and the lint gate refuses one as a dead store, by
# clang-analyzer-deadcode.DeadStores, which WarningsAsErrors makes fatal;
# naming it `_` does not escape that, it escapes only the compiler's own
# -Wunused-variable. That is the shape AGENTS/cpp.md cat 27 fixes, and the
# reason it gives for it.
# Non-zero exit: a range-for over the view is back in the tree, or the gate's
# verdict on one of the four shapes has changed and cat 27's reason is stale.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang-tidy-23 > /dev/null 2>&1 || exit 2

# The sources live under cpp/tests so clang-tidy finds the configuration by
# walking up, which is how the gate runs: pointed at a configuration file from
# elsewhere it inherits no parent and enables no check at all.
work=$(mktemp -d cpp/tests/.tidy-shapes-XXXXXX) || exit 2
trap 'rm -rf "$work"' EXIT

cat > "$work/bare.cpp" << 'EOF'
#include <ranges>
#include <vector>
static void run(int n) {
    std::vector<int> out;
    for (auto const level : std::views::repeat(0, n)) out.push_back(1);
    (void)out.size();
}
EOF
sed 's/auto const level/auto const _/' "$work/bare.cpp" > "$work/underscore.cpp"
sed 's/auto const level/[[maybe_unused]] auto const level/' "$work/bare.cpp" \
    > "$work/annotated.cpp"
cat > "$work/algorithm.cpp" << 'EOF'
#include <algorithm>
#include <ranges>
#include <vector>
static void run(int n) {
    std::vector<int> out;
    std::ranges::for_each(std::views::repeat(0, n), [&out](auto) { out.push_back(1); });
    (void)out.size();
}
EOF

# One finding of the analyzer's own is what the refusal is made of; the file
# reports nothing else, so the whole of clang-tidy's verdict is its exit status.
verdict() {
    # The redirection is written outside the subshell, since the path is
    # relative to the repository root and the gate's own directory is cpp.
    if (cd cpp && clang-tidy-23 --quiet "tests/${work##*/}/$1.cpp" -- -std=c++23 2>&1) \
        > "$work/$1.out"; then echo clean; else echo refused; fi
}

status=0
expect() {
    got=$(verdict "$1")
    [ "$got" = "$2" ] && return 0
    echo "$1.cpp: gate says $got, cat 27 says $2"
    sed -n '1,6p' "$work/$1.out"
    status=1
}

expect bare refused
expect underscore refused
expect annotated clean
expect algorithm clean

# The refusal is the dead store, not some other finding that happens to fire.
for shape in bare underscore; do
    grep -q 'clang-analyzer-deadcode.DeadStores' "$work/$shape.out" || {
        echo "$shape.cpp: refused by something other than the dead store"
        sed -n '1,6p' "$work/$shape.out"
        status=1
    }
done

# The compiler's own diagnostic is the half that reaches only the named form:
# it is silent on `_`, and the build passes no -Wall, so the gate is the wall.
clang++-23 -std=c++23 -Wall -Wextra -c "$work/bare.cpp" -o /dev/null 2> "$work/bare.cc.out"
grep -q 'unused variable' "$work/bare.cc.out" || {
    echo "the compiler no longer warns on the named form under -Wall"
    status=1
}
clang++-23 -std=c++23 -Wall -Wextra -c "$work/underscore.cpp" -o /dev/null \
    2> "$work/underscore.cc.out"
grep -q 'unused variable' "$work/underscore.cc.out" && {
    echo "the compiler now warns on \`_\`, which it exempted"
    status=1
}

# The ruled shape costs nothing where it lands inside a benchmark's timed
# region: at -O3, which is what CMAKE_CXX_FLAGS_RELEASE gives the harnesses,
# the algorithm and the range-for over the same view emit the same
# instructions, the lambda being inlined away. Measured against the counting
# loop they replace, the difference is the branch that enters the loop, `jle`
# against `je`, which is the negative bound the view treats as a precondition
# rather than as a condition.
cat > "$work/shape_algorithm.cpp" << 'EOF'
#include <algorithm>
#include <ranges>
int work(int);
void run(int n) {
    std::ranges::for_each(std::views::repeat(0, n), [&](auto) { (void)work(n); });
}
EOF
cat > "$work/shape_rangefor.cpp" << 'EOF'
#include <ranges>
int work(int);
void run(int n) {
    for ([[maybe_unused]] auto const i : std::views::repeat(0, n)) (void)work(n);
}
EOF
for shape in algorithm rangefor; do
    clang++-23 -std=c++23 -O3 -S -o "$work/$shape.s" "$work/shape_$shape.cpp" || exit 2
    grep -vE '^[[:space:]]*\.|^#' "$work/$shape.s" > "$work/$shape.insns"
done
cmp -s "$work/algorithm.insns" "$work/rangefor.insns" || {
    echo "the algorithm and the range-for no longer emit the same instructions:"
    diff "$work/rangefor.insns" "$work/algorithm.insns" | head -10
    status=1
}

# The tree itself holds the ruled shape and none of the refused ones. Each file
# is read as one line, because the formatter breaks a header that runs past the
# column limit and a per-line pattern would miss exactly the long ones. What
# stands between the `for (` and the colon is a declaration, so a pattern that
# admits no parenthesis there reads the header and not a body that calls the
# algorithm.
refused=""
while IFS= read -r -d '' file; do
    tr '\n' ' ' < "$file" \
        | grep -qE 'for *\([^;{()]*: *std::views::repeat' \
        && refused="$refused$file"$'\n'
done < <(git ls-files -z -- '*.cpp' '*.hpp')
[ -z "$refused" ] || {
    echo "a count with no position written as a range-for, not as an algorithm:"
    printf '%s' "$refused" | head -20
    status=1
}

exit "$status"
