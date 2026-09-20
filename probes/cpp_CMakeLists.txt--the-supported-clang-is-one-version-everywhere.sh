#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt, the workflows, Dockerfile.runtime, the CI steps,
# the probes, and every document that names the compiler.
# Claim: the Clang the policy line in cpp/CMakeLists.txt names is the one every
# toolchain site installs, invokes, caches and documents, and the mutation
# lane's sites all name the one Clang that tools/mutation_run.py runs Mull
# against.  A version below 19 is the runner's stock compiler, named only to
# say why it is not used; a line carrying a date is history; and a measurement
# record ("Measured on ...") names the compiler that produced the numbers it
# introduces, which is a fact about the artifact rather than a toolchain site.
# Non-zero exit: one site was left on another version, so a bump is half done
# and the tree builds, tests or documents against two compilers.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

policy=$(grep -oE 'CMAKE_CXX_COMPILER_VERSION VERSION_LESS [0-9]+' cpp/CMakeLists.txt \
    | grep -oE '[0-9]+$')
[ -n "$policy" ] || { echo "cpp/CMakeLists.txt states no supported Clang"; exit 1; }
lane=$(grep -oE 'mull-runner-[0-9]+' tools/mutation_run.py | sort -u | grep -oE '[0-9]+$')
case $lane in
    '') echo "tools/mutation_run.py names no Mull runner"; exit 1 ;;
    *$'\n'*) echo "tools/mutation_run.py names more than one Mull runner"; exit 1 ;;
esac

tokens='run-clang-tidy-[0-9]+|clang-tidy-[0-9]+|clang\+\+-[0-9]+|clang-[0-9]+|clang[0-9]+-|llvm-toolchain-noble-[0-9]+|llvm[0-9]+\.list|Clang [0-9]+|Clang \([0-9]+\)|mull-[a-z-]+-[0-9]+|llvm-[0-9]+-dev|libclang-[0-9]+-dev|/usr/lib/llvm-[0-9]+'

# check <label> <wanted version> <text>: every version token in the text is
# the wanted one, a version below 19, or on a dated line.
check() {
    local label=$1 want=$2 text=$3 hits
    hits=$(printf '%s\n' "$text" | grep -vE '20[0-9]{2}-[0-9]{2}-[0-9]{2}|^Measured on ' \
        | grep -noE "$tokens" | grep -vE "(^|[^0-9])$want([^0-9]|$)" \
        | while IFS= read -r hit; do
            [ "$(printf '%s' "$hit" | grep -oE '[0-9]+' | tail -1)" -ge 19 ] && printf '%s\n' "$hit"
        done)
    [ -z "$hits" ] || {
        echo "$label names a Clang other than $want:"
        printf '%s\n' "$hits" | sed 's/^/  /'
        status=1
    }
}

# The mutation job of the heavy-lanes workflow and the mutation block of the
# CMake file are the lane's own regions; everything before each is the
# supported toolchain's.
heavy=.github/workflows/pr-heavy-lanes.yml
check "$heavy (before the mutation job)" "$policy" "$(sed '/^  mutation:$/,$d' "$heavy")"
check "$heavy (mutation job)" "$lane" "$(sed -n '/^  mutation:$/,$p' "$heavy")"
cmake_split='# Opt-in via -DALETHEIA_MUTATION=ON'
check "cpp/CMakeLists.txt (policy)" "$policy" "$(sed "/$cmake_split/,\$d" cpp/CMakeLists.txt)"
check "cpp/CMakeLists.txt (mutation block)" "$lane" "$(sed -n "/$cmake_split/,\$p" cpp/CMakeLists.txt)"

for f in $(ls .github/workflows/*.yml | grep -v pr-heavy-lanes) Dockerfile.runtime \
    tools/_ci_steps.py tools/bundle_validate.py benchmarks/run_all.sh \
    AGENTS.md AGENTS/cpp.md CLAUDE.md DEPENDENCIES.md cpp/README.md cpp/src/ffi_backend.cpp \
    docs/architecture/CGO_NOTES.md docs/development/BENCHMARKS.md \
    docs/development/BRANCH_PR_HYGIENE.md docs/development/BUILDING.md \
    docs/development/DISTRIBUTION.md docs/development/RELEASE.md; do
    check "$f" "$policy" "$(grep -viE 'mull|mutation|llvm-[0-9]+-dev' "$f")"
done
for f in tools/mutation_run.py docs/operations/MUTATION.md docs/MUTATION_BENCH.yaml; do
    check "$f" "$lane" "$(cat "$f")"
done
# CI_LOCAL.md and CLAUDE.md each carry both: the sanitizer sentence and the
# Mull recipe.  Their mutation lines are the ones naming Mull.
check "docs/development/CI_LOCAL.md (toolchain)" "$policy" "$(grep -viE 'mull|mutation|llvm-[0-9]+-dev' docs/development/CI_LOCAL.md)"
check "docs/development/CI_LOCAL.md (mutation)" "$lane" "$(grep -iE 'mull|llvm-[0-9]+-dev' docs/development/CI_LOCAL.md)"
check "CLAUDE.md (mutation)" "$lane" "$(grep -iE 'mull' CLAUDE.md)"

# The probes compile with the supported compiler, except those that run the
# mutation lane or its plugin.
for f in probes/*.sh; do
    case $f in
        *mutation-lane*|*MUTATION_BENCH*|*mull*) check "$f" "$lane" "$(cat "$f")" ;;
        *) check "$f" "$policy" "$(cat "$f")" ;;
    esac
done

# The format gate's binary is the pip clang-format of the same major.
fmt=$(grep -oE '"clang-format>=[0-9]+' python/pyproject.toml | grep -oE '[0-9]+$')
[ "$fmt" = "$policy" ] || {
    echo "python/pyproject.toml pins clang-format $fmt, the supported Clang is $policy"
    status=1
}
exit "$status"
