#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: a mutation build's objects are cached under the plugin's bytes and the
# Mull configuration's bytes, not under the command line alone. What the object
# holds depends on both: the plugin writes the mutants into it, and the
# configuration says which ones. Neither is on the command line by content, the
# plugin only by the path it is read from, so the launcher names both to ccache
# as extra files to hash and hashes the compiler by content.
# Two arms. The first reads the configured tree's rules: they must run the
# compiler through ccache, naming the plugin and the configuration, so that the
# recipe the documentation prints gets the same safety a lane does. The second
# compiles one unit through that same launcher shape and reads ccache's own
# counters: with the two named, changing either misses; with neither named, the
# same change hits and the earlier configuration's object is served. Without
# that second arm the first proves only that a string is present.
# Non-zero exit: the rules do not name them, or a change that must miss hits.
# Skipped (exit 0) when ccache or the plugin is not installed, since the claim
# is then untestable.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v ccache > /dev/null || { echo "ccache not installed, claim untestable"; exit 0; }
command -v clang++-23 > /dev/null || { echo "clang++-23 not installed, claim untestable"; exit 0; }
plugin="$HOME/.local/bin/mull-ir-frontend-23"
[ -x "$plugin" ] || { echo "plugin not installed, claim untestable"; exit 0; }

scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT

tree=cpp/build/probe-scratch/mutation-launcher
rm -rf "$tree"
cmake -S cpp -B "$tree" -DALETHEIA_MUTATION=ON -DCMAKE_C_COMPILER=clang-23 \
    -DCMAKE_CXX_COMPILER=clang++-23 > "$scratch/configure.log" 2>&1 ||
    { echo "configure failed:"; tail -5 "$scratch/configure.log"; exit 1; }
grep -q '^CCACHE_PROGRAM:FILEPATH=/' "$tree/CMakeCache.txt" ||
    { echo "ccache not found by the configure, claim vacuous"; exit 1; }
config=$(sed -n 's/^ALETHEIA_MULL_CONFIG:FILEPATH=//p' "$tree/CMakeCache.txt")
[ -n "$config" ] || { echo "the configure recorded no ALETHEIA_MULL_CONFIG"; exit 1; }
rules=$tree/CMakeFiles/aletheia-cpp.dir/build.make
for wanted in "CCACHE_EXTRAFILES=$plugin:$config" "CCACHE_COMPILERCHECK=content"; do
    grep -qF "$wanted" "$rules" || { echo "the mutation build's rules do not carry $wanted"; exit 1; }
done

# One unit, compiled the way the rules compile one, with its own cache each
# time so a counter reads this probe's compiles and nothing else.
cp "$plugin" "$scratch/plugin.so"
cp "$config" "$scratch/config.yml"
printf 'int answer() { return 40 + 2; }\n' > "$scratch/unit.cpp"
# `env` carries the assignments, because a word an expansion produces is not
# read as one: the shell decides what is an assignment before it expands.
compile() { # <cache dir> <extra files, empty for none>
    env CCACHE_DIR="$scratch/$1" CCACHE_COMPILERCHECK=content \
        ${2:+CCACHE_EXTRAFILES="$2"} MULL_CONFIG="$scratch/config.yml" \
        ccache clang++-23 -std=c++23 -g -O0 -grecord-command-line \
        -fpass-plugin="$scratch/plugin.so" -c "$scratch/unit.cpp" \
        -o "$scratch/unit.o" > /dev/null 2>&1
}
verdict() { # <cache dir> -> hit | miss
    env CCACHE_DIR="$scratch/$1" ccache --show-stats |
        grep -qE '^  Hits: +1 ' && echo hit || echo miss
}
zero() { env CCACHE_DIR="$scratch/$1" ccache --zero-stats > /dev/null; }
named="$scratch/plugin.so:$scratch/config.yml"

status=0
check() { # <what changed> <extra files> <cache> <wanted>
    zero "$3"; compile "$3" "$2" || { echo "the compile itself failed ($1)"; exit 1; }
    got=$(verdict "$3")
    [ "$got" = "$4" ] ||
        { echo "$1: wanted a $4, read a $got"; status=1; }
}
for arm in named unnamed; do
    extra=$named; [ "$arm" = unnamed ] && extra=""
    # The first compile of each cache fills it; the change after it is the claim.
    check "$arm, filling the cache" "$extra" "cache-config-$arm" miss
    printf '\n# a slice holds one more file out\n' >> "$scratch/config.yml"
    check "$arm, the configuration changed" "$extra" "cache-config-$arm" \
        "$([ "$arm" = named ] && echo miss || echo hit)"
    cp "$config" "$scratch/config.yml"

    check "$arm, filling the cache" "$extra" "cache-plugin-$arm" miss
    printf '\0' >> "$scratch/plugin.so"
    check "$arm, the plugin changed" "$extra" "cache-plugin-$arm" \
        "$([ "$arm" = named ] && echo miss || echo hit)"
    cp "$plugin" "$scratch/plugin.so"
done
[ "$status" -eq 0 ] &&
    echo "PASS: a mutation object is cached under the plugin's bytes and the configuration's"
exit "$status"
