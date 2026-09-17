#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes .github/workflows/*.yml, Dockerfile.runtime and
# docs/development/BUILDING.md.
# Claim: every place that installs a C++ standard library for the supported
# Clang installs the same one, the document saying which one is that version,
# and no .deb cache key can serve a cache filled before the move.  Non-zero
# exit: one install site was missed, the document and the workflows disagree,
# or a cache key was left unbumped so a warm runner reuses the old package.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

# The version is read from the workflows rather than written here, so the probe
# follows the next bump instead of pinning this one.
version=$(grep -hoE 'libstdc\+\+-[0-9]+-dev' .github/workflows/*.yml \
    | sort -u | sed 's/libstdc++-//; s/-dev//')
case $version in
    '')  echo "no workflow installs a libstdc++ -dev package"; exit 1 ;;
    *' '*|*$'\n'*)
        echo "the workflows install more than one libstdc++ version:"
        printf '%s\n' "$version"
        status=1 ;;
esac
[ "$status" -eq 0 ] || exit "$status"

# Every toolchain .deb download block must name the library: a block taking
# clang-23 alone silently keeps whatever standard library the image ships.
# Blocks are counted by the cache-dir option each one carries, and the package
# names are counted off comment-stripped lines so prose cannot inflate either.
for wf in .github/workflows/*.yml; do
    packages=$(sed 's/#.*//' "$wf")
    blocks=$(printf '%s\n' "$packages" | grep -cF 'Dir::Cache::archives' || true)
    [ "$blocks" -gt 0 ] || continue
    lib_sites=$(printf '%s\n' "$packages" | grep -cE "libstdc\+\+-$version-dev" || true)
    [ "$lib_sites" -eq "$blocks" ] || {
        echo "$wf downloads a toolchain at $blocks site(s), naming the library at $lib_sites"
        status=1
    }
done

# The release image's C++ verify stage builds the bundled binding, so it must
# not accept a library the release lane itself rejects.
grep -qE "libstdc\+\+-$version-dev" Dockerfile.runtime || {
    echo "Dockerfile.runtime does not install libstdc++-$version-dev"
    status=1
}
stray=$(grep -oE 'libstdc\+\+-[0-9]+-dev' Dockerfile.runtime \
    | grep -vF "libstdc++-$version-dev" | sort -u)
[ -z "$stray" ] || {
    echo "Dockerfile.runtime also installs a libstdc++ the workflows do not:"
    printf '%s\n' "$stray"
    status=1
}

# A .deb cache filled before the move contains the old package only, so a key
# that did not change would hand a warm runner the very thing this bump drops.
# The key's clang half is matched literally: a compiler bump is its own event
# with its own key, and this probe speaks only for the standard library.
for wf in .github/workflows/*.yml; do
    grep -qE "libstdc\+\+-$version-dev" "$wf" || continue
    grep -qE "key: clang23.*libstdcxx$version" "$wf" || {
        echo "$wf installs the new library under a cache key that does not name it"
        status=1
    }
done

# The document states the version to a reader who never opens a workflow.
grep -qE "libstdc\+\+ $version" docs/development/BUILDING.md || {
    echo "BUILDING.md does not state that CI builds against libstdc++ $version"
    status=1
}

exit "$status"
