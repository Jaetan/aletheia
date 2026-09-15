# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: every dependency the build fetches is pinned to a published release
# by tag and hash, never to a moving reference or a bare commit, and the set
# it fetches is the set this file declares. A commit pin cannot be read as a
# version by a reader or a security advisory, a pin with no hash is not a pin
# at all, and a dependency that fetches one of its own is neither until this
# file names it too.
# Non-zero exit: a dependency is pinned to something other than a release, a
# declaration carries no hash, or the configured tree fetched something this
# file does not declare.
set -eu
root=$(git rev-parse --show-toplevel)
cd "$root"
cmake=cpp/CMakeLists.txt
status=0

# Every URL line under a FetchContent_Declare, with the hash line that follows.
urls=$(grep -nE '^\s+URL https://' "$cmake" | sed 's/^ *//')
[ -n "$urls" ] || { echo "FAIL: no dependency declarations found"; exit 1; }

while IFS= read -r line; do
    num=${line%%:*}
    url=${line#*URL }
    case "$url" in
        */archive/refs/tags/*|*/releases/download/*) ;;
        *) echo "FAIL: line $num is not pinned to a release: $url"; status=1 ;;
    esac
    next=$(sed -n "$((num + 1))p" "$cmake")
    case "$next" in
        *URL_HASH\ SHA256=*) ;;
        *) echo "FAIL: the declaration at line $num carries no hash"; status=1 ;;
    esac
done <<EOD
$urls
EOD

# What the configured tree actually fetched, against what this file declares.
# A dependency that fetches its own dependencies shows up here and nowhere in
# the declaration list, which is the case this arm exists for.
deps=cpp/build/_deps
if [ -d "$deps" ]; then
    declared=$(grep -oE '^[[:space:]]*FetchContent_Declare\([A-Za-z0-9_.-]+' "$cmake" \
        | sed 's/^[[:space:]]*FetchContent_Declare(//' | tr 'A-Z' 'a-z' | sort -u)
    fetched=$(find "$deps" -maxdepth 1 -type d -name '*-subbuild' -printf '%f\n' \
        | sed 's/-subbuild$//' | tr 'A-Z' 'a-z' | sort -u)
    for name in $fetched; do
        printf '%s\n' "$declared" | grep -qxF "$name" || {
            echo "FAIL: the build fetched $name, which this file does not declare"
            status=1
        }
    done
else
    echo "FAIL: cpp/build is not configured, so what the build fetches cannot be read"
    status=1
fi

[ "$status" -eq 0 ] || exit 1
echo "PASS: every dependency the build fetches is declared here and pinned to a release by tag and hash"
