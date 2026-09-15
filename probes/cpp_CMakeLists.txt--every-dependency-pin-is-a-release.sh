# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: every fetched dependency is pinned to a published release by tag and
# hash, never to a moving reference or a bare commit. A commit pin cannot be
# read as a version by a reader or a security advisory, and a pin with no hash
# is not a pin at all.
# Non-zero exit: a dependency is pinned to something other than a release, or
# a declaration carries no hash.
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

[ "$status" -eq 0 ] || exit 1
echo "PASS: every dependency is pinned to a release by tag and hash"
