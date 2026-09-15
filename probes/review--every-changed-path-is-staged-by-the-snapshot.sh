# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the review store's own snapshot machinery.
# Claim: the snapshot stages every path the round has changed. It stages exactly
# the list in .git/frev/touched.txt, so a file edited but never added to that
# list is written into no tree, and the commit that claims to carry the change
# carries a tree without it, which may not even build.
# Skipped (exit 0) where no round is in progress, since the claim is then
# untestable. Non-zero exit: at least one changed path is outside the list.
set -u
cd "$(dirname "$0")/.." || exit 2
touched=.git/frev/touched.txt
[ -f "$touched" ] || {
    echo "no round in progress, claim untestable"
    exit 0
}
git rev-parse --verify --quiet refs/frev/base > /dev/null || {
    echo "no review base tree anchored, claim untestable"
    exit 0
}

# A list entry may name a directory, which stages everything under it, so a path
# is covered by itself or by any of its ancestors.
covered() {
    candidate=$1
    while [ -n "$candidate" ] && [ "$candidate" != "." ]; do
        grep -qxF "$candidate" "$touched" && return 0
        parent=${candidate%/*}
        [ "$parent" = "$candidate" ] && break
        candidate=$parent
    done
    return 1
}

missing=0
for path in $(git diff --name-only refs/frev/base; git diff --cached --name-only refs/frev/base); do
    covered "$path" || {
        echo "changed but never staged: $path"
        missing=1
    }
done

[ "$missing" -eq 0 ] || exit 1
echo "PASS: every path the round changed is one the snapshot stages"
