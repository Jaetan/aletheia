#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the review store's own snapshot machinery.
# Claim: the snapshot stages every path the round has changed, whether the path
# was already tracked or the round created it. It stages exactly the list in
# .git/frev/touched.txt, so a file edited but never added to that list is
# written into no tree, and the commit that claims to carry the change carries
# a tree without it, which may not even build. A path the round creates is not
# visible in a diff against the base tree at all, so untracked paths are read
# against .git/frev/untracked-baseline.txt, which records what was already
# untracked when the round opened.
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

baseline=.git/frev/untracked-baseline.txt
if [ -f "$baseline" ]; then
    for path in $(git ls-files --others --exclude-standard); do
        grep -qxF "$path" "$baseline" && continue
        # A baseline entry ending in / stands for everything beneath it, which
        # is how a generated corpus is recorded without listing each file.
        prefixed=0
        while IFS= read -r entry; do
            case "$entry" in
                */) case "$path" in "$entry"*) prefixed=1; break;; esac;;
            esac
        done < "$baseline"
        [ "$prefixed" -eq 1 ] && continue
        covered "$path" || {
            echo "created but never staged: $path"
            missing=1
        }
    done
else
    echo "no untracked baseline recorded, so the created-path half is untestable."
    echo "Capture one at round open, before the round creates anything, with:"
    echo "  git ls-files --others --exclude-standard > $baseline"
    echo "and add a line ending in / for any directory a tool fills as it runs."
    missing=1
fi

[ "$missing" -eq 0 ] || exit 1
echo "PASS: every path the round changed is one the snapshot stages"
