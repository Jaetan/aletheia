# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes .gitignore.
# Claim: every build directory the C++ build file tells a reader to create is
# ignored, and the single-venv rule ignores only the sanctioned venv so a
# stray one shows up in git status. Non-zero exit: a documented build tree
# would be left untracked, the sanctioned venv is visible, or a venv outside
# it is hidden.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

# Every `cmake -B <dir>` the build file documents.
trees=$(grep -oE 'cmake -B [A-Za-z0-9_.-]+' cpp/CMakeLists.txt | awk '{print $3}' | sort -u)
[ -n "$trees" ] || { echo "the build file documents no build directory"; exit 2; }
for tree in $trees; do
    git check-ignore -q "cpp/$tree/probe" || {
        echo "a documented build tree is not ignored: cpp/$tree"
        status=1
    }
done

git check-ignore -q python/.venv/probe || {
    echo "the sanctioned venv is not ignored"
    status=1
}
for stray in .venv go/.venv rust/.venv; do
    if git check-ignore -q "$stray/probe"; then
        echo "a venv outside the sanctioned path is hidden: $stray"
        status=1
    fi
done
exit $status
