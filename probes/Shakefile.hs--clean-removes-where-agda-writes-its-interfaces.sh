#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes Shakefile.hs, the `clean` phony.
# Claim: clean removes the tree Agda writes its interfaces into, `_build/`
# under the project root, and names no place Agda never writes. A clean that
# leaves the interfaces behind re-derives MAlonzo from a type-check it did not
# run, and the reproducible-build gate then compares two builds sharing one
# interface set. Non-zero exit: the phony does not remove `_build/`, it still
# carries the dead `src` interface pattern, or an interface sits somewhere
# other than `_build/`, which is where Agda would have moved them.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

# The phony's body: from its header to the first line indented less than it.
body=$(awk '/^    phony "clean"/{f=1; next} f && /^    [^ ]/{exit} f' Shakefile.hs)
[ -n "$body" ] || { echo "no clean phony in Shakefile.hs"; exit 2; }

grep -q 'removeFilesAfter "_build"' <<<"$body" || {
    echo "clean does not remove _build/, where Agda writes its interfaces"
    status=1
}
if grep -q '"src".*agdai' <<<"$body"; then
    echo "clean names src for interfaces, where Agda writes none"
    status=1
fi

# Where the tree holds interfaces at all, every one is under _build/.
stray=$(find . -name '*.agdai' -not -path './_build/*' -not -path './dist-newstyle/*' -not -path './.git/*' | head -3)
[ -z "$stray" ] || {
    echo "interfaces outside _build/, which clean would leave behind:"
    echo "$stray"
    status=1
}
if [ -d _build ] && [ -z "$(find _build -name '*.agdai' -print -quit)" ]; then
    echo "_build/ exists and holds no interface: Agda writes them elsewhere now"
    status=1
fi
exit $status
