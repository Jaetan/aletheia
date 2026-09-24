#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the build-tree cache of .github/workflows/, which restores the
# interface directory _build/ with every file's mtime reset.
# Claim: Agda reuses an interface file however its mtime compares to the
# source's, judging it by the source's hash and the imported interfaces'
# hashes, and re-checks a module only when its interface is missing or stale.
# The command-line checker prints one Checking line per module it re-checks
# and none for an interface it loads. With every interface dated 2020 and
# every source dated now, loading a proof-only module re-checks nothing;
# with one imported interface deleted, it re-checks exactly that module.
# The probe dates every interface under _build/ to 2020 and deletes one that
# its own last run writes back; the sources it leaves alone, since a tracked
# file's mtime is the tree's, and checks instead that none is older than the
# interfaces' date, which a checkout guarantees.
# Non-zero exit: Agda re-checked a module whose interface was current, or
# loaded a module whose interface was gone. Exits 2 when agda is missing, a
# source is dated before the interfaces, or any of the three runs fails to
# check, so a crash never reads as a pass.
set -u
cd "$(dirname "$0")/.." || exit 2
agda=$(command -v agda) || agda=/home/nicolas/.cabal/bin/agda
[ -x "$agda" ] || exit 2
mod=src/Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda
version=$("$agda" --numeric-version) || exit 2
dep=_build/$version/agda/src/Aletheia/DBC/TextParser/Properties/Aggregator/Universal.agdai
out=tools/ci-output/probe-scratch/agda-interface-reuse.log
mkdir -p "$(dirname "$out")" || exit 2
check() {
    "$agda" +RTS -M16G -RTS "$mod" > "$out" 2>&1 && return
    echo "agda exited $? :"; tail -n 5 "$out"; exit 2
}
rechecked() { grep -cE '^ *Checking ' "$out"; }
check
[ -f "$dep" ] || { echo "baseline wrote no $dep"; exit 2; }
find _build -name '*.agdai' -exec touch -d '2020-01-01' {} +
old=$(find src -name '*.agda' ! -newermt '2020-01-01' | head -1)
[ -z "$old" ] || { echo "a source is dated before the interfaces: $old"; exit 2; }
check; n=$(rechecked)
echo "sources newer than every interface: $n modules re-checked"
[ "$n" -eq 0 ] || exit 1
rm "$dep"
check; n=$(rechecked)
echo "one imported interface deleted: $n modules re-checked"
[ "$n" -eq 1 ] || exit 1
[ -f "$dep" ] || { echo "the load wrote no $dep back"; exit 1; }
