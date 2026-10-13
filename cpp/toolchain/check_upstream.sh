#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Refuses a C++ toolchain built from other upstream versions than the ones
# below.  An install that downloads takes the archives' newest builds, and
# apt.llvm.org keeps no older one, so a cache the platform evicts is filled
# again with whatever the archives carry that day, under the same key.  A
# rebuild of a recorded version passes: apt.llvm.org's ~++<date>+<hash>
# snapshot suffix and the PPA's Debian revision are not compared.  A new
# upstream version passes once its row here moves and every workflow's
# toolchain cache key moves to its next suffix (the mutation lane's ccache
# keys carry it too), so that no cache holds the builds it replaces.
#
# Exits 1 naming each source whose installed upstream versions differ from
# its row.
set -euo pipefail

installed=$(dpkg-query -W -f '${db:Status-Status} ${source:Package} ${source:Upstream-Version}\n')
status=0
# Each source package the toolchain is built from and its upstream version.
for entry in "llvm-toolchain-23 23.1.2" "gcc-15 15.2.0" "gcc-16 16-20260315"; do
    read -r source upstream <<< "$entry"
    found=$(awk -v source="$source" '$1 == "installed" && $2 == source {sub(/~.*/, "", $3); print $3}' <<< "$installed" |
        sort -u | paste -sd ' ')
    if [[ $found != "$upstream" ]]; then
        echo "::error::$source is installed at upstream ${found:-none}, not $upstream; a new upstream moves its row in cpp/toolchain/check_upstream.sh and every workflow's toolchain cache key" >&2
        status=1
    fi
done
exit "$status"
