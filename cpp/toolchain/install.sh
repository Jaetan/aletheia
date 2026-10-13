#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Installs the C++ toolchain on a CI runner: clang from apt.llvm.org, and
# libstdc++ 15 from the Ubuntu toolchain PPA, since the libstdc++ 14 of
# ubuntu-24.04 has no pipe form of std::ranges::to.
#
# Usage: cpp/toolchain/install.sh CACHE PACKAGE...
#   CACHE    the directory the workflow's cache step restores and saves
#   PACKAGE  a package to install, by its archive name
#
# Both archives are trusted with the key files beside this script and named by
# source lines written here, so trusting them asks no server: add-apt-repository
# would ask Launchpad's API for the PPA's key on every run, and a timeout there
# fails the job before anything of the tree runs.  A CACHE holding packages is
# installed by dpkg alone, so a warm run reaches no server either; apt refreshes
# its lists only to fill an empty CACHE, or to resolve what dpkg could not
# install from it (a dependency the runner image no longer carries).
#
# An archive that moves to another signing key is refused at the next refresh,
# apt naming the new key in a NO_PUBKEY error and exiting 100; a warm run makes
# no refresh, so the refusal waits for a run that does.  The archive's key file
# is then replaced with its new key (apt.llvm.org serves it as
# llvm-snapshot.gpg.key, keyserver.ubuntu.com serves the PPA's by fingerprint),
# checked against the archive's InRelease with gpgv, and its fingerprint below
# updated.
#
# Exits 1 when a key file is not the key it is named for, 2 on a usage error,
# and otherwise with the failing command's own status.
set -euo pipefail

(($# >= 2)) || { echo "usage: cpp/toolchain/install.sh CACHE PACKAGE..." >&2; exit 2; }
cache=$1
shift
here=$(dirname "$0")

# Each key file and the fingerprint of the key its archive signs with.
for entry in "apt.llvm.org.asc 6084F3CF814B57C1CF12EFD515CF4D18AF4F7421" \
    "ubuntu-toolchain-r.asc C8EC952E2A0E1FBDC5090F6A2C277A0A352154E5"; do
    read -r file fingerprint <<< "$entry"
    found=$(gpg --show-keys --with-colons "$here/$file" | awk -F: '$1 == "fpr" && !seen++ {print $10}')
    [[ $found == "$fingerprint" ]] ||
        { echo "::error::$here/$file holds key ${found:-none}, not $fingerprint" >&2; exit 1; }
done
sudo install -m 0644 "$here/apt.llvm.org.asc" "$here/ubuntu-toolchain-r.asc" /etc/apt/trusted.gpg.d/
echo "deb http://apt.llvm.org/noble/ llvm-toolchain-noble-23 main" |
    sudo tee /etc/apt/sources.list.d/llvm23.list > /dev/null
echo "deb https://ppa.launchpadcontent.net/ubuntu-toolchain-r/test/ubuntu noble main" |
    sudo tee /etc/apt/sources.list.d/ubuntu-toolchain-r.list > /dev/null

mkdir -p "$cache"
shopt -s nullglob
debs=("$cache"/*.deb)
if ((${#debs[@]} > 0)) && sudo dpkg -i "${debs[@]}"; then
    exit 0
fi
sudo apt-get update || {
    status=$?
    echo "::error::apt-get update failed; a NO_PUBKEY above names an archive's new key, which replaces its file in $here as this script's header says" >&2
    exit "$status"
}
if ((${#debs[@]} == 0)); then
    sudo apt-get install -y --download-only -o Dir::Cache::archives="$cache" "$@"
    sudo chown -R "$(id -u):$(id -g)" "$cache"
    debs=("$cache"/*.deb)
    if sudo dpkg -i "${debs[@]}"; then
        exit 0
    fi
fi
sudo apt-get -f install -y
