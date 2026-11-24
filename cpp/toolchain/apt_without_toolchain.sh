#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Runs apt-get over every apt source but the two install.sh beside this script
# writes.  A refresh reading those waits on their servers for any package, and
# an answer like a 503 from one fails it, so a step after the toolchain install
# that takes a package the toolchain's cache cannot hold (valgrind, whose
# libc6-dbg pins the image's libc6 exactly) runs apt through here.
#
# Usage: cpp/toolchain/apt_without_toolchain.sh ARGUMENT...
#   ARGUMENT  an argument of apt-get, as `sudo apt-get ARGUMENT...` takes it
#
# Exits 2 on a usage error, and otherwise with apt-get's own status.
set -euo pipefail

(($# >= 1)) || { echo "usage: cpp/toolchain/apt_without_toolchain.sh ARGUMENT..." >&2; exit 2; }
parts=$(mktemp -d)
trap 'rm -rf "$parts"' EXIT
find /etc/apt/sources.list.d -maxdepth 1 -type f ! -name llvm23.list ! -name ubuntu-toolchain-r.list \
    -exec cp -t "$parts" {} +
sudo apt-get -o "Dir::Etc::SourceParts=$parts" "$@"
