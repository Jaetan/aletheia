#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Installs the Rust that rust-toolchain.toml pins, with each COMPONENT asked
# for, and makes it rustup's default, so a program built outside the tree, as
# the bundle validation builds its consumers, uses it as the tree does.
#
# Usage: tools/install_rust_toolchain.sh [COMPONENT...]
#   COMPONENT  a rustup component to install beside the minimal profile
#
# Exits 1 when rust-toolchain.toml names no channel, and otherwise with the
# failing command's own status.
set -euo pipefail

file="$(dirname "$0")/../rust-toolchain.toml"
channel=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$file")
[[ -n $channel ]] || { echo "::error::$file names no channel" >&2; exit 1; }
components=()
for component; do
    components+=(--component "$component")
done
rustup toolchain install "$channel" --profile minimal --no-self-update "${components[@]}"
rustup default "$channel"
rustc --version
cargo --version
