#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: the version in project(aletheia-cpp VERSION ...) is the release
# version every other binding stamps (python/pyproject.toml, rust/Cargo.toml,
# rust/excel/Cargo.toml, and the first three components of
# haskell-shim/aletheia.cabal), as the release runbook requires them to move
# together. Non-zero exit: any stamp differs from the CMake one.
set -u
cd "$(dirname "$0")/.." || exit 2
cmake_v=$(sed -nE 's/^project\(aletheia-cpp VERSION ([0-9.]+) .*/\1/p' cpp/CMakeLists.txt)
py_v=$(sed -nE 's/^version = "([0-9.]+)"/\1/p' python/pyproject.toml | head -1)
rs_v=$(sed -nE 's/^version = "([0-9.]+)"/\1/p' rust/Cargo.toml | head -1)
xl_v=$(sed -nE 's/^version = "([0-9.]+)"/\1/p' rust/excel/Cargo.toml | head -1)
hs_v=$(sed -nE 's/^version:\s+([0-9]+\.[0-9]+\.[0-9]+).*/\1/p' haskell-shim/aletheia.cabal | head -1)
status=0
for pair in "python:$py_v" "rust:$rs_v" "rust-excel:$xl_v" "haskell:$hs_v"; do
    [ "${pair#*:}" = "$cmake_v" ] || { echo "$pair differs from cmake $cmake_v"; status=1; }
done
[ -n "$cmake_v" ] || status=1
exit $status
