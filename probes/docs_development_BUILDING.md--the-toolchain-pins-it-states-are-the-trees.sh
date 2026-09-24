#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md.
# Claim: the pins the prerequisites state are the tree's: the standard-library
# tag it checks out is the one aletheia.agda-lib depends on, the CMake floor is
# cpp/CMakeLists.txt's cmake_minimum_required, the Go floor is go/go.mod's go
# directive, and the Python floor is python/pyproject.toml's requires-python.
# The Clang version is another probe's claim.
# Non-zero exit: a stated pin differs from the tree's.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
status=0
stated=$(grep -oE 'git checkout v[0-9.]+' "$doc" | sort -u | grep -oE '[0-9.]+$')
tree=$(grep -oE 'standard-library-[0-9.]+' aletheia.agda-lib | grep -oE '[0-9.]+$')
[ "$(printf '%s\n' "$stated" | wc -l)" -eq 1 ] && [ "$stated" = "$tree" ] || { echo "stdlib: the guide checks out '$stated', aletheia.agda-lib depends on $tree"; status=1; }
stated=$(grep -oE 'cmake version [0-9.]+' "$doc" | grep -oE '[0-9.]+$' | sort -u)
tree=$(grep -oE 'cmake_minimum_required\(VERSION [0-9.]+' cpp/CMakeLists.txt | grep -oE '[0-9.]+$')
[ "$stated" = "$tree" ] || { echo "cmake: the guide says $stated, cpp/CMakeLists.txt requires $tree"; status=1; }
stated=$(grep -oE 'go version go[0-9.]+' "$doc" | grep -oE '[0-9]+\.[0-9]+' | sort -u)
tree=$(grep -oE '^go [0-9.]+' go/go.mod | grep -oE '[0-9]+\.[0-9]+')
[ "$stated" = "$tree" ] || { echo "go: the guide says $stated, go/go.mod says $tree"; status=1; }
stated=$(grep -oE 'requires-python = ">=[0-9.]+"' "$doc" | grep -oE '[0-9.]+' | sort -u)
tree=$(grep -oE 'requires-python = ">=[0-9.]+"' python/pyproject.toml | grep -oE '[0-9.]+')
[ -n "$stated" ] && [ "$stated" = "$tree" ] || { echo "python: the guide quotes '$stated', pyproject requires $tree"; status=1; }
[ "$status" -eq 0 ] && echo "PASS: the stdlib, CMake, Go and Python pins the guide states are the tree's"
exit "$status"
