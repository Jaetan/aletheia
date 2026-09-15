#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: every build command the file's comments give is written from cpp/,
# the directory the file lives in, so a reader standing in one place can run
# any of them. A command naming a path through cpp/ belongs to a different
# working directory and is the defect. Non-zero exit: a documented command
# mixes the two, or the file documents no command at all.
set -u
cd "$(dirname "$0")/.." || exit 2
file=cpp/CMakeLists.txt
status=0

commands=$(grep -nE '^[[:space:]]*#.*(cmake (-B|--build)|mull-runner|ctest)' "$file")
[ -n "$commands" ] || { echo "the file documents no build command"; exit 1; }

offenders=$(printf '%s\n' "$commands" | grep -E '(-B|--build|-p|/)[[:space:]]*\.?/?cpp/' || true)
[ -z "$offenders" ] || {
    echo "a documented command is written from the repository root, not from cpp/:"
    printf '%s\n' "$offenders"
    status=1
}

# A configure line with no -S resolves its source from the working directory,
# which is the whole point of the convention: it must name a bare directory.
bare=$(printf '%s\n' "$commands" | grep -cE 'cmake -B[[:space:]]+[A-Za-z_][A-Za-z0-9_-]*')
[ "$bare" -ge 1 ] || {
    echo "no configure line names a bare build directory"
    status=1
}
exit $status
