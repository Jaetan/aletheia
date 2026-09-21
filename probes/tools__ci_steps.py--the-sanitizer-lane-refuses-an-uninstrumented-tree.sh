#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_ci_steps.py.
# Claim: a sanitizer lane refuses a build tree whose CMake cache does not name
# the sanitizer the lane asked for. CMake drops a cache whose compiler has
# changed and configures the tree afresh; a tree that comes back without
# ALETHEIA_SANITIZER builds every target uninstrumented, runs the whole battery
# green and reports as a sanitizer lane, so the lane reads the value back
# between the configure and the build. The guard is taken from the lane's own
# command rather than copied here, so a command that stops carrying it fails
# this probe instead of passing a copy.
# Non-zero exit: the lane's command carries no cache read-back, or the guard
# accepts a cache that names no sanitizer, or it refuses one that does.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
guard=$("$py" - <<'PYEOF'
from tools._ci_steps import sanitizer_ctest_cmd

command = sanitizer_ctest_cmd("address", "/dev/null")
parts = [part for part in command.split(" && ") if "CMakeCache.txt" in part]
print(parts[0] if len(parts) == 1 else "")
PYEOF
)
[ -n "$guard" ] || { echo "the address lane's command carries no cache read-back"; exit 1; }
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/build-asan" || exit 2
cache=$scratch/build-asan/CMakeCache.txt
printf 'CMAKE_BUILD_TYPE:STRING=Release\nALETHEIA_SANITIZER:STRING=address\n' > "$cache"
(cd "$scratch" && eval "$guard") > /dev/null 2>&1 ||
    { echo "the guard refuses a cache that names the sanitizer"; exit 1; }
printf 'CMAKE_BUILD_TYPE:STRING=Release\nALETHEIA_SANITIZER:STRING=\n' > "$cache"
if (cd "$scratch" && eval "$guard") > /dev/null 2>&1; then
    echo "the guard accepts a cache that names no sanitizer"
    exit 1
fi
exit 0
