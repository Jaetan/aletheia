#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/stability_bench.cpp.
# Claim: ALETHEIA_STABILITY_CYCLES and ALETHEIA_STABILITY_FRAMES accept only
# a positive whole number; anything else is refused with a message and the
# harness's setup exit code (2), never silently replaced by the default. Builds
# the target first. Non-zero exit: a bad value was accepted. Exits 2 when
# cpp/build or the kernel is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] && [ -f build/libaletheia-ffi.so ] || exit 2
cmake --build cpp/build --target stability_bench > /dev/null 2>&1 || exit 2
export ALETHEIA_LIB=$PWD/build/libaletheia-ffi.so
for bad in abc 0 -3 5x ""; do
    ALETHEIA_STABILITY_CYCLES=$bad ALETHEIA_STABILITY_FRAMES=100 cpp/build/stability_bench > /dev/null 2>&1
    [ $? -eq 2 ] || { echo "accepted CYCLES='$bad'"; exit 1; }
    ALETHEIA_STABILITY_CYCLES=1 ALETHEIA_STABILITY_FRAMES=$bad cpp/build/stability_bench > /dev/null 2>&1
    [ $? -eq 2 ] || { echo "accepted FRAMES='$bad'"; exit 1; }
done
exit 0
