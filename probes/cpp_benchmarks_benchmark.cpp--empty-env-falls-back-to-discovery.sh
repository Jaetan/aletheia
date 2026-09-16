#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/benchmark.cpp.
# Claim: an ALETHEIA_LIB set to the empty string counts as unset, so the
# benchmark falls back to the kernel next to the repository build tree instead
# of handing "" to dlopen (which opens the program itself and aborts at the
# first symbol lookup). Builds the benchmark target first. Non-zero exit: the
# run with an empty variable fails. Exits 2 when cpp/build is not configured
# or the kernel is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] && [ -f build/libaletheia-ffi.so ] || exit 2
cmake --build cpp/build --target benchmark > /dev/null 2>&1 || exit 2
ALETHEIA_LIB= cpp/build/benchmark throughput --frames 50 --runs 1 --warmup 0 > /dev/null 2>&1
