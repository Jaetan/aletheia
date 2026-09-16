#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/backend.hpp.
# Claim: the backend interface hands out its state as an owning handle and takes
# it back typed, so no call site holds or releases it by hand, and the injection
# block is reachable only through a factory that checks its arrays.
# Non-zero exit: a method takes the state as an untyped pointer, init returns
# one, the release primitive is public, or the injection block is an aggregate a
# caller can fill in unchecked.
set -eu
root=$(git rev-parse --show-toplevel)
cd "$root"
header=cpp/include/aletheia/backend.hpp
fail=0

# Every virtual taking or returning the state must speak in the handle.
if grep -nE '^\s+\[?\[?nodiscard?\]?\]?\s*virtual.*\bvoid\*' "$header"; then
    echo "FAIL: a virtual method still carries the state as an untyped pointer"
    fail=1
fi
if ! grep -q 'virtual auto init() -> BackendState = 0;' "$header"; then
    echo "FAIL: init does not hand out an owning handle"
    fail=1
fi

# close is the release primitive and belongs to the handle alone.
close_line=$(grep -n 'virtual auto close(void\* state) -> void = 0;' "$header" | cut -d: -f1)
protected_line=$(grep -n '^protected:' "$header" | head -1 | cut -d: -f1)
if [ -z "$close_line" ] || [ -z "$protected_line" ] || [ "$close_line" -lt "$protected_line" ]; then
    echo "FAIL: the release primitive is not behind the protected section"
    fail=1
fi
if ! grep -q 'friend class BackendState;' "$header"; then
    echo "FAIL: the handle is not the befriended releaser"
    fail=1
fi

# The injection block is a class with a checking factory, never an aggregate.
if ! grep -q 'static auto create(std::span<const std::uint32_t> indices,' "$header"; then
    echo "FAIL: the injection block has no checking factory"
    fail=1
fi
if grep -q 'struct SignalInjection' "$header"; then
    echo "FAIL: the injection block is an aggregate a caller can fill in unchecked"
    fail=1
fi

[ "$fail" -eq 0 ] || exit 1
echo "PASS: the state crosses as a handle and the injection block is checked"
