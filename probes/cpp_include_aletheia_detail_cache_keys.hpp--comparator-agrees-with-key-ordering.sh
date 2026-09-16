#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/detail/cache_keys.hpp.
# Claim: FrameKeyLess orders keys exactly as FrameKey's defaulted three-way
# comparison does, for every mix of FrameKey and FrameKeyView operands, so a
# std::map keyed by FrameKey can be searched by FrameKeyView without ever
# missing or misplacing an entry; and the two hashers give equal hashes to
# equal keys. Checked over a deterministic pseudo-random set of keys that
# vary each field and payload length. Non-zero exit: a disagreement.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/cache-keys
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/detail/cache_keys.hpp>
#include <cstdint>
#include <cstdio>
#include <random>
#include <vector>
using namespace aletheia::detail;
int main() {
    std::mt19937 rng(20260915);
    std::uniform_int_distribution<int> small(0, 3);
    std::uniform_int_distribution<int> len(0, 9);
    std::uniform_int_distribution<int> byte(0, 2);
    std::vector<FrameKey> keys;
    for (int i = 0; i < 400; ++i) {
        FrameKey k{static_cast<std::uint32_t>(small(rng)), small(rng) % 2 == 0,
                   static_cast<std::uint8_t>(small(rng)), {}};
        const int n = len(rng);
        for (int j = 0; j < n; ++j) k.data.push_back(static_cast<std::byte>(byte(rng)));
        keys.push_back(std::move(k));
    }
    const FrameKeyLess less;
    long failures = 0;
    for (const auto& a : keys)
        for (const auto& b : keys) {
            const FrameKeyView va{a.id_value, a.is_extended, a.dlc, a.data};
            const FrameKeyView vb{b.id_value, b.is_extended, b.dlc, b.data};
            const bool expect = a < b;
            if (less(a, b) != expect || less(va, b) != expect || less(a, vb) != expect || less(va, vb) != expect)
                ++failures;
            if ((a == b) != (!less(a, b) && !less(b, a))) ++failures;
        }
    for (const auto& a : keys) {
        const SignalKey sa{a.id_value, a.is_extended, "sig"}, sb{a.id_value, a.is_extended, "sig"};
        if (SignalKeyHash{}(sa) != SignalKeyHash{}(sb)) ++failures;
        if (MessageKeyHash{}({a.id_value, a.is_extended}) != MessageKeyHash{}({a.id_value, a.is_extended})) ++failures;
    }
    std::printf("failures=%ld\n", failures);
    return failures == 0 ? 0 : 1;
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t"
