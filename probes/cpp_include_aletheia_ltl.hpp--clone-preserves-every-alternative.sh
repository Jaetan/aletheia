#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/ltl.hpp.
# Claim: ltl::clone deep-copies a formula tree without changing it, for every
# formula alternative and every predicate alternative, and the copy owns its
# own children. Shown by serialising a formula that uses all of them through
# the binding's own wire serialiser before and after cloning, and by
# destroying the original before serialising the clone. Non-zero exit: the
# two serialisations differ. Exits 2 when the archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
json=$(find cpp/build/_deps -maxdepth 2 -type d -name 'json-src' | head -1)
[ -f "$lib" ] && [ -n "$json" ] || exit 2
scratch=cpp/build/probe-scratch/ltl-clone
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/ltl.hpp>
#include "detail/json.hpp"
#include <cstdio>
#include <memory>
#include <span>
#include <string>
using namespace aletheia;
static auto pv(int n) -> PhysicalValue { return PhysicalValue::of(n, 1); }
static auto every_formula() -> LtlFormula {
    using namespace ltl;
    const SignalName s{"S"};
    auto a = atomic(equals(s, pv(1)));
    auto b = atomic(less_than(s, pv(2)));
    auto c = atomic(greater_than(s, pv(3)));
    auto d = atomic(less_than_or_equal(s, pv(4)));
    auto e = atomic(greater_than_or_equal(s, pv(5)));
    auto f = atomic(between(s, pv(6), pv(7)));
    auto g = atomic(changed_by(s, Delta{Rational{8, 1}}));
    auto h = atomic(stable_within(s, Tolerance{Rational{9, 1}}));
    auto unary = both(negate(clone(a)), either(next(clone(b)), weak_next(clone(c))));
    auto temporal = until(always(clone(d)), release(eventually(clone(e)), clone(f)));
    auto metric = MetricUntil{Timestamp{10}, std::make_unique<LtlFormula>(within(Timestamp{11}, clone(g))),
                              std::make_unique<LtlFormula>(always_within(Timestamp{12}, clone(h)))};
    auto metric_release = MetricRelease{Timestamp{13}, std::make_unique<LtlFormula>(std::move(metric)),
                                        std::make_unique<LtlFormula>(std::move(temporal))};
    return both(std::move(unary), LtlFormula{std::move(metric_release)});
}
int main() {
    auto original = std::make_unique<LtlFormula>(every_formula());
    const auto before = detail::serialize_set_properties(std::span<const LtlFormula>{original.get(), 1});
    auto copy = ltl::clone(*original);
    original.reset();
    const auto after = detail::serialize_set_properties(std::span<const LtlFormula>{&copy, 1});
    if (before != after || before.size() < 200) { std::printf("differs or too small (%zu bytes)\n", before.size()); return 1; }
    std::printf("identical, %zu bytes\n", before.size());
    return 0;
}
CPP
clang++-23 -std=c++23 -Icpp/include -Icpp/src -I"$json/include" "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t"
