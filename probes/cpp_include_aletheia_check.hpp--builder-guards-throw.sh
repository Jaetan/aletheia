# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/check.hpp.
# Claim: the builders refuse the inputs their comments name: a range with lo
# above hi (stays_between, settles_between, then-stays_between), a negative
# time bound, and a millisecond bound whose microsecond conversion would
# overflow int64, each with std::invalid_argument. Non-zero exit: one of them
# is accepted. Links the built binding because the description builders name
# the kernel renderer. Exits 2 when the archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.a
yaml=$(find cpp/build/_deps -maxdepth 2 -name 'libyaml-cpp.a' | head -1)
xlsx=$(find cpp/build -maxdepth 3 -name 'libOpenXLSX.a' | head -1)
[ -f "$lib" ] && [ -n "$yaml" ] && [ -n "$xlsx" ] || exit 2
scratch=cpp/build/probe-scratch/check-guards
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/check.hpp>
#include <chrono>
#include <limits>
#include <stdexcept>
using namespace aletheia;
template <typename F> static auto throws_invalid(F f) -> bool {
    try { f(); } catch (const std::invalid_argument&) { return true; } catch (...) { return false; }
    return false;
}
int main() {
    const auto lo = PhysicalValue::of(1, 1);
    const auto hi = PhysicalValue::of(2, 1);
    int failures = 0;
    failures += !throws_invalid([&] { (void)check::signal("S").stays_between(hi, lo); });
    failures += !throws_invalid([&] { (void)check::signal("S").settles_between(hi, lo); });
    failures += !throws_invalid([&] { (void)check::when("A").exceeds(lo).then("B").stays_between(hi, lo); });
    failures += !throws_invalid([&] { (void)check::signal("S").settles_between(lo, hi).within(std::chrono::milliseconds{-1}); });
    failures += !throws_invalid([&] {
        (void)check::signal("S").settles_between(lo, hi).within(
            std::chrono::milliseconds{std::numeric_limits<std::int64_t>::max() / 1000 + 1});
    });
    failures += !throws_invalid([&] { (void)check::when("A").exceeds(lo).then("B").equals(hi).within(std::chrono::milliseconds{-5}); });
    // and the accepted edge: the largest bound that fits
    try { (void)check::signal("S").settles_between(lo, hi).within(std::chrono::milliseconds{std::numeric_limits<std::int64_t>::max() / 1000}); }
    catch (...) { ++failures; }
    return failures;
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" "$yaml" "$xlsx" -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t"
