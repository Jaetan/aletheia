# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/yaml.cpp.
# Claim: a failure that is not a property of the document keeps its kind.
# Loading a check whose threshold is a decimal before any backend exists makes
# the kernel decimal parser refuse (the runtime is down), and the loader must
# return an Ffi-kinded error, not a Validation one, while a genuinely
# malformed document still returns Validation. Non-zero exit: either kind is
# wrong, or a load throws instead of returning. Exits 2 when the archive is
# not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] || exit 2
scratch=cpp/build/probe-scratch/yaml-kind
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/yaml.hpp>

#include <iostream>
using namespace aletheia;

int main() {
    int failures = 0;
    // No backend exists in this process, so the kernel decimal parser is down.
    const auto* const doc = "checks:\n  - name: c\n    signal: Speed\n"
                            "    condition: never_exceeds\n    value: 11.5\n";
    auto checks = load_checks_from_yaml_string(doc);
    if (checks) {
        std::cout << "expected a refusal with the runtime down\n";
        return 1;
    }
    if (checks.error().kind() != ErrorKind::Ffi) {
        std::cout << "kind was " << static_cast<int>(checks.error().kind()) << ", expected Ffi: "
                  << checks.error().message() << "\n";
        ++failures;
    }
    // A document that is not a checks list is the loader's own refusal, still
    // Validation, and it never reaches the kernel.
    auto malformed = load_checks_from_yaml_string("not: a checks list\n");
    if (malformed || malformed.error().kind() != ErrorKind::Validation) {
        std::cout << "malformed document did not return Validation\n";
        ++failures;
    }
    std::cout << "failures=" << failures << "\n";
    return failures == 0 ? 0 : 1;
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
env -u ALETHEIA_LIB "$scratch/t"
