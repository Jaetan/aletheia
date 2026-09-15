#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/mock_backend.cpp.
# Claim (as the public headers and the feature matrix state it): a consumer
# holding only the installed headers can call make_mock_backend and get an
# answer back, because the factory hands out a canned-ack backend. Non-zero
# exit: the backend refuses, so the documented canned answers do not exist.
# Exits 2 when the library archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] || exit 2
scratch=cpp/build/probe-scratch/public-mock
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/backend.hpp>

#include <iostream>
#include <string>

int main() {
    auto backend = aletheia::make_mock_backend();
    if (!backend)
        return 3;
    try {
        auto state = backend->init();
        const std::string answer = backend->process(state, R"({"command":"ping"})");
        return answer.empty() ? 4 : 0;
    } catch (const aletheia::AletheiaException& e) {
        std::cout << "refused: " << e.error().message() << "\n";
        return 1;
    }
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -3 "$scratch/compile.log"; exit 1; }
"$scratch/t"
