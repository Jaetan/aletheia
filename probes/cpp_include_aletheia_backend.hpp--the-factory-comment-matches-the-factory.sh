#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/backend.hpp.
# Claim: the comment on the public mock factory describes the object the factory
# hands out. It says the backend answers rather than queues, so a consumer
# holding only the installed headers gets an answer from every operation.
# Non-zero exit: the comment claims an answer the object does not give, or the
# object answers while the comment still describes a queue.
# Exits 2 when the library archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
header=cpp/include/aletheia/backend.hpp
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] || exit 2

# What the comment claims.
claims_answer=0
grep -q 'answers every operation' "$header" && claims_answer=1

scratch=cpp/build/probe-scratch/factory-comment
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/backend.hpp>

#include <string>

// Every endpoint the comment quantifies over, driven through the public
// factory alone.
int main() {
    auto backend = aletheia::make_mock_backend();
    if (!backend)
        return 3;
    auto state = backend->init();
    if (backend->process(state, R"({"command":"startStream"})").empty())
        return 4;
    if (backend->start_stream_binary(state).empty())
        return 4;
    if (backend->end_stream_binary(state).empty())
        return 4;
    if (backend->format_dbc_binary(state).empty())
        return 4;
    // Repeating it proves the answer is fixed rather than consumed.
    if (backend->start_stream_binary(state) != backend->start_stream_binary(state))
        return 5;
    return 0;
}
CPP
clang++-23 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread \
    -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -3 "$scratch/compile.log"; exit 1; }
"$scratch/t"
answers=$?

if [ "$claims_answer" -eq 1 ] && [ "$answers" -ne 0 ]; then
    echo "FAIL: the comment says the factory answers every operation; it returned $answers"
    exit 1
fi
if [ "$claims_answer" -eq 0 ] && [ "$answers" -eq 0 ]; then
    echo "FAIL: the factory answers every operation but the comment no longer says so"
    exit 1
fi
echo "PASS: the comment and the object agree"
